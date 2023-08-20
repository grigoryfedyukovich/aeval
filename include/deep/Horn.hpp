#ifndef HORN__HPP__
#define HORN__HPP__

#include <fstream>
#include "ae/AeValSolver.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  struct HornRuleExt
  {
    ExprVector srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    ExprSet lin;

    ExprVector origSrc;
    ExprVector origDst;
    ExprMap origSrcVars;

    Expr body;

    Expr srcRelation;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;

    void assignVarsAndRewrite (ExprVector& invSrc, ExprVector& invDst)
    {
      for (int i = 0; i < origSrc.size(); i++)
      {
        srcVars.push_back(invSrc[i]);
        lin.insert(mk<EQ>(origSrc[i], srcVars[i]));
      }

      for (int i = 0; i < origDst.size(); i++)
      {
        dstVars.push_back(invDst[i]);
        lin.insert(mk<EQ>(origDst[i], dstVars[i]));
      }
    }

    void shrinkLocVars()
    {
      for (auto it = locVars.begin(); it != locVars.end();)
        if (contains(body, *it)) ++it;
        else it = locVars.erase(it);
    }

    bool splitBody ()
    {
      getConj (simplifyBool(body), lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        if (isOpX<FALSE>(cnj)) return false;
        if (isOpX<FAPP>(cnj) && cnj->arity() > 1 && isOpX<FDECL>(cnj->left()))
        {
          Expr rel = cnj->left();
          if (srcRelation != NULL)
          {
            errs () << "Nonlinear CHC is currently unsupported: ["
                    << srcRelation << " /\\ " << rel->left() << " -> "
                    << dstRelation << "]\n";
            exit(1);
          }
          srcRelation = rel->left();
          for (auto it = cnj->args_begin()+1; it != cnj->args_end(); ++it)
            origSrc.push_back(*it);
          c = lin.erase(c);
        }
        else ++c;
      }
      return true;
    }

  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";
    SMTUtils u;

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    Expr failDecl;
    vector<HornRuleExt> chcs;
    vector<HornRuleExt*> allCHCs;
    vector<HornRuleExt*> wtoCHCs, dwtoCHCs;
    ExprVector wtoDecls;
    ExprSet decls;
    map<Expr, ExprVector> invVars,invVarsPrime;
    map<Expr, vector<int>> outgs;
    bool cycleSearchDone = false;
    ExprVector loopheads;
    map<Expr, vector<vector<int>>> cycles, prefixes;
    vector<vector<int>> acyclic;
    ExprVector seqPoints;
    // vector<vector<int>> prefixes, cycles;  // for cycles
    map<Expr, bool> hasArrays;
    bool hasAnyArrays, hasBV = false;
    bool hasQuery = false;
    int debug;
    set<int> chcsToCheck1, chcsToCheck2, toEraseChcs;
    int glob_ind = 0;
    ExprSet origVrs;

    CHCs(ExprFactory &efac, EZ3 &z3, int d = false) :
      u(efac), m_efac(efac), m_z3(z3), hasAnyArrays(false), debug(d) {};

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->left()))
            if (e->left()->arity() >= 2)
              return true;
      return false;
    }

    Expr getDeclByName (Expr a)
    {
      for (auto & d : decls)
        if (d->left() == a) return d;
      return NULL;
    }

    bool addedDecl (Expr a)
    {
      return getDeclByName(a) != NULL;
    }

    void addDecl (Expr a)
    {
      if (invVars[a->left()].size() == 0)
      {
        decls.insert(a);
        int j = 0;
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr arg = a->arg(i);
          if (!isOpX<INT_TY>(arg) && !isOpX<REAL_TY>(arg) &&
              !isOpX<BOOL_TY>(arg) && !isOpX<ARRAY_TY>(arg) &&
              !isOpX<BVSORT> (arg))
          {
            errs() << "Argument #" << i << " of " << a << " is not supported\n";
            exit(1);
          }
          while (true)
          {
            Expr name = mkTerm<string> (varname + to_string(j), m_efac);
            Expr var = fapp (constDecl (name, arg));
            name = mkTerm<string> (lexical_cast<string>(name) + "'", m_efac);
            Expr varPr = fapp (constDecl (name, arg));
            j++;
            if (find(origVrs.begin(), origVrs.end(), var) != origVrs.end())
              continue;
            if (find(origVrs.begin(), origVrs.end(), varPr) != origVrs.end())
              continue;
            invVars[a->left()].push_back(var);
            invVarsPrime[a->left()].push_back(varPr);
            break;
          }
        }
      }
    }

    bool normalize (Expr& r, HornRuleExt& hr)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 &&
               isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 &&
               isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      // small rewr
      if (isOpX<IMPL>(r) && isOpX<ITE>(r->right()))
      {
        return true;
      }

      if (isOpX<IMPL>(r) && isOpX<IMPL>(r->right()))
      {
        r = mk<IMPL>(mk<AND>(r->left(), r->right()->left()), r->right()->right());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return false;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return true;
    }

    bool parse(string smt, bool doElim = true, bool doArithm = true)
    {
      if (debug > 0) outs () << "\nPARSING" << "\n=======\n";
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      chcs.reserve(fp.m_rules.size());

      ExprMap eqs;
      for (auto it = fp.m_rules.begin(); it != fp.m_rules.end(); )
      {
        if (isOpX<EQ>(*it))
        {
          eqs[(*it)->left()->left()] = (*it)->right()->left();
          it = fp.m_rules.erase(it);
        }
        else ++it;
      }

      for (auto &r: fp.m_rules)
      {
        hasAnyArrays |= containsOp<ARRAY_TY>(r);
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();
        while (true)
        {
          auto r1 = replaceAll(r, eqs);
          if (r == r1) break;
          else r = r1;
        }

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

        filter (r, bind::IsConst(), inserter (origVrs, origVrs.begin()));
        // small rewr:
        if (isOpX<ITE>(r->last()))
        {
          hr.body = mk<IMPL>(mk<AND>(r->left(), r->last()->left()),
                             r->last()->right());
          chcs.push_back(chcs.back());
          chcs.back().body = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->last()->left())),
                             r->last()->last());
        }
        else
        {
          hr.body = r;
        }
      }

      for (auto & hr : chcs)
      {
        Expr head = hr.body->right();
        hr.body = hr.body->left();
        if (isOpX<FAPP>(head))
        {
          if (head->left()->arity() == 2 &&
              (find(fp.m_queries.begin(), fp.m_queries.end(), head) !=
               fp.m_queries.end()))
            addFailDecl(head->left()->left());
          else
            addDecl(head->left());
          hr.dstRelation = head->left()->left();
          for (auto it = head->args_begin()+1; it != head->args_end(); ++it)
            hr.dstVars.push_back(*it); // to be rewritten later
        }
        else
        {
          if (!isOpX<FALSE>(head)) hr.body = mk<AND>(hr.body, mk<NEG>(head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.dstRelation = mk<FALSE>(m_efac);
        }
        hasBV |= containsOp<BVSORT>(hr.body);
      }

      if (debug > 0) outs () << "Reserved space for " << chcs.size()
                          << " CHCs and " << decls.size() << " declarations\n";

      // the second loop is needed because we want to distinguish
      // uninterpreted functions used as variables
      // from relations to be synthesized
      for (auto it = chcs.begin(); it != chcs.end(); )
      {
        // ExprVector origSrcSymbs, origDstSymbs;
        // ExprSet lin;
        HornRuleExt & hr = *it;
        if (!hr.splitBody())
        {
          it = chcs.erase(it);
          continue;
        }
        else ++it;

        if (hr.srcRelation == NULL) hr.srcRelation = mk<TRUE>(m_efac);

        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl);
        if (hr.isQuery) { hasQuery = true; }
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        hr.origDst = hr.dstVars;
        hr.dstVars.clear();

        hr.assignVarsAndRewrite (invVars[hr.srcRelation],
                                 invVarsPrime[hr.dstRelation]);

        if (doElim)
        {
          hr.body = eliminateQuantifiers(conjoin(hr.lin, m_efac), hr.locVars,
                                                 !hasBV && doArithm, false);
          hr.body = u.removeITE(hr.body);
          hr.body = simplifyArr(hr.body);
          hr.shrinkLocVars();
        }
        else
          hr.body = conjoin(hr.lin, m_efac);
      }
      if (doElim)
      {
        int sz = chcs.size();
        for (int c = 0; c < chcs.size(); c++)
        {
          chcsToCheck1.insert(c);
          chcsToCheck2.insert(c);
        }
        if (!eliminateDecls()) return false;

        // eliminating all at once,
        // otherwise elements at chcsToCheck* need updates
        for (auto it = toEraseChcs.rbegin(); it != toEraseChcs.rend(); ++it)
          chcs.erase(chcs.begin() + *it);
        toEraseChcs.clear();

        // get rid of vacuous:
        while (true)
        {
          bool toBreak = true;
          for (auto & d : decls)
          {
            set<int> toEraseChcs;
            bool toCont = false;
            for (int c = 0; c < chcs.size(); c++)
            {
              if (chcs[c].dstRelation == d->left())
              {
                toCont = true;
                break;
              }
              if (chcs[c].srcRelation == d->left())
                toEraseChcs.insert(c);
            }
            if (toCont) continue;
            for (auto it = toEraseChcs.rbegin(); it != toEraseChcs.rend(); ++it)
            {
              toBreak = false;
              chcs.erase(chcs.begin() + *it);
            }
          }
          if (toBreak) break;
        }
      }

      for (int i = 0; i < chcs.size(); i++)
        outgs[chcs[i].srcRelation].push_back(i);

      findCycles();

      // prepare a version of wtoCHCs w/o queries
      dwtoCHCs = wtoCHCs;
      for (auto it = dwtoCHCs.begin(); it != dwtoCHCs.end();)
        if ((*it)->isQuery) it = dwtoCHCs.erase(it);
          else ++it;

      if (debug >= 1)
      {
        outs () << (doElim ? "  Simplified " : "  Parsed ") << "CHCs:\n";
        print(debug >= 4, true);
      }
      return true;
    }

    bool eliminateTrivTrueOrFalse()
    {
      set<int> toEraseChcsTmp;
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
        if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

        auto c = &chcs[i];
        if (c->isQuery && !c->isFact)
        {
          auto f = find(chcsToCheck1.begin(), chcsToCheck1.end(), i);
          if (f != chcsToCheck1.end())
          {
            if (u.isTrue(c->body))
            {
              // thus, c->srcRelation should be false
              for (int j = 0; j < chcs.size(); j++)
              {
                if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end()) continue;
                if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), j) != toEraseChcsTmp.end()) continue;

                HornRuleExt* s = &chcs[j];
                if (s->srcRelation == c->srcRelation)
                {
                  // search for vacuous cases where s == inv -> inv2   and   c == inv /\ true -> false
                  // then, inv can only be false, thus s does not give any constraint
                  toEraseChcsTmp.insert(j);  // could erase here, but ther will be a mess with pointers
                }
                else if (s->dstRelation == c->srcRelation)
                {
                  s->isQuery = true;
                  s->dstRelation = failDecl;
                  s->locVars.insert(s->locVars.end(), s->dstVars.begin(), s->dstVars.end());
                  s->dstVars.clear();
                  chcsToCheck1.insert(j);
                  chcsToCheck2.insert(j);
                }
              }
              decls.erase(c->srcRelation);
            }
            chcsToCheck1.erase(f);
          }
        }
        else if (c->isQuery && c->isFact)
          if (u.isSat(c->body))
          {
            outs () << "Counterexample found (during preprocessing)\n";
            return false;
          }
      }

      if (toEraseChcsTmp.empty()) return true;

      for (auto it = toEraseChcsTmp.rbegin(); it != toEraseChcsTmp.rend(); ++it)
      {
        if (debug >= 2) outs () << "  Eliminating vacuous CHC: " <<
                chcs[*it].srcRelation << " -> " << chcs[*it].dstRelation << "\n";
        if (debug >= 3) outs () << "    its body is true: " << chcs[*it].body << "\n";
        toEraseChcs.insert(*it);
      }

      return eliminateTrivTrueOrFalse();     // recursive call
    }

    bool eliminateDecls()
    {
      pair<int,int> preElim = {chcs.size() - toEraseChcs.size(), decls.size()};
      if (debug > 0)
        outs () << "Reducing the number of CHCs: " << preElim.first <<
              "; and the number of declarations: " << preElim.second << "...\n";
      if (debug >= 3)
      {
        outs () << "  Current CHC topology:\n";
        print(false);
      }

      Expr declToRemove = NULL;
      vector<int> srcMax, dstMax;
      set<int> toEraseChcsTmp;
      for (auto d = decls.begin(); d != decls.end();)
      {
        vector<int> src, dst;
        for (int i = 0; i < chcs.size(); i++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
          if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

          if (chcs[i].srcRelation == (*d)->left()) src.push_back(i);
          if (chcs[i].dstRelation == (*d)->left()) dst.push_back(i);
        }

        if ((src.size() > 0 && dst.size() > 0) &&
            emptyIntersect(src, dst))
        {

          if (declToRemove != NULL)
            if (declToRemove->arity() > (*d)->arity())
              { ++d; continue; }
          if (declToRemove != NULL)
            if (declToRemove->arity() == (*d)->arity() &&
                src.size() * dst.size() > srcMax.size() * dstMax.size())
              { ++d; continue; }

          srcMax = src;
          dstMax = dst;
          declToRemove = *d;
        }

        if (src.size() == 0) // found dangling CHCs
        {
          toEraseChcsTmp.insert(dst.begin(), dst.end());
          d = decls.erase(d);
        }
        else ++d;
      }

      // first, it will remove dangling CHCs since it's cheaper
      if (declToRemove != NULL && toEraseChcsTmp.empty())
      {
        for (int i : srcMax)
          for (int j : dstMax)
            concatenateCHCs(i, j);

        toEraseChcsTmp.insert(srcMax.begin(), srcMax.end());
        toEraseChcsTmp.insert(dstMax.begin(), dstMax.end());
        decls.erase(declToRemove);
      }

      for (auto a = toEraseChcsTmp.rbegin(); a != toEraseChcsTmp.rend(); ++a)
      {
        if (debug >= 2)
          outs () << "  Eliminating CHC: " << chcs[*a].srcRelation
                  << " -> " << chcs[*a].dstRelation << "\n";
        toEraseChcs.insert(*a);
      }

      // get rid of CHCs that don't add any _new_ constraints
      removeTautologies();

      if (preElim.first > (chcs.size() - toEraseChcs.size()) ||
          preElim.second > decls.size())
        return eliminateDecls();
      else
      {
        // remove unrelated constraints and shrink arities of predicates
        // currently disabled
        // if (!hasAnyArrays) slice();

        int preComb = (chcs.size() - toEraseChcs.size());
        combineCHCs();
        if (preComb > (chcs.size() - toEraseChcs.size()))
          return eliminateDecls();
      }
      return true;
    }

    void concatenateCHCs(int i, int j)
    {
      chcs.push_back(HornRuleExt());
      HornRuleExt* s = &chcs[i];
      HornRuleExt* d = &chcs[j];
      HornRuleExt* n = &chcs.back();
      if (debug >= 2)
      {
        outs () << "  Concatenating two CHCs: "
                << d->srcRelation << " -> " << d->dstRelation << " and "
                << s->srcRelation << " -> " << s->dstRelation << "\n";
      }
      n->srcRelation = d->srcRelation;
      n->dstRelation = s->dstRelation;
      n->srcVars = d->srcVars;
      n->dstVars = d->dstVars;

      ExprVector newVars;
      for (int i = 0; i < d->dstVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__bnd_var_" +
          to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->dstVars[i], new_name));
      }
      Expr mergedBody = replaceAll(s->body, s->srcVars, newVars);
      n->dstVars.insert(n->dstVars.end(), d->locVars.begin(), d->locVars.end());
      for (int i = 0; i < d->locVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__loc_var_" +
          to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->locVars[i], new_name));
      }
      mergedBody = mk<AND>(replaceAll(d->body, n->dstVars, newVars), mergedBody);
      n->locVars = newVars;
      n->locVars.insert(n->locVars.end(), s->locVars.begin(), s->locVars.end());
      n->body = simpleQE(mergedBody, n->locVars);
      n->shrinkLocVars();
      n->dstVars = s->dstVars;
      n->isInductive = n->srcRelation == n->dstRelation;
      n->isFact = isOpX<TRUE>(n->srcRelation);
      n->isQuery = n->dstRelation == failDecl;
      chcsToCheck1.insert(chcs.size()-1);
      chcsToCheck2.insert(chcs.size()-1);
    }

    void removeTautologies()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        auto h = &chcs[i];
        auto f = find(chcsToCheck2.begin(), chcsToCheck2.end(), i);
        if (f != chcsToCheck2.end())
        {
          if (u.isFalse(h->body))
          {
            if (debug >= 2)
              outs () << "  Eliminating CHC: " << h->srcRelation
                      << " -> " << h->dstRelation << "\n";
            if (debug >= 3)
              outs () << "    its body is false: " << h->body << "\n";
            toEraseChcs.insert(i);
            continue;
          }
          chcsToCheck2.erase(f);
        }

        bool found = false;
        if (h->isInductive)
        {
          found = true;
          for (int j = 0; j < h->srcVars.size(); j++)
          {
            if (u.isSat(h->body, mkNeg(mk<EQ>(h->srcVars[j], h->dstVars[j]))))
            {
              found = false;
              break;
            }
          }
        }
        if (found)
        {
          if (debug >= 2)
            outs () << "  Eliminating CHC: " << h->srcRelation
                    << " -> " << h->dstRelation << "\n";
          if (debug >= 3)
            outs () << "    inductive but does not change vars: "
                    << h->body << "\n";
          toEraseChcs.insert(i);
        }
        else ++h;
      }
    }

    void combineCHCs()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        set<int> toComb = {i};
        HornRuleExt& s = chcs[i];
        for (int j = i + 1; j < chcs.size(); j++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end())
            continue;

          HornRuleExt& d = chcs[j];
          if (s.srcRelation == d.srcRelation && s.dstRelation == d.dstRelation)
          {
            for (int k = 0; k < s.srcVars.size(); k++)
              assert (s.srcVars[k] == d.srcVars[k]);
            for (int k = 0; k < s.dstVars.size(); k++)
              assert (s.dstVars[k] == d.dstVars[k]);
            toComb.insert(j);
          }
        }
        if (toComb.size() > 1)
        {
          if (debug >= 2)
          {
            outs () << "    Disjoing bodies of " << toComb.size() << " CHCs: "
                    << s.srcRelation << " -> " << s.dstRelation << "\n";
          }
          ExprVector all;
          for (auto it = toComb.rbegin(); it != toComb.rend(); ++it)
          {
            all.push_back(chcs[*it].body);
            if (*it != i) toEraseChcs.insert(*it);
          }
          s.body = distribDisjoin(all, m_efac);
          chcsToCheck1.insert(i);
          chcsToCheck2.insert(i);
          return combineCHCs();
        }
      }
    }

    // (recursive) multi-stage slicing begins here
    set<int> chcsToVisit;
    map<Expr, ExprSet> varsSlice;

    void updateTodo(Expr decl, int num)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        if (i != num &&
            !chcs[i].isQuery &&
            (chcs[i].srcRelation == decl || chcs[i].dstRelation == decl))
              chcsToVisit.insert(i);
      }
    }

    void slice()
    {
      chcsToVisit.clear();
      varsSlice.clear();
      // first, compute sets of dependent variables
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        if (chcs[i].isQuery)
        {
          chcs[i].body = keepQuantifiers(chcs[i].body, chcs[i].srcVars);
          Expr decl = chcs[i].srcRelation;
          filter (chcs[i].body, bind::IsConst(),
            std::inserter (varsSlice[decl], varsSlice[decl].begin ()));
          updateTodo(chcs[i].srcRelation, i);
        }
      }
      while (!chcsToVisit.empty()) slice(*chcsToVisit.begin());

      // now, prepare for variable elimination
      for (auto & d : varsSlice)
      {
//      if (invVars[d.first].size() > d.second.size())
//        outs () << "sliced for " << *d.first << ": " << invVars[d.first].size()
//                << " -> "    << d.second.size() << "\n";
        ExprSet varsPrime;
        for (auto & v : d.second)
        {
          Expr pr = replaceAll(v, invVars[d.first], invVarsPrime[d.first]);
          varsPrime.insert(pr);
        }

        keepOnly(invVars[d.first], d.second);
        keepOnly(invVarsPrime[d.first], varsPrime);
      }

      // finally, update bodies and variable vectors
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;
        auto & c = chcs[i];

        if (u.isFalse(c.body) || u.isTrue(c.body)) continue;

        ExprSet bd;
        getConj(c.body, bd);
        for (auto b = bd.begin(); b != bd.end();)
        {
          if (emptyIntersect(*b, invVars[c.srcRelation]) &&
              emptyIntersect(*b, invVarsPrime[c.dstRelation]))
            b = bd.erase(b);
          else ++b;
        }
        if (!c.isFact) c.srcVars = invVars[c.srcRelation];
        if (!c.isQuery) c.dstVars = invVarsPrime[c.dstRelation];
        c.body = conjoin(bd, m_efac);
      }
    }

    void slice(int num)
    {
      HornRuleExt* hr = &chcs[num];
      assert (!hr->isQuery);
      ExprSet srcCore, dstCore, srcDep, dstDep, varDeps, cnjs;
      auto & dst = hr->dstVars;
      auto & src = hr->srcVars;

      if (qeUnsupported(hr->body))
      {
        varDeps.insert(src.begin(), src.end());
        varDeps.insert(hr->locVars.begin(), hr->locVars.end());
        varDeps.insert(dst.begin(), dst.end());
      }
      else
      {
        // all src vars from the preconditions are dependent
        varDeps = varsSlice[hr->srcRelation];
        filter (getPrecondition(hr), bind::IsConst(),
                      std::inserter (varDeps, varDeps.begin ()));

        for (auto & v : varsSlice[hr->dstRelation])
          varDeps.insert(replaceAll(v, invVars[hr->dstRelation], dst));

        srcCore = varsSlice[hr->dstRelation];
        dstCore = varDeps;

        getConj(hr->body, cnjs);
        while(true)
        {
          int vars_sz = varDeps.size();
          for (auto & c : cnjs)
          {
            ExprSet varsCnj;
            filter (c, bind::IsConst(),
                          std::inserter (varsCnj, varsCnj.begin ()));
            if (!emptyIntersect(varDeps, varsCnj))
              varDeps.insert(varsCnj.begin(), varsCnj.end());
          }
          if (hr->isInductive)
          {
            for (auto & v : varDeps)
            {
              varDeps.insert(replaceAll(v, dst, src));
              varDeps.insert(replaceAll(v, src, dst));
            }
          }
          if (vars_sz == varDeps.size()) break;
        }
      }

      bool updateSrc = false;
      bool updateDst = false;
      if (!hr->isFact)
      {
        ExprSet& srcVars = varsSlice[hr->srcRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(src.begin(), src.end(), *v) != src.end())
          {
            if (find(srcVars.begin(), srcVars.end(), *v) == srcVars.end())
            {
              updateSrc = true;
              srcVars.insert(*v);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      srcDep = varsSlice[hr->srcRelation];
      dstDep = varDeps;

      if (!hr->isQuery)
      {
        ExprSet& dstVars = varsSlice[hr->dstRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(dst.begin(), dst.end(), *v) != dst.end())
          {
            Expr vp = replaceAll(*v, dst, invVars[hr->dstRelation]);
            if (find(dstVars.begin(), dstVars.end(), vp) == dstVars.end())
            {
              updateDst = true;
              dstVars.insert(vp);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      if (!varDeps.empty())
        hr->body = eliminateQuantifiers(hr->body, varDeps, false);

      if (updateSrc) updateTodo(hr->srcRelation, num);
      if (updateDst) updateTodo(hr->dstRelation, num);
      chcsToVisit.erase(num);
    }

    vector<int> getPrefix(Expr rel) // get only first one; to extend
    {
      assert(!cycles[rel].empty());
      assert(!prefixes[rel].empty());
      vector<int> pref = prefixes[rel][0];
      assert(!pref.empty());
      if (chcs[pref[0]].isFact)
        return pref;
      vector<int> ppref = getPrefix(chcs[pref[0]].srcRelation);
      ppref.insert(ppref.end(), pref.begin(), pref.end());
      return ppref;
    }

    bool hasCycles()
    {
      if (chcs.size() == 0) return false;
      if (cycleSearchDone) return cycles.size() > 0;
      findCycles();
      return (cycles.size() > 0);
    }

    void getAllTraces (Expr src, Expr dst, int len, vector<int> trace,
                vector<vector<int>>& traces, bool once = false)
    {
      if (len == 1)
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst)
          {
            if (once && find(trace.begin(), trace.end(), a) != trace.end())
              continue;
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : outgs[src])
        {
          if (once && find(trace.begin(), trace.end(), a) != trace.end())
            continue;
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(chcs[a].dstRelation, dst, len-1, newtrace, traces, once);
        }
      }
    }

    bool isRelVisited(vector<int>& trace, ExprVector& av, Expr rel)
    {
      for (auto t : trace)
        if (chcs[t].dstRelation == rel)
          return true;
      return find(av.begin(), av.end(), rel) != av.end();
    }

    void getAllAcyclicTraces (Expr src, Expr dst, int len, vector<int> trace,
                  vector<vector<int>>& traces, ExprVector& av)
    {
      if (len == 1)
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst ||
              isRelVisited(trace, av, chcs[a].dstRelation))
            continue;
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllAcyclicTraces(chcs[a].dstRelation, dst, len-1, newtrace, traces, av);
        }
      }
    }

    void findCycles()
    {
      ExprVector endRels;
      outgs.clear(); acyclic.clear(); cycles.clear(); allCHCs.clear();
      prefixes.clear(); seqPoints.clear(); wtoCHCs.clear();
      for (int i = 0; i < chcs.size(); i++)
      {
        outgs[chcs[i].srcRelation].push_back(i);
        if (chcs[i].isQuery) unique_push_back(chcs[i].dstRelation, endRels);
      }

      ExprVector av;
      for (auto & d : decls)
        if (outgs[d->left()].empty())
          endRels.push_back(d->left());

      for (auto & r : endRels) {
        findCycles(mk<TRUE>(m_efac), r, av);
      }

      assert(wtoCHCs.size() == chcs.size());

      // filter wtoDecls
      for (auto it = wtoDecls.begin(); it != wtoDecls.end();)
      {
        if (*it == failDecl || isOpX<TRUE>(*it)) it = wtoDecls.erase(it);
        else ++it;
      }

      if (debug > 0)
      {
        for (auto & a : cycles)
          outs () << "  traces num for: " << a.first << ": " << a.second.size() << "\n";
      }
      for (auto & a : acyclic)
      {
        if (seqPoints.empty())
          for (auto & i : a) seqPoints.push_back(chcs[i].dstRelation);
        else
          for (auto it = seqPoints.begin(); it != seqPoints.end(); )
          {
            bool f = false;
            for (auto & i : a)
              if (*it == chcs[i].dstRelation)
                { f = true; break;}
            if (f) ++it;
            else it = seqPoints.erase(it);
          }
        if (seqPoints.empty()) break;
      }
      cycleSearchDone = true;
    }

    bool findCycles(Expr src, Expr dst, ExprVector& avoid)
    {
      if (debug >= 2) outs () << "\nfindCycles:  " << src << " => " << dst << "\n";
      vector<vector<int>> nonCycleTraces;
      ExprVector highLevelRels;
      for (int i = 1; i <= chcs.size(); i++)
      {
        if (debug >= 2)
        {
          outs () << ".";
          outs().flush();
        }
        getAllAcyclicTraces(src, dst, i, vector<int>(), nonCycleTraces, avoid);
      }

      bool tracesFound = nonCycleTraces.size() > 0;
      map <Expr, vector<vector<int>>> prefs;
      for (auto & d : nonCycleTraces)
      {
        vector<int> tmp;
        for (auto & chcNum : d)
        {
          if (chcs[chcNum].isQuery) break;      // last iter anyway
          Expr& r = chcs[chcNum].dstRelation;
          tmp.push_back(chcNum);
          if (find(avoid.begin(), avoid.end(), r) == avoid.end())
          {
            prefs[r].push_back(tmp);
            unique_push_back(r, highLevelRels);
          }
        }
      }

      if (tracesFound)
        if (src == dst)
          for (auto & c : nonCycleTraces) unique_push_back(c, cycles[src]);
        else
          for (auto & c : nonCycleTraces) unique_push_back(c, acyclic);
      else
        assert(src == dst);

      ExprVector avoid2 = avoid;
      for (auto & d : highLevelRels)
      {
        avoid2.push_back(d);
        bool nestedCycle = findCycles(d, d, avoid2);
        if (nestedCycle)
        {
          prefixes[d] = prefs[d]; // to debug
        }
      }

      // WTO sorting is here now:
      if (tracesFound)
      {
        if (src == dst)
        {
          unique_push_back(src, loopheads);      // could there be duplicates?
          if (debug > 0) outs () << "  loophead found: " << src << "\n";
        }
        else if (debug > 0) outs () << "  global:\n";
      }

      for (auto c : nonCycleTraces)
      {
        if (debug > 5)
        {
          outs () << "    trace: " << chcs[c[0]].srcRelation;
          for (auto h : c)
            outs () << " -> " << chcs[h].dstRelation << " ";
          outs () << "\n";
        }

        unique_push_back(chcs[c[0]].srcRelation, wtoDecls);
        for (auto h : c) {
          unique_push_back(chcs[h].dstRelation, wtoDecls);
          unique_push_back(&chcs[h], wtoCHCs);
        }
      }

      return tracesFound;
    }

    vector<int> empt;
    vector<int>& getCycleForRel(Expr rel)
    {
      for (auto & c : cycles[loopheads[0]]) // GF: loopheads[0]]?
        if (chcs[c[0]].srcRelation == rel)
          return c;
      return empt;
    }

    vector<int>& getCycleForRel(int chcNum)
    {
      return getCycleForRel(chcs[chcNum].srcRelation);
    }

    void addRule (HornRuleExt* r)
    {
      chcs.push_back(*r);
      Expr srcRel = r->srcRelation;
      if (!isOpX<TRUE>(srcRel))
      {
        if (invVars[srcRel].size() == 0)
        {
          addDeclAndVars(srcRel, r->srcVars);
        }
      }
      outgs[srcRel].push_back(chcs.size()-1);
    }

    void addDeclAndVars(Expr rel, ExprVector& args)
    {
      ExprVector types;
      for (auto &var: args) {
        types.push_back(bind::typeOf(var));
      }
      types.push_back(mk<BOOL_TY>(m_efac));

      decls.insert(bind::fdecl (rel, types));
      for (auto & v : args)
      {
        invVars[rel].push_back(v);
      }
    }

    void addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          errs () << "Multiple queries are unsupported\n";
          exit (1);
        }
      }
    }

    Expr getPrecondition (HornRuleExt* hr)
    {
      Expr tmp = keepQuantifiers(hr->body, hr->srcVars);
      return weakenForHardVars(tmp, hr->srcVars);
    }

    // Transformations

    void copyIterations(Expr decl, int num)
    {
      HornRuleExt* hr;
      for (auto &a : chcs)
        if (a.srcRelation == decl->left() && a.dstRelation == decl->left())
          hr = &a;
      Expr pre = getPrecondition(hr);
      ExprSet newCnjs;
      newCnjs.insert(mk<NEG>(pre));
      for (int i = 0; i < hr->srcVars.size(); i++)
        newCnjs.insert(mk<EQ>(hr->dstVars[i], hr->srcVars[i]));
      Expr body2 = conjoin(newCnjs, m_efac);

      // adaping the code from BndExpl.hpp
      ExprVector ssa, bindVars1, bindVars2,newLocals;
      int bindVar_index = 0, locVar_index = 0;

      for (int c = 0; c < num; c++)
      {
        Expr body = hr->body;
        bindVars2.clear();
        if (c != 0)
        {
          body = replaceAll(mk<OR>(body, body2), hr->srcVars, bindVars1);
          for (int i = 0; i < hr->locVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__loc_var_" +
              to_string(locVar_index++), m_efac);
            Expr var = cloneVar(hr->locVars[i], new_name);
            body = replaceAll(body, hr->locVars[i], var);
            newLocals.push_back(var);
          }
        }

        if (c != num-1)
        {
          for (int i = 0; i < hr->dstVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" +
              to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr->dstVars[i], new_name));
            body = replaceAll(body, hr->dstVars[i], bindVars2[i]);
            newLocals.push_back(bindVars2[i]);
          }
        }
        ssa.push_back(body);
        bindVars1 = bindVars2;
      }
      hr->body = conjoin(ssa, m_efac);
      hr->locVars.insert(hr->locVars.end(), newLocals.begin(), newLocals.end());
    }

    void print (bool full = false, bool dump_cfg = false)
    {
      std::ofstream enc_chc;
      if (dump_cfg)
      {
        enc_chc.open("chc.dot");
        enc_chc <<("digraph print {\n");
      }
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;
        auto & hr = chcs[i];
        if (full)
        {
          if (hr.isFact) outs() << "  INIT:\n";
          else if (hr.isInductive) outs() << "  TR:\n";
          else if (hr.isQuery) outs() << "  BAD:\n";
          else outs() << "  CHC:\n";
        }

        outs () << "    " << * hr.srcRelation;
        if (full && hr.srcVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.srcVars);
          outs () << ")";
        }
        else outs () << "[#" << hr.srcVars.size() << "]";
        outs () << " -> " << * hr.dstRelation;

        if (full && hr.dstVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.dstVars);
          outs () << ")";
        }
        else outs () << "[#" << hr.dstVars.size() << "]";
        if (full)
        {
          outs() << "\n    body: \n";
          if (treeSize(hr.body) < 1000)
            pprint(hr.body, 4);
          else outs () << " < . . . . too large . . . . >\n";
        }
        else outs() << "\n";
        if (dump_cfg)
        {
          enc_chc << ' ' << hr.srcRelation;
          enc_chc << " -> ";
          enc_chc << ' ' << hr.dstRelation;
          enc_chc << '\n';
        }
      }
      if (dump_cfg)
      {
        enc_chc <<("}");
        enc_chc.close();
        // this needs a graphiz package installed:
        // system("dot -Tpdf -o chc.pdf chc.dot");
      }
    }

    void serialize ()
    {
      std::ofstream enc_chc;
      enc_chc.open("chc.smt2");
      enc_chc << "(set-logic HORN)\n";
      for (auto & d : decls)
      {
        enc_chc << "(declare-fun " << d->left() << " (";
        for (int i = 1; i < d->arity()-1; i++)
        {
          u.print(d->arg(i), enc_chc);
          if (i < d->arity()-2) enc_chc << " ";
        }
        enc_chc << ") Bool)\n";
      }
      enc_chc << "\n";
      for (auto & c : chcs)
      {
        Expr src, dst;
        if (c.isFact)
        {
          src = mk<TRUE>(m_efac);
        }
        else
        {
          for (auto & d : decls)
          {
            if (d->left() == c.srcRelation)
            {
              src = fapp(d, c.srcVars);
              break;
            }
          }
        }
        if (c.isQuery)
        {
          dst = mk<FALSE>(m_efac);
        }
        else
        {
          for (auto & d : decls)
          {
            if (d->left() == c.dstRelation)
            {
              dst = fapp(d, c.dstVars);
              break;
            }
          }
        }

        enc_chc << "(assert ";
        u.print(mkQFla(mk<IMPL>(mk<AND>(src, c.body), dst), true), enc_chc);
        enc_chc << ")\n\n";
      }
      enc_chc << "(check-sat)\n";
    }
  };
}


#endif
