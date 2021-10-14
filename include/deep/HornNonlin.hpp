#ifndef HORNNONLIN__HPP__
#define HORNNONLIN__HPP__

#include "ae/AeValSolver.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  // all adapted from the modver branch
  inline bool rewriteHelperConsts(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  struct HornRuleExt
  {
    vector<ExprVector> srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;

    ExprVector srcRelations;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;

    void assignVarsAndRewrite (vector<ExprVector>& _srcVars, vector<ExprVector>& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst)
    {
      for (int i = 0; i < _srcVars.size(); i++)
      {
        ExprVector tmp;
        for (int j = 0; j < _srcVars[i].size(); j++)
        {
          tmp.push_back(invVarsSrc[i][j]);
          body = mk<AND>(body, mk<EQ>(_srcVars[i][j], tmp[j]));
        }
        srcVars.push_back(tmp);
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        // primed copy of var:
        Expr new_name = mkTerm<string> (lexical_cast<string>(invVarsDst[i]) + "'", body->getFactory());
        Expr var = cloneVar(invVarsDst[i], new_name);
        dstVars.push_back(var);
        body = mk<AND>(body, mk<EQ>(_dstVars[i], dstVars[i]));
      }
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    ExprSet decls;
    Expr failDecl;
    ExprVector extras;
    vector<HornRuleExt> chcs;
    map<Expr, ExprVector> invVars;
    map<Expr, vector<int>> incms;
    int qCHCNum;  // index of the query in chc
    int total_var_cnt = 0;
    ExprVector constructors;

    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3) {};

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->arg(0)))
            if (e->arg(0)->arity() >= 2)
              return true;
      return false;
    }

    void splitBody (Expr body, vector<ExprVector>& srcVars, ExprVector &srcRelations, ExprSet& lin)
    {
      getConj (body, lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        if (isOpX<FAPP>(cnj) && isOpX<FDECL>(cnj->left()))
        {
          Expr rel = cnj->arg(0);
          addDecl(rel);
          srcRelations.push_back(rel);
          ExprVector tmp;
          for (auto it = cnj->args_begin()+1, end = cnj->args_end(); it != end; ++it)
            tmp.push_back(*it);
          srcVars.push_back(tmp);
          c = lin.erase(c);
        }
        else ++c;
      }
    }

    void addDecl (Expr a)
    {
      if (invVars[a].size() == 0)
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          total_var_cnt++;
          Expr var;
          if (isOpX<INT_TY> (a->arg(i)))
            var = bind::intConst(new_name);
          else if (isOpX<REAL_TY> (a->arg(i)))
            var = bind::realConst(new_name);
          else if (isOpX<BOOL_TY> (a->arg(i)))
            var = bind::boolConst(new_name);
          else if (isOpX<ARRAY_TY> (a->arg(i)))
            var = bind::mkConst(new_name, mk<ARRAY_TY>(a->arg(i)->left(), a->arg(i)->right()));
          else if (isOpX<AD_TY>(a->arg(i))){
            ExprVector type;
            type.push_back(a->arg(i));
            var = bind::fapp(bind::fdecl (new_name, type));
          }
          else
            assert(0);
          invVars[a].push_back(var);
        }
      }
    }

    Expr normalize (Expr& r1, HornRuleExt& hr)
    {
      r1 = regularizeQF(r1);
      Expr r = r1;

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
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return NULL;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mk<NEG>(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return r;
    }

    void parse(char *smt_file)
    {
      // GF: this entry part is different from the original implementation
      // (since the fixpoint format does not support ADTs)
      Expr e = z3_from_smtlib_file (m_z3, smt_file);
      for (auto & a : m_z3.getAdtConstructors()) {
        constructors.push_back(regularizeQF(a));
      }
      ExprSet cnjs;
      getConj(e, cnjs);
      unitPropagation(cnjs);

      for (auto r1: cnjs)
      {
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();
        Expr r = normalize(r1, hr);
        if (r == NULL)
        {
          chcs.pop_back();
          continue;
        }

        Expr body = r->arg(0);
        Expr head = r->arg(1);
        vector<ExprVector> origSrcSymbs;
        ExprSet lin;
        splitBody(body, origSrcSymbs, hr.srcRelations, lin);
        if (hr.srcRelations.size() == 0)
        {
          if (hasUninterp(body))
          {
//            errs () << "Unsupported format\n";
//            errs () << "   " << *body << "\n";
//            exit (1);
            lin.clear();
          }
        }

        hr.isFact = hr.srcRelations.empty();

        if (isOpX<FAPP>(head))
        {
          addDecl(head->arg(0));
          hr.dstRelation = head->arg(0);
        }
        else
        {
          if (!isOpX<FALSE>(head)) body = mk<AND>(body, mk<NEG>(head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.dstRelation = mk<FALSE>(m_efac);
        }

        hr.isQuery = (hr.dstRelation == failDecl);
        hr.isInductive = (hr.srcRelations.size() == 1 && hr.srcRelations[0] == hr.dstRelation);
        if (hr.isQuery) qCHCNum = chcs.size() - 1;

        ExprVector allOrigSymbs;
        for (auto & a : origSrcSymbs) for (auto & b : a) allOrigSymbs.push_back(b);
        ExprVector origDstSymbs;
        if (!hr.isQuery)
        {
          for (auto it = head->args_begin()+1, end = head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
        }
        allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());
        //simplBoolReplCnj(allOrigSymbs, lin); // perhaps, not a very important optimization now; consider removing
        hr.body = conjoin(lin, m_efac);

        vector<ExprVector> tmp;
        // we may have several applications of the same predicate symbol in the body:
        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          auto & a = hr.srcRelations[i];
          ExprVector tmp1;
          for (int j = 0; j < i; j++)
          {
            if (hr.srcRelations[i] == hr.srcRelations[j])
            {
              for (int k = 0; k < invVars[a].size(); k++)
              {
                Expr new_name = mkTerm<string> (varname + to_string(++total_var_cnt), m_efac);
                tmp1.push_back(cloneVar(invVars[a][k], new_name));
              }
              break;
            }
          }
          if (tmp1.empty())
          {
            tmp1 = invVars[a];
          }
          tmp.push_back(tmp1);
        }
        hr.assignVarsAndRewrite (origSrcSymbs, tmp,
                                 origDstSymbs, invVars[hr.dstRelation]);

        if ((isOpX<TRUE>(hr.body) && !hr.isQuery) ||
            (hr.srcRelations.size() == 0 && hr.isQuery))
        {
          extras.push_back(r1);
          chcs.pop_back();
          continue;
        }

        // Should keep non-adt variables using in adt constructors
        ExprSet cnjsSet;
        getConj(hr.body, cnjsSet);
        for (auto cnj : cnjsSet) {
          if (isOpX<EQ>(cnj)) {
            Expr l = bind::fname(cnj->left());
            Expr r = bind::fname(cnj->right());
            if (std::find(constructors.begin(), constructors.end(), l) != constructors.end()) {
              for (int i = 0; i < cnj->left()->arity(); ++i) {
                Expr var = cnj->left()->arg(i);
                if (!isAdtConst(var)) {
                  hr.locVars.erase(std::remove(hr.locVars.begin(), hr.locVars.end(), var), hr.locVars.end());
                }
              }
            }
            if (std::find(constructors.begin(), constructors.end(), r) != constructors.end()) {
              for (int i = 0; i < cnj->right()->arity(); ++i) {
                Expr var = cnj->right()->arg(i);
                if (!isAdtConst(var)) {
                  hr.locVars.erase(std::remove(hr.locVars.begin(), hr.locVars.end(), var), hr.locVars.end());
                }
              }
            }
          }
        }
        
        hr.body = simpleQE(hr.body, hr.locVars);
        ExprVector body_vars;
        expr::filter (hr.body, bind::IsConst(), std::inserter (body_vars, body_vars.begin ()));
        for (auto it = hr.locVars.begin(); it != hr.locVars.end(); )
        {
          if (find(body_vars.begin(), body_vars.end(), *it) == body_vars.end())
            it = hr.locVars.erase(it);
          else ++it;
        }
      }

      for (int i = 0; i < chcs.size(); i++)
        incms[chcs[i].dstRelation].push_back(i);

    }

    void unitPropagation(ExprSet &cnjs) {
      ExprMap matching;
      for  (auto &r: cnjs) {
        if (isOpX<NEG>(r) && r->arity() == 1 && !isOpX<FALSE>(r->left())) {
          matching[r->left()] = mk<FALSE>(m_efac);
        }
      }
      if (matching.empty()) {
        return;
      }
      else {
        ExprSet newCnjs;
        for  (auto &r: cnjs) {
          Expr r1 = replaceAll(r, matching);
          newCnjs.insert(r1);
        }
        cnjs = newCnjs;
        unitPropagation(cnjs);
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
          errs () << "Multiple queries are not supported\n";
          exit(1);
        }
      }
    }

    Expr getPostcondition (int i)
    {
      HornRuleExt& hr = chcs[i];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr.body, cnjs);
      ExprVector allVars = hr.locVars;
      for (auto & a : hr.srcVars) allVars.insert(allVars.end(), a.begin(), a.end());
      for (auto & a : cnjs)
      {
        if (emptyIntersect(a, allVars)) newCnjs.insert(a);
      }
      return conjoin(newCnjs, m_efac);
    }

    void print()
    {
      for (auto &hr: chcs) print(hr);
    }

    void print(HornRuleExt& hr)
    {
      if (hr.isFact) outs() << "  INIT CHC:\n";
      else if (hr.isQuery) outs() << "  QUERY CHC:\n";
      else outs() << "  CHC:\n";

      outs () << "    ";

      for (int i = 0; i < hr.srcRelations.size(); i++)
      {
        outs () << * hr.srcRelations[i]->left();
        outs () << " (";
        for(auto &a: hr.srcVars[i]) outs() << *a << ", ";
          outs () << "\b\b)";
        outs () << " /\\ ";
      }

      if (hr.isFact)
        outs () << "true";
      else
        outs () << "\b\b\b\b";

      if (hr.isQuery)
        outs () << " -> false";
      else
        outs () << " -> " << * hr.dstRelation->left();

      if (hr.dstVars.size() > 0)
      {
        outs () << " (";
        for(auto &a: hr.dstVars) outs() << *a << ", ";
        outs () << "\b\b)";
      }
      outs() << "\n    body: " << * hr.body << "\n";
    }
  };
}
#endif
