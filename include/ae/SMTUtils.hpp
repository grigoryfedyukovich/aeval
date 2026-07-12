#ifndef SMTUTILS__HPP__
#define SMTUTILS__HPP__
#include <assert.h>

#include "ae/ExprSimpl.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{

  class SMTUtils {
  private:

    ExprFactory &efac;
    EZ3 z3;
    vector<ZSolver<EZ3>> smt;
    vector<ExprVector> pushed;
    bool can_get_model;
    ZSolver<EZ3>::Model* m;
    int slv = -1;
    unsigned timeout = 0;

    void resetSolver()
    {
      slv = smt.size();
      if (timeout == 0)
        smt.push_back(ZSolver<EZ3>(z3));
      else
        smt.push_back(ZSolver<EZ3>(z3, timeout));
      pushed.push_back({});
      smt[slv].reset();
    }

  public:

    SMTUtils (ExprFactory& _efac) :
      efac(_efac), z3(efac), can_get_model(0), m(NULL) {}

    SMTUtils (ExprFactory& _efac, unsigned _to) :
      efac(_efac), z3(efac), can_get_model(0), m(NULL), timeout(_to) {}

    boost::tribool eval(Expr v, ZSolver<EZ3>::Model* m1)
    {
      Expr ev = m1->eval(v);
      if (m == NULL) return indeterminate;
      if (isOpX<TRUE>(ev)) return true;
      if (isOpX<FALSE>(ev)) return false;
      return indeterminate;
    }

    boost::tribool eval(Expr v)
    {
      getModelPtr();
      if (m == NULL) return indeterminate;
      return eval(v, m);
    }

    ZSolver<EZ3>::Model* getModelPtr()
    {
      if (!can_get_model) return NULL;
      if (slv < 0) return NULL;
      if (m == NULL) m = smt[slv].getModelPtr();
      return m;
    }

    Expr getModel(Expr v)
    {
      getModelPtr();
      if (m == NULL) return NULL;
      return m->eval(v);
    }

    template <typename T> Expr getModel(T& vars)
    {
      getModelPtr();
      if (m == NULL) return NULL;
      ExprVector eqs;
      for (auto & v : vars)
      {
        Expr e = m->eval(v);
        if (e == NULL || containsOp<EXISTS>(e) || containsOp<FORALL>(e))
        {
          continue;
        }
        else if (e != v)
        {
          eqs.push_back(mk<EQ>(v, e));
        }
      }
      return conjoin (eqs, efac);
    }

    ExprSet allVars;
    Expr getModel()
    {
      if (!can_get_model)
        return NULL;
      allVars.clear();
      for (auto & c : pushed[slv])
        filter (c, bind::IsConst (), inserter (allVars, allVars.begin()));
      return getModel(allVars);
    }

    void getModel (ExprSet& vars, ExprMap& e)
    {
      ExprSet mdl;
      getConj(getModel(vars), mdl);
      for (auto & m : mdl) e[m->left()] = m->right();
    }

    template <typename T> void getOptModel (ExprSet& vars, ExprMap& e, Expr v)
    {
      if (!can_get_model) return;
      while (true)
      {
        getModel(vars, e);
        smt[slv].assertExpr(mk<T>(v, e[v]));
        if (m != NULL) { free(m); m = NULL; }
        auto res = smt[slv].solve();
        if (!res || indeterminate(res)) return;
      }
    }

    template <typename T> boost::tribool isSat(T& cnjs, bool reset=true)
    {
      allVars.clear();
      if (m != NULL) { free(m); m = NULL; }
      if (reset || slv < 0)
      {
        resetSolver();
      }
      for (auto & c : cnjs)
      {
        filter (c, bind::IsConst (), inserter (allVars, allVars.begin()));
        smt[slv].push();
        smt[slv].assertExpr(c);
        pushed[slv].push_back(c);
      }
      boost::tribool res = smt[slv].solve ();
      can_get_model = res ? true : false;
      return res;
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, Expr b, Expr c, Expr d, bool reset=true)
    {
      ExprSet cnjs;
      getConj(a, cnjs);
      getConj(b, cnjs);
      getConj(c, cnjs);
      getConj(d, cnjs);
      return isSat(cnjs, reset);
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, Expr b, Expr c, bool reset=true)
    {
      ExprSet cnjs;
      getConj(a, cnjs);
      getConj(b, cnjs);
      getConj(c, cnjs);
      return isSat(cnjs, reset);
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, Expr b, bool reset=true)
    {
      ExprSet cnjs;
      getConj(a, cnjs);
      getConj(b, cnjs);
      return isSat(cnjs, reset);
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, bool reset=true)
    {
      ExprSet cnjs = {a};
      return isSat(cnjs, reset);
    }

    /**
     * Incremental SMT-check
     */
    boost::tribool isSatIncrem(ExprVector& v, int& sz)
    {
      int csz = 0;
      int cslv = 0;
      for (int i = 0; i < pushed.size(); i++)
      {
        int j = 0;
        while (j < v.size() && j < pushed[i].size())
        {
          if (v[j] != pushed[i][j]) break;
          j++;
        }
        if (j > csz)
        {
          csz = j;
          cslv = i;
        }
      }
      if (csz > v.size() / 3)
      {
        sz = csz;
        slv = cslv;
        int psz = pushed[slv].size();
        if (psz > sz)
        {
          smt[slv].pop(psz - sz);
          pushed[slv].resize(sz);
        }
        if (sz == v.size())
        {
          m = NULL;
          boost::tribool res = smt[slv].solve();
          can_get_model = res ? true : false;
          return res;
        }
      }
      else sz = 0;

      while (sz < v.size())
      {
        auto res = isSat(v[sz], sz == 0);
        sz++;
        if (res == false || indeterminate(res)) return res;
      }
      return true;    // sat
    }

    /**
     * SMT-based formula equivalence check
     */
    boost::tribool isEquiv(Expr a, Expr b)
    {
      auto r1 = implies (a, b);
      auto r2 = implies (b, a);
      return r1 && r2;
    }

    /**
     * SMT-based implication check
     */
    boost::tribool implies (Expr a, Expr b)
    {
      if (a == b) return true;
      if (isOpX<TRUE>(b)) return true;
      if (isOpX<FALSE>(a)) return true;
      return ! isSat(a, mkNeg(b));
    }

    /**
     * SMT-based check for a tautology
     */
    boost::tribool isTrue(Expr a){
      if (isOpX<TRUE>(a)) return true;
      return !isSat(mkNeg(a));
    }

    /**
     * SMT-based check for false
     */
    boost::tribool isFalse(Expr a){
      if (isOpX<FALSE>(a)) return true;
      if (isOpX<NEQ>(a) && a->left() == a->right()) return true;
      return !isSat(a);
    }

    void pop(int sz = 1)
    {
      if (m != NULL) { free(m); m = NULL; }
      if (slv >= 0 && sz > 0)
      {
        smt[slv].pop(sz);
        pushed[slv].resize(pushed[slv].size() - sz);
      }
      can_get_model = false;
    }

    boost::tribool reSolve(int sz = 0)
    {
      if (m != NULL) { free(m); m = NULL; }
      if (sz > 0) pop(sz);
      boost::tribool res = smt[slv].solve();
      can_get_model = res ? true : false;
      return res;
    }

    /**
     * Check if v has only one sat assignment in phi
     */
    boost::tribool hasOneModel(Expr v, Expr phi) {
      if (isFalse(phi)) return false;

      getModelPtr();
      if (m == NULL) return indeterminate;

      Expr val = m->eval(v);
      if (v == val) return false;

      ExprSet assumptions;
      assumptions.insert(mk<NEQ>(v, val));

      return !isSat(assumptions, false);
    }

    /**
     * Check if phi has one model
     */
    boost::tribool hasOneModel(Expr phi) {
      if (isFalse(phi)) return false;

      getModelPtr();
      if (m == NULL) return indeterminate;

      ExprSet assumptions;
      assumptions.insert(mk<NEG>(getModel()));

      return !isSat(assumptions, false);
    }

    /**
     * ITE-simplifier (prt 2)
     */
    Expr simplifyITE(Expr ex, Expr upLevelCond)
    {
      if (isOpX<ITE>(ex)){

        Expr cond = ex->arg(0);
        Expr br1 = ex->arg(1);
        Expr br2 = ex->arg(2);

        if (!isSat(cond, upLevelCond)) return br2;

        if (!isSat(mk<NEG>(cond), upLevelCond)) return br1;

        return mk<ITE>(cond,
                       simplifyITE(br1, mk<AND>(upLevelCond, cond)),
                       simplifyITE(br2, mk<AND>(upLevelCond, mk<NEG>(cond))));
      } else {
        return ex;
      }
    }

    /**
     * ITE-simplifier (prt 1)
     */
    Expr simplifyITE(Expr ex)
    {
      if (isOpX<ITE>(ex)){

        Expr cond = simplifyITE(ex->arg(0));
        Expr br1 = ex->arg(1);
        Expr br2 = ex->arg(2);

        if (isOpX<TRUE>(cond)) return br1;
        if (isOpX<FALSE>(cond)) return br2;

        if (br1 == br2) return br1;

        if (isOpX<TRUE>(br1) && isOpX<FALSE>(br2)) return cond;

        if (isOpX<FALSE>(br1) && isOpX<TRUE>(br2)) return mk<NEG>(cond);

        return mk<ITE>(cond,
                       simplifyITE(br1, cond),
                       simplifyITE(br2, mk<NEG>(cond)));

      } else if (isOpX<IMPL>(ex)) {

        return mk<IMPL>(simplifyITE(ex->left()), simplifyITE(ex->right()));
      } else if (isOpX<AND>(ex) || isOpX<OR>(ex)){

        ExprSet args;
        for (auto it = ex->args_begin(), end = ex->args_end(); it != end; ++it){
          args.insert(simplifyITE(*it));
        }
        return isOpX<AND>(ex) ? conjoin(args, efac) : disjoin (args, efac);
      }
      return ex;
    }

    Expr removeITE(Expr ex)
    {
      ExprVector ites;
      getITEs(ex, ites);
      int sz = ites.size();
      for (auto it = ites.begin(); it != ites.end();)
      {
        Expr tmp;
        if (implies(ex, (*it)->left()))
          tmp = (*it)->right();
        else if (implies(ex, mk<NEG>((*it)->left())))
          tmp = (*it)->last();
        else {++it; continue; }

        ex = replaceAll(ex, *it, tmp);
        it = ites.erase(it);
      }
      if (sz == ites.size()) return ex;
      else return simplifyBool(simplifyArithm(removeITE(ex)));
    }

    /**
     * Remove some redundant conjuncts from the set of formulas
     */
    void removeRedundantConjuncts(ExprSet& conjs)
    {
      if (conjs.size() < 2) return;
      ExprSet newCnjs = conjs;

      for (auto & cnj : conjs)
      {
        if (isTrue (cnj))
        {
          newCnjs.erase(cnj);
          continue;
        }

        ExprSet newCnjsTry = newCnjs;
        newCnjsTry.erase(cnj);

        Expr newConj = conjoin(newCnjsTry, efac);
        if (implies (newConj, cnj))
          newCnjs.erase(cnj);

        else {
          // workaround for arrays or complicated expressions
          Expr new_name = mkTerm<string> ("subst", cnj->getFactory());
          Expr new_conj = bind::boolConst(new_name);
          Expr tmp = replaceAll(newConj, cnj, new_conj);
          if (implies (tmp, new_conj)) {
            errs() << "erased\n";
            newCnjs.erase(cnj);
          }
        }
      }
      conjs.clear();
      for (auto & cnj : newCnjs)
        conjs.insert(removeRedundantDisjuncts(cnj));
    }

    /**
     * Remove some redundant conjuncts from the formula
     */
    Expr removeRedundantConjuncts(Expr exp)
    {
      ExprSet conjs;
      getConj(exp, conjs);
      if (conjs.size() < 2) return exp;
      else
      {
        removeRedundantConjuncts(conjs);
        return conjoin(conjs, efac);
      }
    }

    void removeRedundantConjunctsVec(ExprVector& exps)
    {
      ExprVector expsn;
      for (auto e : exps)
      {
        e = removeRedundantConjuncts(e);
        if (!isOpX<TRUE>(e)) expsn.push_back(e);
      }
      exps = expsn;
    }

    /**
     * Remove some redundant disjuncts from the formula
     */
    template <typename Range> void removeRedundantDisjuncts(Range& disjs)
    {
      if (disjs.size() < 2) return;

      for (auto it = disjs.begin(); it != disjs.end(); )
      {
        if (isFalse (*it))
        {
          it = disjs.erase(it);
          continue;
        }

        auto newDisjsTry = disjs;
        for (auto it2 = newDisjsTry.begin(); it2 != newDisjsTry.end(); )
          if (*it == *it2)
            it2 = newDisjsTry.erase(it2);
          else
            ++it2;

        if (implies (*it, disjoin(newDisjsTry, efac)))
        {
           it = disjs.erase(it);
           continue;
        }
        ++it;
      }
    }

    Expr removeRedundantDisjuncts(Expr exp)
    {
      ExprSet disjs;
      getDisj(exp, disjs);
      if (disjs.size() < 2) return exp;
      else
      {
        removeRedundantDisjuncts(disjs);
        return disjoin(disjs, efac);
      }
    }

    // to extend
    Expr simplifiedAnd(Expr a, Expr b)
    {
      ExprVector disjs, vars;
      flatten(a, disjs, false, vars, [](Expr a, ExprVector& b){return a;});
      for (auto it = disjs.begin(); it != disjs.end(); )
      {
        if (!isSat(*it, b)) it = disjs.erase(it);
        else ++it;
      }
      return mk<AND>(distribDisjoin(disjs, efac), b);
    }

    /**
     * Model-based simplification of a formula with 1 (one only) variable
     */
    Expr numericUnderapprox(Expr exp)
    {
      ExprVector cnstr_vars;
      filter (exp, bind::IsConst (), back_inserter (cnstr_vars));
      if (cnstr_vars.size() == 1)
      {
        resetSolver();
        smt[slv].assertExpr(exp);
        if (smt[slv].solve()) {
          can_get_model = true;
          getModelPtr();
          if (m == NULL) return exp;
          return mk<EQ>(cnstr_vars[0], m->eval(cnstr_vars[0]));
        }
      }
      return exp;
    }

    template <typename Range1, typename Range2, typename Range3> bool
      splitUnsatSets(Range1 & src, Range2 & dst1, Range3 & dst2)
    {
      if (isSat(src)) return false;

      for (auto & a : src) dst1.push_back(a);

      for (auto it = dst1.begin(); it != dst1.end(); )
      {
        dst2.push_back(*it);
        it = dst1.erase(it);
        if (isSat(dst1)) break;
      }

      // now dst1 is SAT, try to get more things from dst2 back to dst1

      for (auto it = dst2.begin(); it != dst2.end(); )
      {
        if (!isSat(conjoin(dst1, efac), *it)) { ++it; continue; }
        dst1.push_back(*it);
        it = dst2.erase(it);
      }

      return true;
    }

    void insertUnique(Expr e, ExprSet& v)
    {
      for (auto & a : v)
        if (isEquiv(a, e)) return;
      v.insert(e);
    }

    void getTrueLiterals(Expr ex, ZSolver<EZ3>::Model &m, ExprSet& lits, bool splitEqs = true)
    {
      ExprVector ites;
      getITEs(ex, ites);
      if (ites.empty())
      {
        getLiterals(ex, lits, splitEqs);
        for (auto it = lits.begin(); it != lits.end(); ){
          if (isOpX<TRUE>(m.eval(*it))) ++it;
          else it = lits.erase(it);
        }
      }
      else
      {
        // eliminate ITEs first
        for (auto it = ites.begin(); it != ites.end();)
        {
          if (isOpX<TRUE>(m((*it)->left())))
          {
            ex = replaceAll(ex, *it, (*it)->right());
            ex = mk<AND>(ex, (*it)->left());
          }
          else if (isOpX<FALSE>(m((*it)->left())))
          {
            ex = replaceAll(ex, *it, (*it)->last());
            ex = mk<AND>(ex, mkNeg((*it)->left()));
          }
          else
          {
            ex = replaceAll(ex, *it, (*it)->right()); // TODO
            ex = mk<AND>(ex, mk<EQ>((*it)->right(), (*it)->last()));
          }
          it = ites.erase(it);
        }
        return getTrueLiterals(ex, m, lits, splitEqs);
      }
    }

    Expr getTrueLiterals(Expr ex, bool splitEqs = true)
    {
      ExprSet lits;
      getModelPtr();
      if (m == NULL) return NULL;
      getTrueLiterals(ex, *m, lits, splitEqs);
      return conjoin(lits, efac);
    }

    bool flatten(Expr fla, ExprVector& prjcts, bool splitEqs, ExprVector& vars,
                 function<Expr(Expr, ExprVector& vars)> qe) // lazy DNF-ization
    {
      resetSolver();
      Expr tmp = fla;
      while (isSat(tmp, false))
      {
        prjcts.push_back(qe(getTrueLiterals(fla, splitEqs), vars)); // if qe is identity, then it's pure DNF
        if (prjcts.back() == NULL) return false;
        tmp = mk<NEG>(prjcts.back());
      }
      return true;
    }

    Expr getWeakerMBP(Expr mbp, Expr fla, ExprVector& srcVars)
    {
      if (containsOp<ARRAY_TY>(fla)) return mbp;

      ExprSet cnjs;
      getConj(mbp, cnjs);
      if (cnjs.size() == 1) return mbp;

      ExprSet varsSet;
      filter (fla, bind::IsConst (), inserter(varsSet, varsSet.begin()));
      minusSets(varsSet, srcVars);

      ExprVector args;
      Expr efla;
      for (auto & v : varsSet) args.push_back(v->left());
      if (args.empty()) efla = fla;
      else {
        args.push_back(fla);
        efla = mknary<EXISTS>(args);
      }

      bool prog = true;
      while (prog)
      {
        prog = false;
        for (auto it = cnjs.begin(); it != cnjs.end();)
        {
          ExprVector cnjsTmp;
          for (auto & a : cnjs) if (a != *it) cnjsTmp.push_back(a);
          if (implies(conjoin(cnjsTmp, efac), efla))
          {
            prog = true;
            it = cnjs.erase(it);
          }
          else ++it;
        }
      }
      return conjoin(cnjs, efac);
    }

    Expr getImplDecomp(Expr a, Expr b)
    {
      // if a == a1 /\ a2 s.t. b => a1 then return a2
      ExprSet cnjs;
      getConj(a, cnjs);
      for (auto it = cnjs.begin(); it != cnjs.end();)
        if (implies(b, *it)) it = cnjs.erase(it);
        else ++it;
      return conjoin(cnjs, efac);
    }

    void print (Expr e, std::ostream& out = outs())
    {
      if (isOpX<FORALL>(e) || isOpX<EXISTS>(e))
      {
        if (isOpX<FORALL>(e)) out << "(forall (";
        else out << "(exists (";

        for (int i = 0; i < e->arity() - 1; i++)
        {
          Expr var = bind::fapp(e->arg(i));
          out << "(" << z3.toSmtLib(var) << " " << z3.toSmtLib(typeOf(var)) << ")";
          if (i != e->arity() - 2) out << " ";
        }
        out << ") ";
        print (e->last(), out);
        out << ")";
      }
      else if (isOpX<NEG>(e))
      {
        out << "(not ";
        print(e->left(), out);
        out << ")";
      }
      else if (isOpX<AND>(e))
      {
        out << "(and ";
        ExprSet cnjs;
        getConj(e, cnjs);
        int i = 0;
        for (auto & c : cnjs)
        {
          i++;
          print(c, out);
          if (i != cnjs.size()) out << " ";
        }
        out << ")";
      }
      else if (isOpX<OR>(e))
      {
        out << "(or ";
        ExprSet dsjs;
        getDisj(e, dsjs);
        int i = 0;
        for (auto & d : dsjs)
        {
          i++;
          print(d, out);
          if (i != dsjs.size()) out << " ";
        }
        out << ")";
      }
      else if (isOpX<IMPL>(e) || isOp<ComparissonOp>(e))
      {
        if (isOpX<IMPL>(e)) out << "(=> ";
        if (isOpX<EQ>(e)) out << "(= ";
        if (isOpX<GEQ>(e)) out << "(>= ";
        if (isOpX<LEQ>(e)) out << "(<= ";
        if (isOpX<LT>(e)) out << "(< ";
        if (isOpX<GT>(e)) out << "(> ";
        if (isOpX<NEQ>(e)) out << "(distinct ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOpX<ITE>(e))
      {
        out << "(ite ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << " ";
        print(e->last(), out);
        out << ")";
      }
      else out << z3.toSmtLib (e);
    }

    void serialize_formula(Expr form)
    {
      outs() << "(assert ";
      print (form);
      outs() << ")\n";
    }
  };

  /**
   * Horn-based interpolation over particular vars
   */
  inline Expr getItp(Expr A, Expr B, ExprVector& sharedVars)
  {
    ExprFactory &efac = A->getFactory();
    EZ3 z3(efac);

    ExprVector allVars;
    filter (mk<AND>(A,B), bind::IsConst (), back_inserter (allVars));

    ExprVector sharedTypes;

    for (auto &var: sharedVars) {
      sharedTypes.push_back (bind::typeOf (var));
    }
    sharedTypes.push_back (mk<BOOL_TY> (efac));

    // fixed-point object
    ZFixedPoint<EZ3> fp (z3);
    ZParams<EZ3> params (z3);
    params.set (":engine", "pdr");
    params.set (":xform.slice", false);
    params.set (":xform.inline-linear", false);
    params.set (":xform.inline-eager", false);
    fp.set (params);

    Expr errRel = bind::boolConstDecl(mkTerm<string> ("err", efac));
    fp.registerRelation(errRel);
    Expr errApp = bind::fapp (errRel);

    Expr itpRel = bind::fdecl (mkTerm<string> ("itp", efac), sharedTypes);
    fp.registerRelation (itpRel);
    Expr itpApp = bind::fapp (itpRel, sharedVars);

    fp.addRule(allVars, boolop::limp (A, itpApp));
    fp.addRule(allVars, boolop::limp (mk<AND> (B, itpApp), errApp));

    tribool res;
    try {
      res = fp.query(errApp);
    } catch (z3::exception &e){
      char str[3000];
      strncpy(str, e.msg(), 300);
      errs() << "Z3 ex: " << str << "...\n";
      exit(55);
    }

    if (res) return NULL;

    return fp.getCoverDelta(itpApp);
  }

  /**
   * Horn-based interpolation
   */
  inline Expr getItp(Expr A, Expr B)
  {
    ExprVector sharedVars;

    ExprVector aVars;
    filter (A, bind::IsConst (), back_inserter (aVars));

    ExprVector bVars;
    filter (B, bind::IsConst (), back_inserter (bVars));

    // computing shared vars:
    for (auto &var: aVars) {
      if (find(bVars.begin(), bVars.end(), var) != bVars.end())
      {
        sharedVars.push_back(var);
      }
    }

    return getItp(A, B, sharedVars);
  };

}

#endif
