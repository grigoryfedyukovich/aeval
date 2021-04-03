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
    ZSolver<EZ3> smt;

  public:

    SMTUtils (ExprFactory& _efac) :
      efac(_efac), z3(efac), smt (z3) {}

    SMTUtils (ExprFactory& _efac, unsigned _to) :
      efac(_efac), z3(efac), smt (z3, _to) {}

    Expr getModel(Expr v)
    {
      ExprVector eqs;
      ZSolver<EZ3>::Model m = smt.getModel();
      return m.eval(v);
    }

    template <typename T> Expr getModel(T& vars)
    {
      ExprVector eqs;
      ZSolver<EZ3>::Model m = smt.getModel();
      bool res = true;
      for (auto & v : vars)
      {
        Expr e = m.eval(v);
        if (e == NULL)
        {
          res = false;
          return NULL;
        }
        else if (e != v)
        {
          eqs.push_back(mk<EQ>(v, e));
        }
        else
        {
          if (bind::isBoolConst(v))
          eqs.push_back(mk<EQ>(v, mk<TRUE>(efac)));
          else if (bind::isIntConst(v))
          eqs.push_back(mk<EQ>(v, mkTerm (mpz_class (0), efac)));
        }
      }
      if (!res) return NULL;
      return conjoin (eqs, efac);
    }

    ExprSet allVars;
    Expr getModel() { return getModel(allVars); }

    template <typename T> boost::tribool isSat(T& cnjs, bool reset=true)
    {
      allVars.clear();
      if (reset) smt.reset();
      for (auto & c : cnjs)
      {
        filter (c, bind::IsConst (), inserter (allVars, allVars.begin()));
        smt.assertExpr(c);
      }
      boost::tribool res = smt.solve ();
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
      ExprSet cnjs;
      getConj(a, cnjs);
      return isSat(cnjs, reset);
    }

    /**
     * SMT-based formula equivalence check
     */
    bool isEquiv(Expr a, Expr b)
    {
      return implies (a, b) && implies (b, a);
    }

    /**
     * SMT-based implication check
     */
    bool implies (Expr a, Expr b)
    {
      if (isOpX<TRUE>(b)) return true;
      if (isOpX<FALSE>(a)) return true;
      return bool(!isSat(a, mkNeg(b)));
    }

    /**
     * SMT-based check for a tautology
     */
    bool isTrue(Expr a){
      if (isOpX<TRUE>(a)) return true;
      return bool(!isSat(mkNeg(a)));
    }

    /**
     * SMT-based check for false
     */
    bool isFalse(Expr a){
      if (isOpX<FALSE>(a)) return true;
      if (isOpX<NEQ>(a) && a->left() == a->right()) return true;
      return bool(!isSat(a));
    }

    /**
     * Check if v has only one sat assignment in phi
     */
    bool hasOneModel(Expr v, Expr phi) {
      if (isFalse(phi)) return false;

      ZSolver<EZ3>::Model m = smt.getModel();
      Expr val = m.eval(v);
      if (v == val) return false;

      ExprSet assumptions;
      assumptions.insert(mk<NEQ>(v, val));

      return bool((!isSat(assumptions, false)));
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

    /**
     * Remove some redundant disjuncts from the formula
     */
    void removeRedundantDisjuncts(ExprSet& disjs)
    {
      if (disjs.size() < 2) return;
      ExprSet newDisjs = disjs;

      for (auto & disj : disjs)
      {
        if (isFalse (disj))
        {
          newDisjs.erase(disj);
          continue;
        }

        ExprSet newDisjsTry = newDisjs;
        newDisjsTry.erase(disj);

        if (implies (disj, disjoin(newDisjsTry, efac))) newDisjs.erase(disj);
      }
      disjs = newDisjs;
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

    /**
     * Model-based simplification of a formula with 1 (one only) variable
     */
    Expr numericUnderapprox(Expr exp)
    {
      ExprVector cnstr_vars;
      filter (exp, bind::IsConst (), back_inserter (cnstr_vars));
      if (cnstr_vars.size() == 1)
      {
        smt.reset();
        smt.assertExpr (exp);
        if (smt.solve ()) {
          ZSolver<EZ3>::Model m = smt.getModel();
          return mk<EQ>(cnstr_vars[0], m.eval(cnstr_vars[0]));
        }
      }
      return exp;
    }

    inline static string varType (Expr var)
    {
      if (bind::isIntConst(var))
        return "Int";
      else if (bind::isRealConst(var))
        return "Real";
      else if (bind::isBoolConst(var))
        return "Bool";
      else if (bind::isConst<ARRAY_TY> (var))
      {
        Expr name = mkTerm<string> ("", var->getFactory());
        Expr s1 = bind::mkConst(name, var->last()->right()->left());
        Expr s2 = bind::mkConst(name, var->last()->right()->right());
        return string("(Array ") + varType(s1) + string(" ") + varType(s2) + string(")");
      }
      else return "";
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

    bool isModelSkippable(Expr model, ExprVector& vars, map<int, ExprVector>& cands)
    {
      if (model == NULL) return true;

      if (containsOp<EXISTS>(model) || containsOp<FORALL>(model)) return true;
      
      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;

        Expr tmp = getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp))
        {
          return true;
        }
      }

//      for (auto & a : cands)
//      {
//        for (auto & b : a.second)
//        {
//          if (containsOp<FORALL>(b)) return true;
//        }
//      }
      return false;
    }

    bool isModelSkippable(Expr v)
    {
      Expr tmp = getModel(v);
      if (tmp == NULL) return true;
      if (!containsOp<ARRAY_TY>(v)) return false;
      if (tmp != v && !isNumeric(v) && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp)) return true;
      return false;
    }

    bool isModelSkippable()
    {
      for (auto & v : allVars) if (isModelSkippable(v)) return true;
      return false;
    }

    void insertUnique(Expr e, ExprSet& v)
    {
      for (auto & a : v)
        if (isEquiv(a, e)) return;
      v.insert(e);
    }

    Expr getTrueLiterals(Expr ex, Expr model)
    {
      ExprVector ites;
      getITEs(ex, ites);
      if (ites.empty())
      {
        ExprSet tmp;
        getLiterals(ex, tmp);
        for (auto it = tmp.begin(); it != tmp.end(); ){
          if (isSat(model, (Expr)*it)) ++it;
          else it = tmp.erase(it);
        }
        return conjoin(tmp, efac);
      }
      else
      {
        // eliminate ITEs first
        for (auto it = ites.begin(); it != ites.end();)
        {
          if (isSat(model, (Expr)(*it)->left()))
          {
            ex = replaceAll(ex, *it, (*it)->right());
            ex = mk<AND>(ex, (*it)->left());
          }
          else
          {
            ex = replaceAll(ex, *it, (*it)->last());
            ex = mk<AND>(ex, mkNeg((*it)->left()));
          }
          it = ites.erase(it);
        }
        return getTrueLiterals(simplifyBool(simplifyArithm(ex)), model);
      }
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
      for (auto & v : varsSet) args.push_back(v->left());
      args.push_back(fla);
      Expr efla = mknary<EXISTS>(args);

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

    void print (Expr e)
    {
      if (isOpX<FORALL>(e) || isOpX<EXISTS>(e))
      {
        if (isOpX<FORALL>(e)) outs () << "(forall (";
        else outs () << "(exists (";

        for (int i = 0; i < e->arity() - 1; i++)
        {
          Expr var = bind::fapp(e->arg(i));
          outs () << "(" << *var << " " << varType(var) << ")";
          if (i != e->arity() - 2) outs () << " ";
        }
        outs () << ") ";
        print (e->last());
        outs () << ")";
      }
      else if (isOpX<NEG>(e))
      {
        outs () << "(not ";
        print(e->left());
        outs () << ")";
      }
      else if (isOpX<AND>(e))
      {
        outs () << "(and ";
        ExprSet cnjs;
        getConj(e, cnjs);
        int i = 0;
        for (auto & c : cnjs)
        {
          i++;
          print(c);
          if (i != cnjs.size()) outs () << " ";
        }
        outs () << ")";
      }
      else if (isOpX<OR>(e))
      {
        outs () << "(or ";
        ExprSet dsjs;
        getDisj(e, dsjs);
        int i = 0;
        for (auto & d : dsjs)
        {
          i++;
          print(d);
          if (i != dsjs.size()) outs () << " ";
        }
        outs () << ")";
      }
      else if (isOpX<IMPL>(e) || isOp<ComparissonOp>(e))
      {
        if (isOpX<IMPL>(e)) outs () << "(=> ";
        if (isOpX<EQ>(e)) outs () << "(= ";
        if (isOpX<GEQ>(e)) outs () << "(>= ";
        if (isOpX<LEQ>(e)) outs () << "(<= ";
        if (isOpX<LT>(e)) outs () << "(< ";
        if (isOpX<GT>(e)) outs () << "(> ";
        if (isOpX<NEQ>(e)) outs () << "(distinct ";
        print(e->left());
        outs () << " ";
        print(e->right());
        outs () << ")";
      }
      else if (isOpX<ITE>(e))
      {
        outs () << "(ite ";
        print(e->left());
        outs () << " ";
        print(e->right());
        outs () << " ";
        print(e->last());
        outs () << ")";
      }
      else outs () << z3.toSmtLib (e);
    }

    void serialize_formula(Expr form)
    {
      outs () << "(assert ";
      print (form);
      outs () << ")\n";

      // old version (to  merge, maybe?)
//      smt.reset();
//      smt.assertExpr(form);
//      smt.toSmtLib (outs());
//      outs().flush ();
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
      outs() << "Z3 ex: " << str << "...\n";
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
