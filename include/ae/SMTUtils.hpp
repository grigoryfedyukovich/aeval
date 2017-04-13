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
    efac(_efac),
    z3(efac),
    smt (z3)
    {}
    
    /**
     * SMT-check
     */
    bool isSat(Expr a)
    {
      smt.reset();
      smt.assertExpr (a);
      if (!smt.solve ()) {
        return false;
      }
      return true;
    }
    
    /**
     * SMT-based formula equivalence check
     */
    bool isEquiv(Expr a, Expr b)
    {
      return !isSat(mk<AND>(a, mk<NEG>(b))) &&
      !isSat(mk<AND>(b, mk<NEG>(a)));
    }
    
    /**
     * SMT-based implication check
     */
    bool isImplies (Expr a, Expr b)
    {
      return ! isSat(mk<AND>(a, mk<NEG>(b)));
    }
    
    /**
     * SMT-based check for a tautology
     */
    bool isTrue(Expr a){
      if (isOpX<TRUE>(a)) return true;
      return isEquiv(a, mk<TRUE>(efac));
    }
    
    /**
     * SMT-based check for false
     */
    bool isFalse(Expr a){
      if (isOpX<FALSE>(a)) return true;
      return isEquiv(a, mk<FALSE>(efac));
    }
    
    /**
     * ITE-simplifier (prt 2)
     */
    Expr simplifyITE(Expr ex, Expr upLevelCond)
    {
      ex = replaceAll(ex, upLevelCond, mk<TRUE>(efac));
      
      if (isOpX<ITE>(ex)){
        
        Expr cond = ex->arg(0);
        Expr br1 = ex->arg(1);
        Expr br2 = ex->arg(2);
        
        Expr updCond1 = mk<AND>(upLevelCond, mk<NEG>(cond));
        Expr updCond2 = mk<AND>(mk<NEG>(upLevelCond), cond);
        
        if (!isSat(updCond1)) return br1;
        
        if (!isSat(updCond2)) return br2;
        
        return mk<ITE>(cond,
                       simplifyITE(br1, updCond1),
                       simplifyITE(br2, updCond2));
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
    
    /**
     * Remove some redundant conjuncts from the formula
     */
    Expr removeRedundantConjuncts(Expr exp)
    {
      ExprSet newCnjs;
      ExprSet conjs;
      getConj(exp, conjs);
      
      if (conjs.size() < 2) return exp;
      
      for (auto & cnj : conjs)      // GF: todo: incremental solving
      {
        if (isTrue (cnj)) continue;
        
        if (isEquiv (conjoin(newCnjs, efac), mk<AND>(conjoin(newCnjs, efac), cnj))) continue;
        
        newCnjs.insert(cnj);
      }
      
      return conjoin(newCnjs, efac);
    }
    
    /**
     * Remove some redundant disjuncts from the formula
     */
    Expr removeRedundantDisjuncts(Expr exp)
    {
      ExprSet newDisj;
      ExprSet disjs;
      getDisj(exp, disjs);
      
      if (disjs.size() < 2) return exp;
      
      for (auto & disj : disjs)      // GF: todo: incremental solving
      {
        if (isFalse (disj)) continue;
        
        if (isEquiv (disjoin(newDisj, efac), mk<OR>(disjoin(newDisj, efac), disj))) continue;
        
        newDisj.insert(disj);
      }
      
      return disjoin(newDisj, efac);
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
    
    if (res) return mk<FALSE> (efac);
    
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
