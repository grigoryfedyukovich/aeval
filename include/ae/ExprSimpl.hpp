#ifndef EXPRSIMPL__HPP__
#define EXPRSIMPL__HPP__
#include <assert.h>

#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  /**
   * Represent Expr as multiplication
   */
  inline static Expr mult(Expr e){
    if (isOpX<MULT>(e)){
      return e;
    } else {
      return mk<MULT>(e, mkTerm (mpz_class (1), e->getFactory()));
    }
  }
  
  /**
   * Represent Zero as multiplication
   */
  inline static Expr multZero(Expr e, Expr multiplier){
    if (lexical_cast<string>(e) == "0")
      return mk<MULT>(multiplier, e);
    else return e;
  }
  
  /**
   * Rewrites distributivity rule:
   * a*b + a*c -> a*(b + c)
   * (assume, all common multipliers might be only in the first place)
   */
  inline static Expr exprDistributor(Expr e){
    if (e->arity () == 0) return e;
    Expr multiplier = mult(e->arg(0));
    ExprSet newE;
    newE.insert(multiplier->right());
    multiplier = multiplier->left();
    
    for (unsigned i = 1; i < e->arity (); i++){
      Expr a = mult(e->arg(i));
      if (isOpX<MULT>(a)){
        if (a->left() == multiplier){
          newE.insert(a->right());
        } else {
          return e;
        }
      } else {
        return e;
      }
    }
    if (isOpX<PLUS>(e)){
      return mk<MULT>(multiplier, mknary<PLUS>(newE));
    }
    return e;
  }
  
  /**
   * Self explanatory
   */
  inline static bool IsConstOrItsAdditiveInverse(Expr e, Expr var){
    if (e == var) {
      return true;
    }
    if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1" && e->right() == var){
        return true;
      }
    }
    
    return false;
  }
  
  /**
   * Self explanatory
   */
  inline static Expr additiveInverse(Expr e){
    if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1"){
        return e->right();
      }
    }
    return mk<MULT>(mkTerm (mpz_class (-1), e->getFactory()), e);
  }
  
  /**
   * Commutativity in Addition
   */
  inline static Expr exprSorted(Expr e){
    Expr res = e;
    if (isOpX<PLUS>(e)) {
      ExprSet expClauses;
      for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it){
        expClauses.insert(*it);
      }
      res = mknary<PLUS>(expClauses);
    }
    
    if (isOpX<MULT>(e)) {
      if (lexical_cast<string>(e->left())  == "-1"){
        Expr l = e->right();
        
        if (isOpX<PLUS>(l)) {
          ExprSet expClauses;
          for (auto it = l->args_begin(), end = l->args_end(); it != end; ++it){
            expClauses.insert(additiveInverse(*it));
          }
          res = mknary<PLUS>(expClauses);
        }
      }
    }
    
    return res;
  }
  
  /**
   * Helper used in ineqReverter
   */
  template <typename T> static Expr rewriteHelperN(Expr e){
    assert(e->arity() == 2);
    Expr minus_one = mkTerm (mpz_class (-1), e->getFactory());
    
    Expr l = multZero(e->left(), minus_one);
    Expr r = multZero(exprDistributor(e->right()), minus_one);
    if (!isOpX<MULT>(r))
      r = mk<MULT>(minus_one, mk<MULT>(minus_one,r)); // a bit of hack
    
    if (isOpX<MULT>(l) && isOpX<MULT>(r)){
      if (lexical_cast<string>(l->left())  == "-1" &&
          lexical_cast<string>(r->left())  == "-1" ){
        return mk<T>(l->right(), r->right());
      }
    }
    return e;
  }
  
  /**
   *  Helper used in ineqMover
   */
  template <typename T> static Expr rewriteHelperM(Expr e, Expr var){
    Expr l = e->left();
    Expr r = e->right();
    Expr lhs;     // expression, containing var; assume, var contains only in one clause
    ExprSet rhs;  // the rest of e
    
    // first, parse l;
    
    if (isOpX<PLUS>(l)){
      for (unsigned i = 0; i < l->arity (); i++){
        Expr a = l->arg(i);
        if (IsConstOrItsAdditiveInverse(a, var)){
          lhs = a;
          continue;
        }
        rhs.insert(additiveInverse(a));
      }
    } else {
      if (IsConstOrItsAdditiveInverse(l, var)){
        lhs = l;
      } else if (lexical_cast<string>(l) != "0"){
        rhs.insert(additiveInverse(l));
      }
    }
    
    // second, parse r;
    
    if (isOpX<PLUS>(r)){
      for (unsigned i = 0; i < r->arity (); i++){
        Expr a = r->arg(i);
        if (IsConstOrItsAdditiveInverse(a, var)){
          lhs = additiveInverse(a);
          continue;
        }
        rhs.insert(a);
      }
    } else {
      if (IsConstOrItsAdditiveInverse(r, var)){
        lhs = additiveInverse(r);
      } else if (lexical_cast<string>(r) != "0"){
        rhs.insert(r);
      }
    }
    
    // third, combine results;
    
    if (lhs != 0){
      Expr rhsPlus;
      if (rhs.size() > 1){
        rhsPlus = exprDistributor(mknary<PLUS>(rhs));
      } else if (rhs.size() == 1) {
        rhsPlus = *rhs.begin();
      } else if (rhs.size() == 0) {
        rhsPlus = mkTerm (mpz_class (0), e->getFactory());
      }
      return mk<T>(lhs,rhsPlus);
    }
    return e;
  }
  
  /**
   * Helper used in exprMover
   */
  template <typename T> static Expr rewriteHelperE(Expr e, Expr var){
    //todo: debug: clean = false -> shared_ptr.hpp:418: Assertion `px != 0' failed
    assert(e->arity() == 2);
    Expr l = e->left();
    Expr r = e->right();
    if (r == var) {
      l = exprSorted(l);
      return mk<T>(r, l);
    }
    
    if (isOpX<MULT>(r)){
      if (r->left() == var || r->right() == var){
        l = exprSorted(l);
        return mk<T>(r, l);
      }
    }
    return e;
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= b && a >= b) -> (a == b)
   */
  inline static void ineqMerger(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<LEQ>(e)){
        for (auto &e2: expClauses){
          if (isOpX<GEQ>(e2)){
            if (e->left() == e2->left()){
              Expr e1r = exprSorted(e->right());
              Expr e2r = exprSorted(e2->right());
              if ( e1r == e2r ){
                if (clean){
                  expClauses.erase(e);
                  expClauses.erase(e2);
                }
                expClauses.insert(mk<EQ>(e->left(), e1r));
              }
            }
          }
        }
      }
    }
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= b && b <= a) -> (a == b)
   */
  template <typename T> static void ineqMergerSwap(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->left() == e2->right() && e->right() == e2->left()){
              if (clean){
                expClauses.erase(e);
                expClauses.erase(e2);
              }
              expClauses.insert(mk<EQ>(e->left(), e->right()));
            }
          }
        }
      }
    }
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= 0 && -a <= 0) -> (a == 0)
   *  (a >= 0 && -a >= 0) -> (a == 0)
   */
  template <typename T> static void ineqMergerSwapMinus(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->right() == e2->right() && e2->right() == mkTerm (mpz_class (0), e2->getFactory())){
              Expr l1 = exprSorted(additiveInverse(e->left()));
              Expr l2 = exprSorted(e2->left());
              if (l1 == l2){
                if (clean){
                  expClauses.erase(e);
                  expClauses.erase(e2);
                }
                expClauses.insert(mk<EQ>(e->left(), e->right()));
              }
            }
          }
        }
      }
    }
  }
  
  /**
   *  Trivial simplifier:
   *  (-1*a <= -1*b) -> (a >= b)
   *  (-1*a >= -1*b) -> (a <= b)
   *  (-1*a == -1*b) -> (a == b)
   */
  inline static Expr ineqReverter(Expr e){
      if (isOpX<LEQ>(e)){
        return rewriteHelperN<GEQ>(e);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperN<LEQ>(e);
      } else if (isOpX<LT>(e)){
        return rewriteHelperN<GT>(e);
      } else if (isOpX<GT>(e)){
        return rewriteHelperN<LT>(e);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperN<EQ>(e);
      }
    return e;
  }
  
  inline static Expr ineqNegReverter(Expr a){
    if (isOpX<NEG>(a)){
      Expr e = a->arg(0);
      if (isOpX<LEQ>(e)){
        return mk<GT>(e->arg(0), e->arg(1));
      } else if (isOpX<GEQ>(e)){
        return mk<LT>(e->arg(0), e->arg(1));
      } else if (isOpX<LT>(e)){
        return mk<GEQ>(e->arg(0), e->arg(1));
      } else if (isOpX<GT>(e)){
        return mk<LEQ>(e->arg(0), e->arg(1));
      }
    }
    return a;
  }
  
  /**
   *  Transform the inequalities by the following rules:
   *  (a + .. + var + .. + b <= c ) -> (var <= -1*a + .. + -1*b + c)
   *  (a + .. + -1*var + .. + b <= c) -> (-1*var <= -1*a + .. + -1*b + c )
   *  (a <= b + .. + var + .. + c) -> (-1*var <= (-1)*a + b + .. + c)
   *  (a <= b + .. + (-1)*var + .. + c) -> (var <= (-1)*a + b + .. + c)
   *
   *  same for >=
   */
  inline static Expr ineqMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperM<LEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperM<GEQ>(e, var);
      } else if (isOpX<LT>(e)){
        return rewriteHelperM<LT>(e, var);
      } else if (isOpX<GT>(e)){
        return rewriteHelperM<GT>(e, var);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperM<EQ>(e, var);
      }
    return e;
  }
  
  /**
   *  Move "var" to the left hand side of expression:
   *  (a <= var) -> (var >= b)
   *  (a >= var) -> (var <= b)
   *  (a == var) -> (var == b)
   */
  inline static Expr exprMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperE<GEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperE<LEQ>(e, var);
      } if (isOpX<EQ>(e)){
        return rewriteHelperE<EQ>(e, var);
      } if (isOpX<NEG>(e)){
        return mk<NEG>(exprMover(e->arg(0), var));
      }
    return e;
  }
  
  /**
   *
   */
  inline static Expr eqDiffMover(Expr e){
    if(isOpX<EQ>(e)){
      if (isOpX<MINUS>(e->left()) && e->left()->arity() == 2 && lexical_cast<string>(e->right()) == "0"){
        return mk<EQ>(e->left()->left(), e->left()->right());
      }
    }
    return e;
  }
  
  /**
   * Search for an equality
   */
  inline static bool equalitySearch(ExprSet& expClauses, Expr var){
    for (auto &e: expClauses){
      if (isOpX<EQ>(e)){
        Expr l = e->left();
        Expr r = e->right();
        if (l == var || r == var){
          ExprSet singleton;
          singleton.insert(e);
          expClauses = singleton;
          return true;
        }
      }
    }
    return false;
  }
  
  template<typename Range> static Expr conjoin(Range& conjs, ExprFactory &efac){
    return
      (conjs.size() == 0) ? mk<TRUE>(efac) :
      (conjs.size() == 1) ? *conjs.begin() :
        mknary<AND>(conjs);
  }

  template<typename Range> static Expr disjoin(Range& disjs, ExprFactory &efac){
    return
      (disjs.size() == 0) ? mk<FALSE>(efac) :
      (disjs.size() == 1) ? *disjs.begin() :
        mknary<OR>(disjs);
  }
  
  template<typename Range> static Expr mkplus(Range& terms, ExprFactory &efac){
    return
      (terms.size() == 0) ? mkTerm (mpz_class (0), efac) :
      (terms.size() == 1) ? *terms.begin() :
        mknary<PLUS>(terms);
  }
  
  /**
   * Simplifier Wrapper
   */
  inline static Expr ineqSimplifier(Expr v, Expr exp){
    ExprSet substsMap;
    if (isOpX<AND>(exp)){
      for (ENode::args_iterator it = exp->args_begin(), end = exp->args_end();
           it != end; ++it){
        Expr cl = *it;
        cl = exprMover(*it, v);
        cl = ineqMover(cl, v);
        cl = ineqReverter (cl);
        substsMap.insert(cl);
      }
      
      ineqMerger(substsMap);
      equalitySearch(substsMap, v);
      return conjoin(substsMap, v->getFactory());
      
    }
    return exp;
  }
  
  
  template<typename T>
  struct RW
  {
    std::shared_ptr<T> _r;
    
    RW (std::shared_ptr<T> r) : _r(r) {}
    RW (T *r) : _r (r) {}
    
    
    VisitAction operator() (Expr exp)
    {
      // -- apply the rewriter
      if (exp->arity() == 0)
        // -- do not descend into non-boolean operators
        return VisitAction::skipKids ();
      
      return VisitAction::changeDoKidsRewrite (exp, _r);
      
    }
  };
  
  inline static Expr simplifiedPlus (Expr exp, Expr to_skip){
    
    ExprVector args;
    
    Expr ret;
    
    for (ENode::args_iterator it = exp->args_begin(),
         end = exp->args_end(); it != end; ++it){
      Expr a = *it;
      if (a != to_skip) {
        args.push_back (a);
      }
    }
    
    if (args.size() == 1) {
      ret = args[0];
    }
    
    else if (args.size() == 2){
      if (isOpX<UN_MINUS>(args[0]) && !isOpX<UN_MINUS>(args[1]))
        ret =  mk<MINUS>(args[1], args[0]->left());
      else if (!isOpX<UN_MINUS>(args[0]) && isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[0], args[1]->left());
      
      else ret = mknary<PLUS>(args);
      
    } else {
      ret = mknary<PLUS>(args);
    }
    
    return ret;
  }
  
  // return a - b
  inline static Expr simplifiedMinus (Expr a, Expr b){
    
    Expr ret = mk<MINUS>(a, b);
    
    if (a == b) {
      ret = mkTerm (mpz_class (0), a->getFactory());
    } else
      
      if (isOpX<PLUS>(a)){
        Expr res = simplifiedPlus(a, b);
        if (res->arity() == a->arity() - 1) ret = res;
      } else
        
        if (isOpX<PLUS>(b)){
          Expr res = simplifiedPlus(b, a);
          if (res->arity() == b->arity() - 1) ret = mk<UN_MINUS>(res);
        } else
          
          if (isOpX<MINUS>(a)){
            if (a->left() == b) ret = mk<UN_MINUS>(a->right());
          } else
            
            if (isOpX<MINUS>(b)){
              if (a == b->right()) ret = mk<UN_MINUS>(b->left());
            } else
              
              if (isOpX<UN_MINUS>(b)) {
                if (b->left() == mkTerm (mpz_class (0), a->getFactory())) {
                  ret = a;
                } else {
                  ret = mk<PLUS>(a,b->left());
                }
              } else
                
                if (mkTerm (mpz_class (-1), a->getFactory()) == b) {
                  ret = simplifiedPlus(a, mkTerm (mpz_class (1), a->getFactory()));
                } else
                  
                  if (b == mkTerm (mpz_class (0), a->getFactory())) {
                    ret = a;
                  } else
                    
                    if (a == mkTerm (mpz_class (0), a->getFactory())){
                      if (isOpX<UN_MINUS>(b)){
                        ret = b->left();
                      }
                      else {
                        ret = mk<UN_MINUS>(b);
                      }
                    }
    
    return ret;
  }
  
  struct SimplifyArithmExpr
  {
    ExprFactory &efac;
    
    Expr zero;
    Expr one;
    Expr minus_one;
    
    SimplifyArithmExpr (ExprFactory& _efac):
    efac(_efac)
    {
      zero = mkTerm (mpz_class (0), efac);
      one = mkTerm (mpz_class (1), efac);
      minus_one = mkTerm (mpz_class (1), efac);
    };
    
    Expr operator() (Expr exp)
    {
      if (isOpX<PLUS>(exp))
      {
        return simplifiedPlus(exp, zero);
      }
      
      if (isOpX<MINUS>(exp) && exp->arity() == 2)
      {
        return simplifiedMinus(exp->left(), exp->right());
      }
      
      if (isOpX<MULT>(exp))
      {
        if (exp->left() == zero) return zero;
        if (exp->right() == zero) return zero;
        if (exp->left() == one) return exp->right();
        if (exp->right() == one) return exp->left();
        if (exp->left() == minus_one) return mk<UN_MINUS>(exp->right());
        if (exp->right() == minus_one) return mk<UN_MINUS>(exp->left());
      }
      
      if (isOpX<UN_MINUS>(exp))
      {
        Expr uneg = exp->left();
        if (uneg == zero) return zero;
        if (uneg == minus_one) return one;
        if (isOpX<UN_MINUS>(uneg)) return uneg->left();
        if (isOpX<PLUS>(uneg)){
          Expr unegl = uneg->left();
          Expr unegr = uneg->right();
          if (isOpX<UN_MINUS>(unegl)) return mk<MINUS>(unegl->left(), unegr);
          if (isOpX<UN_MINUS>(unegr)) return mk<MINUS>(unegr->left(), unegl);
        }
      }
      
      if (isOpX<MINUS>(exp))
      {
        if (isOpX<UN_MINUS>(exp->right())) return mk<PLUS>(exp->left(), exp->right()->left());
      }
      return exp;
    }
  };
  
  struct SimplifyBoolExpr
  {
    ExprFactory &efac;
    
    SimplifyBoolExpr (ExprFactory& _efac) : efac(_efac){};
    
    Expr operator() (Expr exp)
    {
      // GF: to enhance
      
      if (isOpX<IMPL>(exp))
      {
        if (isOpX<TRUE>(exp->right()))
          return mk<TRUE>(efac);

        if (isOpX<FALSE>(exp->right()))
          return mk<NEG>(exp->left());
        
        return (mk<OR>(
                 mk<NEG>(exp->left()),
                 exp->right()));
      }
      
      if (isOpX<OR>(exp)){
        for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it){
          
          if (isOpX<TRUE>(*it)) return mk<TRUE>(efac);
          
          if (isOpX<EQ>(*it) && (*it)->left() == (*it)->right()) return mk<TRUE>(efac);
          
        }
      }
      
      if (isOpX<AND>(exp)){
        for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it){
          
          if (isOpX<FALSE>(*it)) return mk<FALSE>(efac);
          
        }
      }
      
      return exp;
    }
  };
  
  struct PlusMinusChanger
  {
    ExprFactory &efac;
    
    // bool changed;
    
    PlusMinusChanger (ExprFactory& _efac):
    efac(_efac)
    {
      // changed = false;
    };
    
    Expr operator() (Expr exp)
    {
      
      if (isOpX<PLUS>(exp)/* && !changed*/){
        //changed = true;
        ExprSet expClauses;
        bool changed = false;
        expClauses.insert(mkTerm (mpz_class (1), exp->getFactory()));
        for (ENode::args_iterator it = exp->args_begin(), end = exp->args_end();
             it != end; ++it){
          if (changed){
            expClauses.insert(additiveInverse(*it));
          } else {
            expClauses.insert(*it);
          }
          
          changed = !changed;
        }
        Expr res = mknary<PLUS>(expClauses);
        
        return res;
      }
      
      return exp;
    }
  };
  
  inline static Expr simplifyArithm (Expr exp)
  {
    RW<SimplifyArithmExpr> rw(new SimplifyArithmExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }
  
  inline static Expr simplifyBool (Expr exp)
  {
    RW<SimplifyBoolExpr> rw(new SimplifyBoolExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }
  
  inline static Expr randomChangePlusMinus (Expr exp)
  {
    RW<PlusMinusChanger> rw(new PlusMinusChanger(exp->getFactory()));
    return dagVisit (rw, exp);
  }
  
  inline static ExprSet minusSets(ExprSet& v1, ExprSet& v2){
    ExprSet v3;
    bool res;
    for (auto &var1: v1){
      res = true;
      for (auto &var2: v2){
        if (var1 == var2) { res = false; break;}
      }
      if (res) v3.insert(var1);
    }
    return v3;
  }
  
  inline static bool emptyIntersect(Expr a, Expr b){
    ExprVector av;
    ExprVector bv;
    
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    filter (b, bind::IsConst (), inserter(bv, bv.begin()));
    
    for (auto &var1: av){
      for (auto &var2: bv){
        if (var1 == var2){
          return false;
        }
      }
    }
    return true;
  }
  
  inline static bool emptyIntersect(Expr a, ExprSet& bv){
    ExprVector av;
    
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    
    for (auto &var1: av){
      for (auto &var2: bv) if (var1 == var2) return false;
    }
    return true;
  }
  
  inline static bool isNumericConst(Expr e)
  {
    return isOpX<MPZ>(e) || isOpX<MPQ>(e);
  }
  
  template<typename Range> static int getVarIndex(Expr var, Range& vec)
  {
    int i = 0;
    for (auto &e: vec)
    {
      if (var == e) return i;
      i++;
    }
    return -1;
  }
  
  static void getAddTerm (Expr a, ExprVector &terms); // declaration only
  
  inline static Expr arithmInverse(Expr e)
  {
    bool success = true;
    if (isOpX<MULT>(e))
    {
      int coef = 1;
      Expr var = NULL;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        if (isNumericConst(*it))
        {
          coef *= lexical_cast<int>(*it);
        }
        else if (bind::isIntConst(*it) && var == NULL)
        {
          var = *it;
        }
        else
        {
          success = false;
        }
      }
      if (success && coef != 0) return mk<MULT>(mkTerm (mpz_class (-coef), e->getFactory()), e->right());
      
      if (coef == 0) return mkTerm (mpz_class (0), e->getFactory());
    }
    else if (isOpX<PLUS>(e))
    {
      ExprVector terms;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        getAddTerm(arithmInverse(*it), terms);
      }
      return mknary<PLUS>(terms);
    }
    else if (isOpX<MINUS>(e))
    {
      ExprVector terms;
      getAddTerm(arithmInverse(*e->args_begin ()), terms);
      auto it = e->args_begin () + 1;
      for (auto end = e->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
      return mknary<PLUS>(terms);
    }
    else if (isOpX<UN_MINUS>(e))
    {
      return e->left();
    }
    else if (isNumericConst(e))
    {
      return mkTerm (mpz_class (-lexical_cast<int>(e)), e->getFactory());
    }
    return mk<MULT>(mkTerm (mpz_class (-1), e->getFactory()), e);
  }
  
  inline static void getAddTerm (Expr a, ExprVector &terms) // implementation (mutually recursive)
  {
    if (isOpX<PLUS>(a))
    {
      for (auto it = a->args_begin (), end = a->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
    }
    else if (isOpX<MINUS>(a))
    {
      auto it = a->args_begin ();
      auto end = a->args_end ();
      getAddTerm(*it, terms);
//      outs () <<"   [   " << *(*it) << "\n";
      ++it;
      for (; it != end; ++it)
      {
//        outs () << *mk<UN_MINUS>(*it) << "   ]   \n";
        getAddTerm(arithmInverse(*it), terms);
      }
    }
    else
    {
      terms.push_back(a);
    }
  }
  
  struct AddMultDistr
  {
    AddMultDistr () {};
    
    Expr operator() (Expr exp)
    {
      if (isOpX<MULT>(exp))
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();
        
        ExprVector alllhs;
        getAddTerm(lhs, alllhs);
        
        ExprVector allrhs;
        getAddTerm(rhs, allrhs);
        
        ExprVector unf;
        for (auto &a : alllhs)
        {
          for (auto &b : allrhs)
          {
            unf.push_back(mk<MULT>(a, b));
          }
        }
        return mkplus(unf, exp->getFactory());
      }
      
      return exp;
    }
  };
  
  inline static Expr rewriteMultAdd (Expr exp)
  {
    RW<AddMultDistr> mu(new AddMultDistr());
    return dagVisit (mu, exp);
  }
  
  inline static void getConj (Expr a, ExprSet &conjs)
  {
    if (isOpX<TRUE>(a)) return;
    if (isOpX<AND>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getConj(a->arg(i), conjs);
      }
    } else {
      conjs.insert(a);
    }
  }
  
  inline static void getDisj (Expr a, ExprSet &disjs)
  {
    if (isOpX<TRUE>(a)) return;
    if (isOpX<OR>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getDisj(a->arg(i), disjs);
      }
    } else {
      disjs.insert(a);
    }
  }
  
  inline Expr convertToGEandGT(Expr term)
  {   
    if (isOpX<LT>(term)) return mk<GT>(term->right(), term->left());
    
    if (isOpX<LEQ>(term)) return mk<GEQ>(term->right(), term->left());
    
    if (isOpX<EQ>(term)) return mk<AND>(
                  mk<GEQ>(term->left(), term->right()),
                  mk<GEQ>(term->right(), term->left()));
    
    if (isOpX<NEQ>(term)) return mk<OR>(
                  mk<GT>(term->left(), term->right()),
                  mk<GT>(term->right(), term->left()));
    
    if (isOpX<NEG>(term))
    {
      return mk<NEG>(convertToGEandGT(term->last()));
    }
    
    if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(convertToGEandGT(term->arg(i)));
      }
      
      return isOpX<AND>(term) ? conjoin (args, term->getFactory()) :
                  disjoin (args, term->getFactory());
      
    }
    return term;
  }
  
  /**
   * To rem
   */
  inline bool containsOnlyOf(Expr a, Expr b)
  {
    ExprVector av;
    filter (a, bind::IsConst (), back_inserter (av));
    if (av.size() == 1) if (av[0] == b) return true;
    
    return false;
  }
  
  inline static Expr simplifiedAnd (Expr a, Expr b){
    ExprSet conjs;
    getConj(a, conjs);
    getConj(b, conjs);
    return
    (conjs.size() == 0) ? mk<TRUE>(a->getFactory()) :
    (conjs.size() == 1) ? *conjs.begin() :
    mknary<AND>(conjs);
  }
  
  
  inline int intersectSize(ExprVector& a, ExprVector& b){
    ExprSet c;
    for (auto &var: a)
      if (find(b.begin(), b.end(), var) != b.end()) c.insert(var);
    return c.size();
  }
  
  inline static void productAnd (ExprSet& as, ExprSet& bs, ExprSet& ps)
  {
    for (auto &a : as)
    {
      for (auto &b : bs)
      {
        ps.insert(mk<OR>(a, b));
      }
    }
  }
  
  // ab \/ cde \/ f =>
  //                    (a \/ c \/ f) /\ (a \/ d \/ f) /\ (a \/ e \/ f) /\
  //                    (b \/ c \/ f) /\ (b \/ d \/ f) /\ (b \/ e \/ f)
  inline static Expr rewriteOrAnd(Expr exp)
  {
    ExprSet disjs;
    getDisj(exp, disjs);
    if (disjs.size() == 1) return exp;
    
    vector<ExprSet> dconjs;
    for (auto &a : disjs)
    {
      ExprSet conjs;
      getConj(a, conjs);
      dconjs.push_back(conjs);
    }
    
    ExprSet older;
    productAnd(dconjs[0], dconjs[1], older);
    
    ExprSet newer = older;
    for (int i = 2; i < disjs.size(); i++)
    {
      newer.clear();
      productAnd(dconjs[i], older, newer);
      older = newer;
    }
    
    return conjoin (newer, exp->getFactory());
  }
  
  // not very pretty method, but..
  inline static Expr reBuildCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term))
    {
      return mk<LEQ>(lhs, rhs);
    }
    if (isOpX<GEQ>(term))
    {
      return mk<GEQ>(lhs, rhs);
    }
    if (isOpX<LT>(term))
    {
      return mk<LT>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<GT>(lhs, rhs);
  }
  
  inline static Expr reBuildNegCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term))
    {
      return mk<GT>(lhs, rhs);
    }
    if (isOpX<GEQ>(term))
    {
      return mk<LT>(lhs, rhs);
    }
    if (isOpX<LT>(term))
    {
      return mk<GEQ>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<LEQ>(lhs, rhs);
  }
  
  // not very pretty method, but..
  inline static bool evaluateCmpConsts(Expr term, int a, int b)
  {
    if (isOpX<EQ>(term))
    {
      return (a == b);
    }
    if (isOpX<NEQ>(term))
    {
      return (a != b);
    }
    if (isOpX<LEQ>(term))
    {
      return (a <= b);
    }
    if (isOpX<GEQ>(term))
    {
      return (a >= b);
    }
    if (isOpX<LT>(term))
    {
      return (a < b);
    }
    assert(isOpX<GT>(term));
    return (a > b);
  }
  
  inline static Expr mkNeg(Expr term)
  {
    if (isOpX<NEG>(term))
    {
      return term->arg(0);
    }
    else if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(mkNeg(term->arg(i)));
      }
      return isOpX<AND>(term) ? disjoin(args, term->getFactory()) :
                                conjoin (args, term->getFactory());
    }
    else if (isOp<ComparissonOp>(term))
    {
      return reBuildNegCmp(term, term->arg(0), term->arg(1));
    }
    return mk<NEG>(term);
  }
  
  inline static Expr unfoldITE(Expr term)
  {
    if (isOpX<ITE>(term))
    {
      Expr iteCond = unfoldITE (term->arg(0));
      Expr iteC1 = unfoldITE (term->arg(1));
      Expr iteC2 = unfoldITE (term->arg(2));
      
      return mk<OR>( mk<AND>(iteCond, iteC1),
                    mk<AND>(mkNeg(iteCond), iteC2));
    }
    else if (isOpX<NEG>(term))
    {
      return mk<NEG>(unfoldITE(term->last()));
    }
    else if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(unfoldITE(term->arg(i)));
      }
      return isOpX<AND>(term) ? conjoin (args, term->getFactory()) :
                                disjoin (args, term->getFactory());
    }
    else if (isOp<ComparissonOp>(term))
    {
      Expr lhs = term->arg(0);
      Expr rhs = term->arg(1);
      
      if (isOpX<ITE>(rhs))
      {
        
        Expr iteCond = unfoldITE (rhs->arg(0));
        Expr iteC1 = rhs->arg(1);
        Expr iteC2 = rhs->arg(2);
        
        Expr newCmp1 = unfoldITE (reBuildCmp(term, lhs, iteC1));
        Expr newCmp2 = unfoldITE (reBuildCmp(term, lhs, iteC2));
        
        Expr transformed = mk<OR>( mk<AND>(iteCond, newCmp1),
                                  mk<AND>(mkNeg(iteCond), newCmp2));
        
        //          outs () << "     [1b] ---> " << *term << "\n";
        //          outs () << "     [1e] ---> " << *transformed << "\n\n";
        return transformed;
        
      }
      else if (isOpX<ITE>(lhs))
      {
        // GF: symmetric case to the one above
        
        Expr iteCond = unfoldITE (lhs->arg(0));
        Expr iteC1 = lhs->arg(1);
        Expr iteC2 = lhs->arg(2);
        
        Expr newCmp1 = unfoldITE (reBuildCmp(term, iteC1, rhs));
        Expr newCmp2 = unfoldITE (reBuildCmp(term, iteC2, rhs));
        
        Expr transformed = mk<OR>( mk<AND>(iteCond, newCmp1),
                                  mk<AND>(mkNeg(iteCond), newCmp2));
        
        //          outs () << "    [2b] ---> " << *term << "\n";
        //          outs () << "    [2e] ---> " << *transformed << "\n\n";
        return transformed;
      }
      else if (isOpX<PLUS>(rhs))
      {
        bool found = false;
        Expr iteArg;
        ExprVector newArgs;
        for (auto it = rhs->args_begin(), end = rhs->args_end(); it != end; ++it)
        {
          // make sure that only one ITE is found
          
          if (!found && isOpX<ITE>(*it))
          {
            found = true;
            iteArg = *it;
          }
          else
          {
            newArgs.push_back(*it);
          }
        }
        if (found)
        {
          Expr iteCond = unfoldITE (iteArg->arg(0));
          Expr iteC1 = iteArg->arg(1);
          Expr iteC2 = iteArg->arg(2);
          
          newArgs.push_back(iteC1);
          Expr e1 = unfoldITE (reBuildCmp(term, lhs, mknary<PLUS>(newArgs))); // GF: "unfoldITE" gives error...
          
          newArgs.pop_back();
          newArgs.push_back(iteC2);
          Expr e2 = unfoldITE (reBuildCmp(term, lhs, mknary<PLUS>(newArgs)));
          
          Expr transformed = mk<OR>(mk<AND>(iteCond, e1),
                                    mk<AND>(mkNeg(iteCond),e2));
          
          //            outs () << "    [3b] ---> " << *term << "\n";
          //            outs () << "    [3e] ---> " << *transformed << "\n\n";
          
          return transformed;
        }
      }
      else if (isOpX<PLUS>(lhs))
      {
        // symmetric to the above case
        bool found = false;
        Expr iteArg;
        ExprVector newArgs;
        for (auto it = lhs->args_begin(), end = lhs->args_end(); it != end; ++it)
        {
          if (!found && isOpX<ITE>(*it))
          {
            found = true;
            iteArg = *it;
          }
          else
          {
            newArgs.push_back(*it);
          }
        }
        
        if (found)
        {
          Expr iteCond = unfoldITE (iteArg->arg(0));
          Expr iteC1 = iteArg->arg(1);
          Expr iteC2 = iteArg->arg(2);
          
          newArgs.push_back(iteC1);
          Expr e1 = unfoldITE (reBuildCmp(term, mknary<PLUS>(newArgs), rhs));
          
          newArgs.pop_back();
          newArgs.push_back(iteC2);
          Expr e2 = unfoldITE (reBuildCmp(term, mknary<PLUS>(newArgs), rhs));
          
          Expr transformed = mk<OR>(mk<AND>(iteCond,e1),
                                    mk<AND>(mkNeg(iteCond),e2));
          
          //            outs () << "    [4b] ---> " << *term << "\n";
          //            outs () << "    [4e] ---> " << *transformed << "\n\n";
          
          return transformed;
        }
      }
    }
    
    return term;
  }
  
  // very simple check if tautology (SMT-based check is expensive)
  inline static bool isTautology(Expr term)
  {
    if (isOpX<EQ>(term))
      if (term->arg(0) == term->arg(1)) return true;
    
    if (isOp<ComparissonOp>(term))
      if (isNumericConst(term->arg(0)) && isNumericConst(term->arg(1)))
        return evaluateCmpConsts(term,
                                 lexical_cast<int>(term->arg(0)), lexical_cast<int>(term->arg(1)));
    
    ExprSet cnjs;
    getConj(term, cnjs);
    if (cnjs.size() < 2) return false;
    
    bool res = true;
    for (auto &a : cnjs) res &= isTautology(a);
    
    return res;
  }
  
  inline static Expr normalizeAtom(Expr term, ExprVector& intVars)
  {
    if (isOp<ComparissonOp>(term))
    {
      Expr lhs = term->left();
      Expr rhs = term->right();
      
      ExprVector all;
      ExprVector allrhs;
      
      getAddTerm(lhs, all);
      getAddTerm(rhs, allrhs);
      for (auto & a : allrhs)
      {
        all.push_back(arithmInverse(a));
      }
      
      ExprSet newlhs;
      
      for (auto &v : intVars)
      {
        int coef = 0;
        for (auto it = all.begin(); it != all.end();)
        {
          if(v == *it)
          {
            coef++;
            it = all.erase(it);
          }
          else if (isOpX<UN_MINUS>(*it) && (*it)->left() == v)
          {
            coef--;
            it = all.erase(it);
          }
          else if (isOpX<MULT>(*it) && (*it)->right() == v)
          {
            coef += lexical_cast<int>((*it)->left());
            it = all.erase(it);
          }
          else
          {
            ++it;
          }
        }
        if (coef != 0) newlhs.insert(mk<MULT>(mkTerm (mpz_class (coef), term->getFactory()), v));
      }
      
      bool success = true;
      int intconst = 0;
      
      for (auto &e : all)
      {
        if (isNumericConst(e))
        {
          intconst += lexical_cast<int>(e);
        }
        else
        {
          success = false;
        }
      }
      
      if (success && newlhs.size() == 0)
      {
        return (evaluateCmpConsts(term, 0, -intconst)) ? mk<TRUE>(term->getFactory()) :
                                                         mk<FALSE>(term->getFactory());
      }
      
      if (success)
      {
        Expr pl = (newlhs.size() == 1) ? *newlhs.begin(): mknary<PLUS>(newlhs);
        Expr c = mkTerm (mpz_class (-intconst), term->getFactory());
        return reBuildCmp(term, pl, c);
      }
      
    }
    return term;
  }
  
  inline static Expr normalizeDisj(Expr exp, ExprVector& intVars)
  {
    ExprSet disjs;
    ExprSet newDisjs;
    getDisj(exp, disjs);
    for (auto &d : disjs)
    {
      Expr norm = normalizeAtom(d, intVars);
      if ( isOpX<TRUE> (norm)) return norm;
      if (!isOpX<FALSE>(norm)) newDisjs.insert(norm);
    }
    return disjoin(newDisjs, exp->getFactory());
  }
  
  inline static void getLinCombCoefs(Expr ex, set<int>& intCoefs)
  {
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        getLinCombCoefs(*it, intCoefs);
      }
      else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
      {
        Expr lhs = ex->left();
        if (isOpX<PLUS>(lhs))
        {
          for (auto it = lhs->args_begin (), end = lhs->args_end (); it != end; ++it)
          {
            if (isOpX<MULT>(*it))           // else, it is 1, and we will add it anyway;
            {
              intCoefs.insert(lexical_cast<int> ((*it)->left()));
            }
          }
        }
        else
        {
          if (isOpX<MULT>(lhs))
          {
            intCoefs.insert(lexical_cast<int> (lhs->left()));
          }
        }
      }
    }

  inline static void getLinCombConsts(Expr ex, set<int>& intConsts)
  {
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        getLinCombConsts(*it, intConsts);
      }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      intConsts.insert(lexical_cast<int> (ex->right()));
    }
  }
}

#endif
