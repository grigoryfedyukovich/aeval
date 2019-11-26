#ifndef EXPRSIMPL__HPP__
#define EXPRSIMPL__HPP__
#include <assert.h>

#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{

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

  template<typename Range> static Expr mkmult(Range& terms, ExprFactory &efac){
    return
      (terms.size() == 0) ? mkTerm (mpz_class (1), efac) :
      (terms.size() == 1) ? *terms.begin() :
      mknary<MULT>(terms);
  }

  template<typename Range1, typename Range2> static bool emptyIntersect(Range1& av, Range2& bv){
    for (auto &var1: av){
      for (auto &var2: bv) if (var1 == var2) return false;
    }
    return true;
  }

  template<typename Range> static bool emptyIntersect(Expr a, Range& bv){
    ExprVector av;
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    return emptyIntersect(av, bv);
  }

  inline static bool emptyIntersect(Expr a, Expr b){
    ExprVector bv;
    filter (b, bind::IsConst (), inserter(bv, bv.begin()));
    return emptyIntersect(a, bv);
  }

  inline static bool hasExtraVars(Expr a, ExprVector& b)
  {
    ExprVector av;
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    for (auto & v : av) if (find(b.begin(), b.end(), v) == b.end()) return true;
    return false;
  }

  inline static bool hasExtraVars(Expr a, Expr b)
  {
    ExprVector bv;
    filter (b, bind::IsConst (), inserter(bv, bv.begin()));
    return hasExtraVars(a, bv);
  }

  // if at the end disjs is empty, then a == true
  inline static void getConj (Expr a, ExprSet &conjs)
  {
    if (isOpX<TRUE>(a)) return;
    if (isOpX<FALSE>(a)){
      conjs.clear();
      conjs.insert(a);
      return;
    } else if (isOpX<AND>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getConj(a->arg(i), conjs);
      }
    } else {
      conjs.insert(a);
    }
  }

  // if at the end disjs is empty, then a == false
  inline static void getDisj (Expr a, ExprSet &disjs)
  {
    if (isOpX<FALSE>(a)) return;
    if (isOpX<TRUE>(a)){
      disjs.clear();
      disjs.insert(a);
      return;
    } else if (isOpX<OR>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getDisj(a->arg(i), disjs);
      }
    } else {
      disjs.insert(a);
    }
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

  /**
   * Represent Expr as multiplication
   */
  inline static Expr mult(Expr e){
    if (isOpX<MULT>(e)){
      return e;
    } else {
      return mk<MULT>(mkTerm (mpz_class (1), e->getFactory()), e);
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

  inline static void getMultOps (Expr a, ExprVector &ops)
  {
    if (isOpX<MULT>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getMultOps(a->arg(i), ops);
      }
    } else {
      ops.push_back(a);
    }
  }

  static void getAddTerm (Expr a, ExprVector &terms); // declaration only

  inline static Expr arithmInverse(Expr e)
  {
    bool success = true;
    if (isOpX<MULT>(e))
    {
      int coef = 1;
      ExprVector ops;
      getMultOps (e, ops);

      Expr var = NULL;
      for (auto & a : ops)
      {
        if (isOpX<MPZ>(a))
        {
          coef *= lexical_cast<int>(a);
        }
        else if (bind::isIntConst(a) && var == NULL)
        {
          var = a;
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
    else if (isOpX<MPZ>(e))
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
      ++it;
      for (; it != end; ++it)
      {
        getAddTerm(arithmInverse(*it), terms);
      }
    }
    else if (isOpX<UN_MINUS>(a))
    {
      getAddTerm(arithmInverse(a->left()), terms);
    }
    else
    {
      terms.push_back(a);
    }
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
  inline static bool isConstOrItsAdditiveInverse(Expr e, Expr var){
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
    if (isOpX<UN_MINUS>(e)){
      return e->left();
    }
    else if (isOpX<MPQ>(e)){
      string val = lexical_cast<string>(e);
      int delim = val.find("/");
      int val1 = stoi(val.substr(0, delim));
      int val2 = stoi(val.substr(delim + 1));
      if (delim < 0) {
        return mkTerm (mpq_class (-val1), e->getFactory());
      } else {
        string inv_val = to_string(-val1) + "/" + to_string(val2);
        return mkTerm (mpq_class (inv_val), e->getFactory());
      }
    }
    else if (isOpX<MPZ>(e)){
      int val = lexical_cast<int>(e);
      return mkTerm (mpz_class (-val), e->getFactory());
    }
    else if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1"){
        return e->right();
      } else if (e->arity() == 2) {
        Expr c = additiveInverse(e->left());
        return mk<MULT>(c, e->right());
      }
    }
    else if (bind::isIntConst(e))
      return mk<MULT>(mkTerm (mpz_class (-1), e->getFactory()), e);

    else if (isOpX<PLUS>(e) || isOpX<MINUS>(e))
    {
      ExprVector all;
      getAddTerm(e, all);
      ExprVector negged;
      for (auto & a : all) negged.push_back(additiveInverse(a));
      return mkplus(negged, e->getFactory());
    }
    return mk<MULT>(mkTerm (mpq_class (-1), e->getFactory()), e);
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
    if (!isOpX<UN_MINUS>(e->left()) &&
        !(isOpX<MULT>(e->left()) &&
          lexical_cast<string>(e->left()->left()) == "-1") ) return e;

    return mk<T>(additiveInverse(e->left()), additiveInverse(exprDistributor(e->right())));
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
        if (isConstOrItsAdditiveInverse(a, var)){
          lhs = a;
          continue;
        }
        rhs.insert(additiveInverse(a));
      }
    } else if (isOpX<MINUS>(l)){
      if (isConstOrItsAdditiveInverse(l->left(), var)){
        lhs = l->left();
        rhs.insert(additiveInverse(l->right()));
      } else if (isConstOrItsAdditiveInverse(l->right(), var)){
        lhs = l->right();
        rhs.insert(additiveInverse(l->left()));
      }
    } else {
      if (isConstOrItsAdditiveInverse(l, var)){
        lhs = l;
      } else if (lexical_cast<string>(l) != "0"){
        rhs.insert(additiveInverse(l));
      }
    }
    
    // second, parse r;
    
    if (isOpX<PLUS>(r)){
      for (unsigned i = 0; i < r->arity (); i++){
        Expr a = r->arg(i);
        if (isConstOrItsAdditiveInverse(a, var)){
          lhs = additiveInverse(a);
          continue;
        }
        rhs.insert(a);
      }
    } else {
      if (isConstOrItsAdditiveInverse(r, var)){
        lhs = additiveInverse(r);
      } else if (lexical_cast<string>(r) != "0"){
        rhs.insert(r);
      }
    }
    
    // third, combine results;
    
    if (lhs != 0){
      return mk<T>(lhs, mkplus(rhs, var->getFactory()));
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
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperN<NEQ>(e);
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
      } else if (isOpX<NEQ>(e)){
        return mk<EQ>(e->arg(0), e->arg(1));
      } else if (isOpX<EQ>(e)){
        return mk<NEQ>(e->arg(0), e->arg(1));
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
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperM<NEQ>(e, var);
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

  /**
   * Simplifier Wrapper
   */
  inline static Expr ineqSimplifier(Expr v, Expr exp){
    ExprSet conjs;
    getConj(exp, conjs);
    ExprSet substsMap;
    for (auto cl : conjs)
    {
      cl = ineqNegReverter(cl);
      cl = exprMover(cl, v);
      cl = ineqMover(cl, v);
      cl = ineqReverter (cl);
      substsMap.insert(cl);
    }

    ineqMerger(substsMap);
    equalitySearch(substsMap, v);
    return conjoin(substsMap, v->getFactory());
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
    bool f = false;
    
    for (ENode::args_iterator it = exp->args_begin(),
         end = exp->args_end(); it != end; ++it){
      if (*it == to_skip) f = true;
      else args.push_back (*it);
    }

    if (f == false)
    {
      args.push_back(additiveInverse(to_skip));
    }
    
    if (args.size() == 1) {
      ret = args[0];
    }
    
    else if (args.size() == 2){
      if (isOpX<UN_MINUS>(args[0]) && !isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[1], args[0]->left());
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
        return simplifiedPlus(a, b);
      } else
        
        if (isOpX<PLUS>(b)){
          Expr res = simplifiedPlus(b, a);
          return mk<UN_MINUS>(res);
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
                  ret = mk<PLUS>(a, mkTerm (mpz_class (1), a->getFactory()));
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

  static Expr simplifyBool (Expr exp);

  struct SimplifyBoolExpr
  {
    ExprFactory &efac;
    
    SimplifyBoolExpr (ExprFactory& _efac) : efac(_efac){};
    
    Expr operator() (Expr exp)
    {
      // GF: to enhance
      
      if (isOpX<IMPL>(exp))
      {
        Expr lhs = simplifyBool(exp->left());
        Expr rhs = simplifyBool(exp->right());
        if (isOpX<TRUE>(rhs)) return mk<TRUE>(efac);
        if (isOpX<FALSE>(rhs)) return mkNeg(lhs);
        if (isOpX<TRUE>(lhs)) return rhs;

        return mk<IMPL>(lhs, rhs);
      }
      
      if (isOpX<OR>(exp)){
        ExprSet dsjs;
        ExprSet newDsjs;
        getConj(exp, dsjs);
        for (auto & d : dsjs)
        {
          if (isOpX<TRUE>(d)) return mk<TRUE>(efac);
          if (isOpX<EQ>(d) && d->left() == d->right()) return mk<TRUE>(efac);
          if (!isOpX<FALSE>(d)) newDsjs.insert(d);
        }
        return disjoin(newDsjs, efac);
      }
      
      if (isOpX<AND>(exp)){
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(exp, cnjs);
        for (auto & c : cnjs)
        {
          if (isOpX<FALSE>(c)) return mk<FALSE>(efac);
          if (!isOpX<TRUE>(c)) newCnjs.insert(c);
        }
        return conjoin(newCnjs, efac);
      }

      if (isOpX<EQ>(exp) && exp->left() == exp->right()) {
        return mk<TRUE>(efac);
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
    (conjs.size() == 1) ? *(conjs.begin()) :
    mknary<AND>(conjs);
  }
  
  
  inline int intersectSize(ExprVector& a, ExprVector& b){
    ExprSet c;
    for (auto &var: a)
      if (find(b.begin(), b.end(), var) != b.end()) c.insert(var);
    return c.size();
  }

  // not very pretty method, but..
  inline static Expr reBuildCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term)){
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term)){
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term)){
      return mk<LEQ>(lhs, rhs);
    }
    if (isOpX<GEQ>(term)){
      return mk<GEQ>(lhs, rhs);
    }
    if (isOpX<LT>(term)){
      return mk<LT>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<GT>(lhs, rhs);
  }

  inline static Expr simplIneqMover(Expr exp)
  {
    exp = ineqNegReverter(exp);
    if (lexical_cast<string>(exp->right()) == "0") return exp;

    // GF: find a better way how to move things
    exp = reBuildCmp(exp, simplifiedMinus(exp->left(), exp->right()),
                     mkTerm (mpz_class (0), exp->getFactory()));
    return exp;
  }

  struct EqMiner : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& eqs;
    Expr& var;

    EqMiner (Expr& _var, ExprSet& _eqs): var(_var), eqs(_eqs) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<EQ>(exp) && (exp->left() == var || exp->right() == var))
      {
        eqs.insert(exp);
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline void getEqualities (Expr exp, Expr var, ExprSet& eqs)
  {
    EqMiner trm (var, eqs);
    dagVisit (trm, exp);
  }

  struct QFregularizer
  {
    ExprVector& vars;

    QFregularizer (ExprVector& _vars): vars(_vars){};

    Expr operator() (Expr exp)
    {
      if (bind::isBVar(exp))
      {
        return vars[vars.size() - bind::bvarId(exp) - 1];
      }
      return exp;
    }
  };

  inline static Expr regularizeQF (Expr exp)
  {
    if (!isOpX<FORALL>(exp)) return exp;
    ExprVector vars;
    for (int i = 0; i < exp->arity() - 1; i++)
    {
      vars.push_back(bind::fapp(exp->arg(i)));
    }
    RW<QFregularizer> rw(new QFregularizer(vars));
    return dagVisit (rw, exp);
  }

  inline static bool findMatching(Expr pattern, Expr exp, ExprVector& vars, ExprMap& matching)
  {
    if (pattern == exp && (isOpX<FDECL>(pattern) || isOpX<MPZ>(pattern)))  return true;

    if (bind::typeOf(pattern) != bind::typeOf(exp)) return false;

    if (pattern->arity() == 1 && find(vars.begin(), vars.end(), pattern) != vars.end())
    {
      if (matching[pattern] != NULL && matching[pattern] != exp) return false;
      else
      {
        matching[pattern] = exp;
        return true;
      }
    }

    if ((isOpX<EQ>(exp) && isOpX<EQ>(pattern)) ||
        (isOpX<LEQ>(exp) && isOpX<LEQ>(pattern)) ||
        (isOpX<GEQ>(exp) && isOpX<GEQ>(pattern)) ||
        (isOpX<LT>(exp) && isOpX<LT>(pattern)) ||
        (isOpX<GT>(exp) && isOpX<GT>(pattern)) ||
        (isOpX<STORE>(exp) && isOpX<STORE>(pattern)) ||
        (isOpX<FAPP>(exp) && isOpX<FAPP>(pattern) &&
          pattern->left() == exp->left()))
    {
      for (int i = 0; i < pattern->arity(); i++)
      {
        if (!findMatching(pattern->arg(i), exp->arg(i), vars, matching))
          return false;
      }
      return true;
    }
    return false;
  }

  struct SubexprMatcher : public std::unary_function<Expr, VisitAction>
  {
    bool found;
    ExprVector& vars;
    ExprMap& matching;
    Expr pattern;
    SubexprMatcher (Expr _p, ExprVector& _v, ExprMap& _m) :
      found (false), pattern(_p), vars(_v), matching(_m) {}

    VisitAction operator() (Expr exp)
    {
      if (found)
      {
        return VisitAction::skipKids ();
      }
      else if ((isOpX<FAPP>(exp) || isOp<ComparissonOp>(exp)) &&
          findMatching (pattern, exp, vars, matching))
      {
        found = true;
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline bool findMatchingSubexpr (Expr pattern, Expr exp, ExprVector& vars, ExprMap& matching)
  {
    SubexprMatcher fn (pattern, vars, matching);
    dagVisit (fn, exp);
    return fn.found;
  }

  struct ITElifter
  {
    ITElifter () {};

    Expr operator() (Expr exp)
    {
      // currently, can lift only one ITE
      if (isOpX<FAPP>(exp))
      {
        ExprVector vars1;
        ExprVector vars2;
        Expr cond = NULL;
        vars1.push_back(exp->arg(0));
        vars2.push_back(exp->arg(0));
        for (int i = 1; i < exp->arity(); i++)
        {
          if (isOpX<ITE>(exp->arg(i)) && cond == NULL)
          {
            cond = exp->arg(i)->arg(0);
            vars1.push_back(exp->arg(i)->arg(1));
            vars2.push_back(exp->arg(i)->arg(2));
          }
          else
          {
            vars1.push_back(exp->arg(i));
            vars2.push_back(exp->arg(i));
          }
        }
        if (cond == NULL) return exp;
        return mk<ITE>(cond, mknary<FAPP>(vars1), mknary<FAPP>(vars2));
      }
      return exp;
    }
  };

  inline static Expr liftITEs (Expr exp)
  {
    RW<ITElifter> rw(new ITElifter());
    return dagVisit (rw, exp);
  }

  struct SelectStoreRewriter
  {
    SelectStoreRewriter () {};

    ExprSet unusedSelects;

    Expr operator() (Expr exp)
    {
      if (isOpX<SELECT>(exp) && isOpX<STORE>(exp->left()))
      {
        if (exp->right() == exp->left()->right())
          return exp->left()->last();
        else
          return mk<ITE>(mk<EQ>(exp->right(), exp->left()->right()),
             exp->left()->last(), mk<SELECT>(exp->left()->left(), exp->right()));
      }
      else if (isOpX<EQ>(exp))
      {
        Expr exprStore;
        Expr exprArr;
        if (isOpX<STORE>(exp->left()))
        {
          exprStore = exp->left();
          exprArr = exp->right();
        }
        else if (isOpX<STORE>(exp->right()))
        {
          exprStore = exp->right();
          exprArr = exp->left();
        }

        if (exprStore != NULL && exprArr != NULL)
        {
          ExprSet all;
          all.insert(mk<EQ>(exprStore->last(), mk<SELECT>(exprArr, exprStore->right())));
          ExprSet nested;
          for (auto rit = unusedSelects.rbegin(); rit != unusedSelects.rend(); ++rit)
          {
            Expr a = *rit;
            Expr elem = a->right();
            if (contains(exprStore, a) && exprStore != a &&
                find(nested.begin(), nested.end(), elem) == nested.end())
            {
              nested.insert(elem); // to avoid over-writing cells
              all.insert(mk<EQ>(a->last(), mk<SELECT>(exprArr, elem)));
            }
          }
          return conjoin(all, exp->getFactory());
        }
      }
      else if (isOpX<STORE>(exp))
      {
        unusedSelects.insert(exp);
      }
      return exp;
    }
  };

  inline static Expr rewriteSelectStore(Expr exp)
  {
    RW<SelectStoreRewriter> a(new SelectStoreRewriter());
    return dagVisit (a, exp);
  }

  inline static void getCounters (Expr a, ExprSet &cntrs)
  {
    if (isOpX<SELECT>(a) || isOpX<STORE>(a)){
      cntrs.insert(a->right());
      if (isOpX<STORE>(a))
        getCounters(a->left(), cntrs);
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getCounters(a->arg(i), cntrs);
    }
  }

  inline static bool isNumeric(Expr a)
  {
    // don't consider ITE-s
    return (isOp<NumericOp>(a) || isOpX<MPZ>(a) ||
            isOpX<MPQ>(a) || bind::isIntConst(a) || isOpX<SELECT>(a));
  }

  inline static void mutateHeuristic (Expr exp, ExprSet& guesses /*, int bnd = 100*/)
  {
    // to extend, if needed
    ExprSet cnjs;
    getConj(exp, cnjs);
    for (auto c : cnjs)
    {
      if (isOpX<NEG>(c)) c = mkNeg(c->left());

      if (isOpX<EQ>(c))
      {
        if (isNumeric(c->left()))
        {
          guesses.insert(mk<LEQ>(c->right(), c->left()));
          guesses.insert(mk<LEQ>(c->left(), c->right()));
        }
        else
        {
          guesses.insert(c);
        }
      }
    }
  }

  inline static Expr normalizeTerm(Expr term)
  {
    ExprVector intVars;
    filter (term, bind::IsConst (), inserter(intVars, intVars.begin()));
    ExprVector all;
    getAddTerm(term, all);
    ExprSet newtermPos;
    ExprSet newtermNeg;
    for (auto &v : intVars)
    {
      int coef = 0;
      string s1 = lexical_cast<string>(v);
      for (auto it = all.begin(); it != all.end();)
      {
        string s2 = lexical_cast<string>(*it);

        if (s1 == s2)
        {
          coef++;
          it = all.erase(it);
        }
        else if (isOpX<UN_MINUS>(*it))
        {
          string s3 = lexical_cast<string>((*it)->left());
          if (s1 == s3)
          {
            coef--;
            it = all.erase(it);
          }
          else
          {
            ++it;
          }
        }
        else if (isOpX<MULT>(*it))
        {
          ExprVector ops;
          getMultOps (*it, ops);

          int c = 1;
          bool success = true;
          for (auto & a : ops)
          {
            if (s1 == lexical_cast<string>(a))
            {
              // all good!
            }
            else if (isOpX<MPZ>(a))
            {
              c = c * lexical_cast<int>(a);
            }
            else
            {
              ++it;
              success = false;
              break;
            }
          }
          if (success)
          {
            coef += c;
            it = all.erase(it);
          }
        }
        else
        {
          ++it;
        }
      }
      if (coef == 1)
        newtermPos.insert(v);
      else if (coef > 0)
        newtermPos.insert(mk<MULT>(mkTerm (mpz_class (coef), term->getFactory()), v));
      else if (coef == -1)
        newtermNeg.insert(v);
      else if (coef < 0)
        newtermNeg.insert(mk<MULT>(mkTerm (mpz_class (-coef), term->getFactory()), v));
    }

    bool success = true;
    int intconst = 0;

    for (auto &e : all)
    {
      if (isOpX<MPZ>(e))
      {
        intconst += lexical_cast<int>(e);
      }
      else if (isOpX<MULT>(e))
      {
        // GF: sometimes it fails (no idea why)
        int thisTerm = 1;
        for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
        {
          if (isOpX<MPZ>(*it))
            thisTerm *= lexical_cast<int>(*it);
          else
            success = false;
        }
        intconst += thisTerm;
      }
      else
      {
        success = false;
      }
    }
    if (intconst > 0)
      newtermPos.insert(mkTerm (mpz_class (intconst), term->getFactory()));
    else if (intconst < 0)
      newtermNeg.insert(mkTerm (mpz_class (-intconst), term->getFactory()));

    for (auto & a : newtermNeg)
      newtermPos.insert(arithmInverse(a));
//    if (newtermNeg.empty())
      return mkplus(newtermPos, term->getFactory());
//    else
//      return mk<MINUS>(mkplus(newtermPos, term->getFactory()),
//                       mkplus(newtermNeg, term->getFactory()));
  }

  struct NormalizeArithmExpr
  {
    ExprFactory &efac;

    NormalizeArithmExpr (ExprFactory& _efac):
    efac(_efac){};

    Expr operator() (Expr e)
    {
      if (isOpX<PLUS>(e) || isOpX<MINUS>(e) || isOpX<MULT>(e))
        return normalizeTerm(e);
      if (isOp<ComparissonOp>(e) && isNumeric(e->left())) {
        return reBuildCmp(e,
          normalizeTerm(mk<PLUS>(e->left(), arithmInverse(e->right()))),
            mkTerm (mpz_class (0), efac));
      }
      return e;
    }
  };

  inline static Expr normalizeArithm (Expr exp)
  {
    RW<NormalizeArithmExpr> rw(new NormalizeArithmExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }

  Expr normalizeImplHlp (Expr e, ExprSet& lhs)
  {
    if (isOpX<IMPL>(e))
    {
      lhs.insert(e->left());
      return normalizeImplHlp(e->right(), lhs);
    }
    return e;
  }

  Expr normalizeImpl (Expr e)
  {
    ExprSet lhs;
    Expr rhs = normalizeImplHlp(e, lhs);
    if (lhs.empty()) return e;
    return (mk<IMPL>(conjoin(lhs, e->getFactory()), rhs));
  }

  Expr createQuantifiedFormula(Expr def, ExprVector& toAvoid)
  {
    ExprSet vars;
    ExprVector args;
    filter(def, bind::IsConst (), inserter(vars, vars.begin()));
    for (auto & a : vars)
      if (find(toAvoid.begin(), toAvoid.end(), a->left()) == toAvoid.end()) args.push_back(a->last());
    args.push_back(def);
    return mknary<FORALL>(args);
  }

  Expr swapPlusMinusConst(Expr e)
  {
    ExprVector ops;
    ExprVector newOps;
    getAddTerm(e, ops);
    for (auto & a : ops)
    {
      if (isOpX<MPZ>(a)) newOps.push_back(additiveInverse(a));
      else newOps.push_back(a);
    }
    return mkplus(newOps, e->getFactory());
  }

  bool isConstPos(Expr e)
  {
    ExprVector ops;
    getAddTerm(e, ops);
    int i = 0;
    for (auto & a : ops)
      if (isOpX<MPZ>(a)) i += lexical_cast<int>(a);

    return i>0;
  }
}

#endif
