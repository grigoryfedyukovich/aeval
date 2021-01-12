#ifndef EXPRSIMPL__HPP__
#define EXPRSIMPL__HPP__
#include <assert.h>
#include <boost/multiprecision/cpp_int.hpp>

#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
using namespace boost::multiprecision;

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

  inline static void getCounters (Expr a, ExprVector &cntrs)
  {
    if (isOpX<SELECT>(a) || isOpX<STORE>(a)){
      cntrs.push_back(a->right());
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getCounters(a->arg(i), cntrs);
    }
  }

  template<typename T> static void unique_push_back(T e, vector<T>& v)
  {
    if (find(v.begin(), v.end(), e) == v.end()) v.push_back(e);
  }

  static void uniquePushConj(Expr e, ExprVector& v)
  {
    ExprSet cnjs;
    getConj(e, cnjs);
    for (auto & g : cnjs) unique_push_back(g, v);
  }

  inline static bool isNumeric(Expr a)
  {
    return bind::typeOf(a) == mk<INT_TY>(a->getFactory());
  }

  inline static void findComplexNumerics (Expr a, ExprSet &terms)
  {
    if (bind::isIntConst(a) || isOpX<MPZ>(a)) return;
    if (isNumeric(a))
    {
      bool hasNoNumeric = false;
      for (unsigned i = 0; i < a->arity(); i++)
        if (!isNumeric(a->arg(i))) hasNoNumeric = true;
      if (hasNoNumeric)
      {
        terms.insert(a);
        return;
      }
    }
    for (unsigned i = 0; i < a->arity(); i++)
      findComplexNumerics(a->arg(i), terms);
  }

  inline static void getArrIneqs (Expr a, ExprSet &ineqs)
  {
    if (isOp<ComparissonOp>(a) && containsOp<SELECT>(a)){
      if (isOpX<EQ>(a) && isNumeric(a->left()))
      {
        ineqs.insert(mk<LEQ>(a->left(), a->right()));
        ineqs.insert(mk<GEQ>(a->left(), a->right()));
      }
      else
      {
        ineqs.insert(a);
      }
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getArrIneqs(a->arg(i), ineqs);
    }
  }

  inline static void getMultOps (Expr a, ExprVector &ops)
  {
    if (isOpX<MULT>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getMultOps(a->arg(i), ops);
      }
    } else if (isOpX<UN_MINUS>(a) && isNumeric(a->left())){
      ops.push_back(mkTerm (mpz_class (-1), a->getFactory()));
      ops.push_back(a->left());
    } else {
      ops.push_back(a);
    }
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

  static void getAddTerm (Expr a, ExprVector &terms);

  /**
   * Self explanatory
   */
  inline static Expr additiveInverse(Expr e)
  {
    if (isOpX<MULT>(e))
    {
      cpp_int coef = 1;
      ExprVector ops;
      getMultOps (e, ops);

      ExprVector rem;
      for (auto & a : ops)
      {
        if (isOpX<MPZ>(a))
        {
          coef *= lexical_cast<cpp_int>(a);
        }
        else
        {
          rem.push_back(a);
        }
      }

      Expr num = mkTerm (mpz_class (string (-coef)), e->getFactory());
      if (rem.empty() || coef == 0) return num;

      Expr remTerm = mkmult(rem, e->getFactory());
      if (coef == -1) return remTerm;

      return mk<MULT>(num, remTerm);
    }
    else if (isOpX<PLUS>(e))
    {
      ExprVector terms;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        getAddTerm(additiveInverse(*it), terms);
      }
      return mkplus(terms, e->getFactory());
    }
    else if (isOpX<MINUS>(e))
    {
      ExprVector terms;
      getAddTerm(additiveInverse(*e->args_begin ()), terms);
      auto it = e->args_begin () + 1;
      for (auto end = e->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
      return mkplus(terms, e->getFactory());
    }
    else if (isOpX<UN_MINUS>(e))
    {
      return e->left();
    }
    else if (isOpX<MPZ>(e))
    {
      return mkTerm (mpz_class (string (-lexical_cast<cpp_int>(e))), e->getFactory());
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
//    return mk<MULT>(mkTerm (mpz_class (-1), e->getFactory()), e);
    return mk<UN_MINUS>(e);
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
      res = mkplus(expClauses, e->getFactory());
    }

    if (isOpX<MULT>(e)) {
      if (lexical_cast<string>(e->left())  == "-1"){
        Expr l = e->right();

        if (isOpX<PLUS>(l)) {
          ExprSet expClauses;
          for (auto it = l->args_begin(), end = l->args_end(); it != end; ++it){
            expClauses.insert(additiveInverse(*it));
          }
          res = mkplus(expClauses, e->getFactory());
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
    Expr tmp = additiveInverse(e->left());
    if (isOpX<UN_MINUS>(e->left()))
      return mk<T>(additiveInverse(e->left()), additiveInverse(e->right()));

    if (isOpX<MULT>(tmp))
      if (isOpX<MPZ>(tmp->left()))
        if (lexical_cast<cpp_int>(tmp->left()) > 0)
          return mk<T>(tmp, additiveInverse(e->right()));

    if (bind::isIntConst(tmp) || bind::isRealConst(tmp))
      return mk<T>(tmp, additiveInverse(e->right()));

    return e;
  }

  /**
   *  Helper used in ineqMover
   */
  template <typename T> static Expr rewriteHelperM(Expr e, Expr var){
    Expr l = e->left();
    Expr r = e->right();
    ExprVector orig_lhs, orig_rhs, lhs, rhs;

    // parse

    getAddTerm(l, orig_lhs);
    getAddTerm(r, orig_rhs);
    for (auto & a : orig_lhs)
    {
      if (contains (a, var)) lhs.push_back(a);
      else rhs.push_back(additiveInverse(a));
    }
    for (auto & a : orig_rhs)
    {
      if (contains (a, var)) lhs.push_back(additiveInverse(a));
      else rhs.push_back(a);
    }

    // combine results

    cpp_int coef = 0;
    for (auto it = lhs.begin(); it != lhs.end(); )
    {
      bool found = false;
      if (*it == var) { coef++; found = true; }
      if (isOpX<UN_MINUS>(*it) && (*it)->left() == var) { coef--; found = true; }
      if (isOpX<MULT>(*it) && 2 == (*it)->arity() && isOpX<MPZ>((*it)->left()) && (*it)->right() == var) {
        coef += lexical_cast<cpp_int>((*it)->left());
        found = true;
      }

      if (found) { it = lhs.erase(it); continue; }
      else ++it;
    }

    if (!lhs.empty())
    {
//      errs() << "WARNING: COULD NOT NORMALIZE w.r.t. " << *var << ": "
//             << *conjoin (lhs, e->getFactory()) << "\n";
      return e;
    }

    r = mkplus(rhs, e->getFactory());

    if (coef == 0){
      l = mkTerm (mpz_class (0), e->getFactory());
    } else if (coef == 1){
      l = var;
    } else {
      l = mk<MULT>(mkTerm (mpz_class (string(coef)), e->getFactory()), var);
    }

    return mk<T>(l,r);
  }

  /**
   * Helper used in exprMover
   */
  template <typename T> static Expr rewriteHelperE(Expr e, Expr var){
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
      } else if (isOpX<LT>(e)){
        return rewriteHelperE<GT>(e, var);
      } else if (isOpX<GT>(e)){
        return rewriteHelperE<LT>(e, var);
      } if (isOpX<EQ>(e)){
        return rewriteHelperE<EQ>(e, var);
      } if (isOpX<NEQ>(e)){
        return rewriteHelperE<NEQ>(e, var);
      }
    return e;
  }

  static Expr simplifyArithm (Expr exp, bool keepRedundandDisj, bool keepRedundandConj);

  /**
   * Move var v to LHS of each expression and simplify
   */
  inline static Expr ineqSimplifier(Expr v, Expr exp, bool merge = false){
    ExprSet substsMap;
    if (isOpX<AND>(exp)){
      ExprSet cnjs;
      getConj(exp, cnjs);
      for (Expr cl : cnjs)
        substsMap.insert(ineqSimplifier(v, cl));

      if (merge) ineqMerger(substsMap);
      return conjoin(substsMap, v->getFactory());
    }
    else if (isOp<ComparissonOp>(exp))
    {
      exp = ineqMover(exp, v);
      exp = simplifyArithm(exp, false, false);
      exp = ineqReverter(exp);
    }
    return exp;
  }

  template<typename T> struct RW
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

    // not very pretty method, but..
  inline static Expr reBuildCmp(Expr fla, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(fla))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(fla))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(fla))
    {
      return mk<LEQ>(lhs, rhs);
    }
    if (isOpX<GEQ>(fla))
    {
      return mk<GEQ>(lhs, rhs);
    }
    if (isOpX<LT>(fla))
    {
      return mk<LT>(lhs, rhs);
    }
    assert(isOpX<GT>(fla));
    return mk<GT>(lhs, rhs);
  }

  inline static Expr reBuildCmpSym(Expr fla, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(fla)){
      return mk<EQ>(rhs, lhs);
    }
    if (isOpX<NEQ>(fla)){
      return mk<NEQ>(rhs, lhs);
    }
    if (isOpX<LEQ>(fla)){
      return mk<GEQ>(rhs, lhs);
    }
    if (isOpX<GEQ>(fla)){
      return mk<LEQ>(rhs, lhs);
    }
    if (isOpX<LT>(fla)){
      return mk<GT>(rhs, lhs);
    }
    assert(isOpX<GT>(fla));
    return mk<LT>(rhs, lhs);
  }

  inline static Expr reBuildNegCmp(Expr fla, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(fla))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(fla))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(fla))
    {
      return mk<GT>(lhs, rhs);
    }
    if (isOpX<GEQ>(fla))
    {
      return mk<LT>(lhs, rhs);
    }
    if (isOpX<LT>(fla))
    {
      return mk<GEQ>(lhs, rhs);
    }
    assert(isOpX<GT>(fla));
    return mk<LEQ>(lhs, rhs);
  }

  // not very pretty method, but..
  inline static bool evaluateCmpConsts(Expr fla, cpp_int a, cpp_int b)
  {
    if (isOpX<EQ>(fla))
    {
      return (a == b);
    }
    if (isOpX<NEQ>(fla))
    {
      return (a != b);
    }
    if (isOpX<LEQ>(fla))
    {
      return (a <= b);
    }
    if (isOpX<GEQ>(fla))
    {
      return (a >= b);
    }
    if (isOpX<LT>(fla))
    {
      return (a < b);
    }
    assert(isOpX<GT>(fla));
    return (a > b);
  }

  inline static Expr mkNeg(Expr fla)
  {
    if (isOpX<NEG>(fla))
    {
      return fla->arg(0);
    }
    else if (isOpX<FALSE>(fla))
    {
      return mk<TRUE>(fla->getFactory());
    }
    else if (isOpX<TRUE>(fla))
    {
      return mk<FALSE>(fla->getFactory());
    }
    else if (isOpX<AND>(fla) || isOpX<OR>(fla))
    {
      ExprSet args;
      for (int i = 0; i < fla->arity(); i++){
        args.insert(mkNeg(fla->arg(i)));
      }
      return isOpX<AND>(fla) ?
        disjoin(args, fla->getFactory()) :
        conjoin (args, fla->getFactory());
    }
    else if (isOp<ComparissonOp>(fla))
    {
      return reBuildNegCmp(fla, fla->arg(0), fla->arg(1));
    }
    else if (isOpX<IMPL>(fla))
    {
      return mk<AND>(fla->left(), mkNeg(fla->right()));
    }
    else if (isOpX<FORALL>(fla) || isOpX<EXISTS>(fla))
    {
      ExprVector args;
      for (int i = 0; i < fla->arity() - 1; i++)
        args.push_back(fla->arg(i));
      args.push_back(mkNeg(fla->last()));
      return isOpX<FORALL>(fla) ?
        mknary<EXISTS>(args) : mknary<FORALL>(args);
    }
    return mk<NEG>(fla);
  }

  inline static cpp_int separateConst(ExprVector& plsOps)
  {
    cpp_int c = 0;
    for (auto it = plsOps.begin(); it != plsOps.end(); )
    {
      if (isOpX<MPZ>(*it))
      {
        c += lexical_cast<cpp_int>(*it);
        it = plsOps.erase(it);
        continue;
      }
      else ++it;
    }
    return c;
  }

  inline static Expr simplifyPlus (Expr exp)
  {
    ExprVector plsOps;
    getAddTerm (exp, plsOps);
    cpp_int c = separateConst(plsOps);
    std::sort(plsOps.begin(), plsOps.end(), [](Expr& x, Expr& y) {return x < y;});
    // GF: to write some kind of a fold-operator that counts the numbers of occurences
    if (c != 0) plsOps.push_back(mkTerm (mpz_class (string(c)), exp->getFactory()));
    return mkplus(plsOps, exp->getFactory());
  }

  inline static Expr simplifyMult (Expr e)
  {
    if (isOpX<MULT>(e))
    {
      cpp_int coef = 1;
      ExprVector ops;
      getMultOps (e, ops);

      ExprVector rem;
      for (auto a : ops)
      {
        if (isOpX<MPZ>(a))
          coef *= lexical_cast<cpp_int>(a);
        else
          rem.push_back(a);
      }

      Expr num = mkTerm (mpz_class (string (coef)), e->getFactory());
      if (rem.empty() || coef == 0) return num;

      Expr remTerm = mkmult(rem, e->getFactory());
      if (coef == 1) return remTerm;

      return mk<MULT>(num, remTerm);
    }
    return e;
  }

  inline static Expr simplifyMod (Expr e)
  {
    if (isOpX<MOD>(e) && isOpX<MPZ>(e->right()))
    {
      cpp_int coef = 1;
      cpp_int divider = lexical_cast<cpp_int>(e->right());
      ExprVector ops;
      getMultOps (e->left(), ops);

      for (auto a : ops)
        if (isOpX<MPZ>(a))
          coef *= lexical_cast<cpp_int>(a);

      if (coef % divider == 0)
        return mkTerm (mpz_class (0), e->getFactory());
    }
    return e;
  }

  inline static Expr simplifyIte (Expr exp)  // simple version, on the syntactic level
  {
    ExprFactory &efac = exp->getFactory();
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getAddTerm(exp->right(), plusOpsLeft);
    getAddTerm(exp->last(), plusOpsRight);

    ExprVector commonTerms;
    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      bool found = false;
      for (auto it2 = plusOpsRight.begin(); it2 != plusOpsRight.end(); )
      {
        if (*it1 == *it2)
        {
          if (lexical_cast<string>(*it1) != "0")
            commonTerms.push_back(*it1);
          found = true;
          plusOpsRight.erase(it2);
          break;
        }
        else
        {
          ++it2;
        }
      }
      if (found) it1 = plusOpsLeft.erase(it1);
      else ++it1;
    }

    Expr b1 = simplifyPlus(mkplus(plusOpsLeft, efac));
    Expr b2 = simplifyPlus(mkplus(plusOpsRight, efac));
    if (b1 == b2)
    {
      if (lexical_cast<string>(b1) != "0")
        commonTerms.push_back(b1);
    }
    else
    {
      commonTerms.push_back(mk<ITE>(exp->left(), b1, b2));
    }
    return mkplus(commonTerms, efac);
  }

  inline static Expr simplifyCmp (Expr exp)
  {
    ExprFactory &efac = exp->getFactory();

    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getAddTerm(exp->left(), plusOpsLeft);
    getAddTerm(exp->right(), plusOpsRight);

    cpp_int constLeft = separateConst(plusOpsLeft);
    cpp_int constRight = separateConst(plusOpsRight);

    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      bool found = false;
      for (auto it2 = plusOpsRight.begin(); it2 != plusOpsRight.end(); )
      {
        if (*it1 == *it2)
        {
          found = true;
          plusOpsRight.erase(it2);
          break;
        }
        else
        {
          ++it2;
        }
      }
      if (found) it1 = plusOpsLeft.erase(it1);
      else ++it1;
    }

    // processing of constLeft/Right to prepare for further simplifyArithmDisjunctions/Conjunctions
    if (constLeft != 0 || constRight != 0)
    {
      if (plusOpsLeft.size() == 0)
      {
        constLeft = constLeft - constRight;
        constRight = 0;
      }
      else
      {
        constRight = constRight - constLeft;
        constLeft = 0;
      }
    }

    if (constLeft != 0) plusOpsLeft.push_back(mkTerm (mpz_class (string (constLeft)), efac));
    if (constRight != 0) plusOpsRight.push_back(mkTerm (mpz_class (string (constRight)), efac));

    if (plusOpsLeft.size() == 0 && plusOpsRight.size() == 0)
    {
      if (isOpX<EQ>(exp) || isOpX<GEQ>(exp) || isOpX<LEQ>(exp))
        return mk<TRUE>(efac);
      else
        return mk<FALSE>(efac);
    }

    if (plusOpsLeft.size() == 0 && plusOpsRight.size() == 1 &&
        isOpX<MPZ>(*plusOpsRight.begin()))
    {
      if (evaluateCmpConsts(exp, 0, lexical_cast<cpp_int>(*plusOpsRight.begin())))
        return mk<TRUE>(efac);
      else
        return mk<FALSE>(efac);
    }

    if (plusOpsLeft.size() == 1 && plusOpsRight.size() == 0 &&
        isOpX<MPZ>(*plusOpsLeft.begin()))
    {
      if (evaluateCmpConsts(exp, lexical_cast<cpp_int>(*plusOpsLeft.begin()), 0))
        return mk<TRUE>(efac);
      else
        return mk<FALSE>(efac);
    }

    return reBuildCmp(exp, mkplus(plusOpsLeft, efac), mkplus(plusOpsRight, efac));
  }

  // GF: to rewrite/remove
  inline static Expr simplifiedPlus (Expr exp, Expr to_skip){
    ExprVector args;
    Expr ret;
    bool f = false;

    for (ENode::args_iterator it = exp->args_begin(),
         end = exp->args_end(); it != end; ++it){
      if (*it == to_skip) f = true;
      else args.push_back (*it);
    }

    if (f == false) {
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
    // GF: to rewrite/remove
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

  static Expr simplifyArithmDisjunctions(Expr fla, bool keepRedundandDisj);
  static Expr simplifyArithmConjunctions(Expr fla, bool keepRedundandConj);

  struct SimplifyArithmExpr
  {
    Expr e;
    ExprFactory &efac;
    bool keepRedundandDisj;
    bool keepRedundandConj;

    SimplifyArithmExpr (Expr& _e, bool _d, bool _c) :
      e(_e), efac(_e->getFactory()), keepRedundandDisj(_d), keepRedundandConj(_c) {};

    Expr operator() (Expr exp)
    {
      if (isOpX<PLUS>(exp))
      {
        return simplifyPlus(exp);
      }

      if (isOpX<MINUS>(exp) && exp->arity() == 2)
      {
        return simplifiedMinus(exp->left(), exp->right());
      }

      if (isOpX<MULT>(exp))
      {
        return simplifyMult(exp);
      }

      if (isOpX<MOD>(exp))
      {
        return simplifyMod(exp);
      }

      if (isOpX<UN_MINUS>(exp))
      {
        return additiveInverse(exp->left());
      }

      if (isOpX<MINUS>(exp))
      {
        if (isOpX<UN_MINUS>(exp->right())) return mk<PLUS>(exp->left(), exp->right()->left());
      }

      if (isOp<ComparissonOp>(exp) && isNumeric(exp->right()))
      {
        return simplifyCmp(exp);
      }

      if (isOpX<ITE>(exp) && isNumeric(exp->right()))
      {
        return simplifyIte(exp);
      }

      if (isOpX<OR>(exp))
      {
        return simplifyArithmDisjunctions(exp, keepRedundandDisj && (e == exp));
      }

      if (isOpX<AND>(exp))
      {
        return simplifyArithmConjunctions(exp, keepRedundandConj && (e == exp));
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
        if (isOpX<TRUE>(exp->right()))
          return mk<TRUE>(efac);

        if (isOpX<FALSE>(exp->right()))
          return mkNeg(exp->left());

        if (isOpX<TRUE>(exp->left()))
          return exp->right();

//        return simplifyBool(mk<OR>(
//                 mkNeg(exp->left()),
//                 exp->right()));
      }

      if (isOpX<EQ>(exp))
      {
        if (exp->left() == exp->right())
          return mk<TRUE>(efac);

        if (isOpX<TRUE>(exp->right()))
          return exp->left();

        if (isOpX<TRUE>(exp->left()))
          return exp->right();

        if (isOpX<FALSE>(exp->right()))
          return mkNeg(exp->left());

        if (isOpX<FALSE>(exp->left()))
          return mkNeg(exp->right());
      }

      if (isOpX<NEQ>(exp))
      {
        if (isOpX<FALSE>(exp->right()))
          return exp->left();

        if (isOpX<FALSE>(exp->left()))
          return exp->right();

        if (isOpX<TRUE>(exp->right()))
          return mkNeg(exp->left());

        if (isOpX<TRUE>(exp->left()))
          return mkNeg(exp->right());
      }

      if (isOpX<OR>(exp))
      {
        ExprSet dsjs;
        ExprSet newDsjs;
        getDisj(exp, dsjs);
        for (auto a : dsjs)
        {
          a = simplifyBool(a);
          if (isOpX<TRUE>(a))
          {
            return mk<TRUE>(efac);
          }
          if (isOpX<FALSE>(a))
          {
            continue;
          }
          newDsjs.insert(a);
        }
        return disjoin (newDsjs, efac);
      }

      if (isOpX<AND>(exp))
      {
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(exp, cnjs);
        for (auto a : cnjs)
        {
          a = simplifyBool(a);
          if (isOpX<FALSE>(a))
          {
            return mk<FALSE>(efac);
          }
          if (isOpX<TRUE>(a))
          {
            continue;
          }
          newCnjs.insert(a);
        }
        return conjoin (newCnjs, efac);
      }

      if (isOpX<ITE>(exp))
      {
        Expr cond = exp->arg(0);
        if (isOpX<TRUE>(cond))
        {
          return exp->arg(1);
        }
        else if (isOpX<FALSE>(cond))
        {
          return exp->arg(2);
        }
        else if (isOpX<TRUE>(exp->arg(1)) && isOpX<FALSE>(exp->arg(2)))
        {
          return cond;
        }
        else if (isOpX<FALSE>(exp->arg(1)) && isOpX<TRUE>(exp->arg(2)))
        {
          return mkNeg(cond);
        }
        else if (exp->arg(1) == exp->arg(2))
        {
          return exp->arg(1);
        }
      }

      if (isOpX<NEG>(exp) &&
          (isOp<ComparissonOp>(exp->left()) ||
           isOpX<TRUE>(exp->left()) || isOpX<FALSE>(exp->left())))
        return mkNeg(exp->left());

      return exp;
    }
  };

  static Expr simplifyArr (Expr exp);

  struct SimplifyArrExpr
  {
    SimplifyArrExpr (ExprVector& _forallVars, ExprMap& _repls) :
      forallVars(_forallVars), repls(_repls) {};

    ExprVector& forallVars;
    ExprMap& repls;

    Expr operator() (Expr exp)
    {
      // GF: to enhance

      if (isOpX<STORE>(exp))
      {
        if (isOpX<STORE>(exp->left()))
        {
          for (auto it = forallVars.begin(); it != forallVars.end(); ++it)
          {
            if (*it == exp->right())
            {
              if (repls[*it] == NULL)
              {
                repls[*it] = exp->left()->right();
                return mk<STORE>(exp->left()->left(), exp->left()->right(), exp->last());
              }
            }
          }
        }
        if (isOpX<STORE>(exp->left()) && exp->right() == exp->left()->right())
          return mk<STORE>(exp->left()->left(), exp->right(), exp->last());
      }

      if (isOpX<SELECT>(exp))
      {
        if (isOpX<STORE>(exp->left()) && exp->right() == exp->left()->right())
        {
          return exp->left()->last();
        }
        if (isOpX<STORE>(exp->left()) && // exp->right() != exp->left()->right() &&
            bind::typeOf(exp->left())->last() == mk<BOOL_TY> (exp->efac ()))
        {
          return mk<OR>(
                        mk<AND>(mk<EQ>(exp->right(), exp->left()->right()),
                                exp->left()->last()),
                        mk<AND>(mk<NEQ>(exp->right(), exp->left()->right()),
                                mk<SELECT>(exp->left()->left(), exp->last())));
        }
      }

      if (isOpX<EQ>(exp))
      {
        if (isOpX<STORE>(exp->left()) && exp->right() == exp->left()->left())
        {
          return simplifyArr(mk<EQ>(mk<SELECT>(exp->right(), exp->left()->right()), exp->left()->last()));
        }
        if (isOpX<STORE>(exp->right()) && exp->left() == exp->right()->left())
        {
          return simplifyArr(mk<EQ>(mk<SELECT>(exp->left(), exp->right()->right()), exp->right()->last()));
        }
        if (isOpX<SELECT>(exp->left()) && isOpX<STORE>(exp->left()->left()) &&
            exp->right() == exp->left()->left()->last())
        {
          return mk<OR>(
            mk<EQ>(exp->left()->right(), exp->left()->left()->right()),
            mk<EQ>(mk<SELECT>(exp->left()->left()->left(), exp->left()->right()), exp->right()));
        }
        if (isOpX<SELECT>(exp->right()) && isOpX<STORE>(exp->right()->left()) &&
            exp->left() == exp->right()->left()->last())
        {
          return mk<OR>(
            mk<EQ>(exp->right()->right(), exp->right()->left()->right()),
            mk<EQ>(mk<SELECT>(exp->right()->left()->left(), exp->right()->right()), exp->left()));
        }
      }
      return exp;
    }
  };

  static Expr simplifyExists (Expr exp);

  struct SimplifyExists
  {
    ExprFactory &efac;
    SimplifyExists (ExprFactory& _efac): efac(_efac){ };

    Expr operator() (Expr exp)
    {
      if (isOpX<EXISTS>(exp))
      {
        ExprVector args;
        for (int i = 0; i < exp->arity() - 1; i++)
          args.push_back(bind::fapp(exp->arg(i)));

        Expr qFree = exp->last();

        if (isOpX<OR>(qFree))
        {
          ExprSet dsj;
          getDisj(qFree, dsj);
          ExprSet q;
          ExprSet newDsj;
          for (auto & c : dsj)
            if (emptyIntersect(c, args)) newDsj.insert(c);
            else q.insert(c);

          for (auto & a : q)
            newDsj.insert(simplifyExists(replaceAll(exp, qFree, a)));

          return disjoin (newDsj, efac);
        }

        // simplify first
        ExprSet cnj;
        getConj(qFree, cnj);
        for (auto & c : cnj)
        {
          if (isOpX<EQ>(c))
          {
            if (find (args.begin(), args.end(), c->right()) == args.end() &&
                find (args.begin(), args.end(), c->left()) != args.end())
              qFree = replaceAll(qFree, c->left(), c->right());
            if (find (args.begin(), args.end(), c->left()) == args.end() &&
                find (args.begin(), args.end(), c->right()) != args.end())
              qFree = replaceAll(qFree, c->right(), c->left());
          }
        }
        qFree = simplifyBool(qFree);

        if (isOpX<TRUE>(qFree)) return qFree;

        // find a subset of conjuncts independent on quantifiers
        cnj.clear();
        getConj(qFree, cnj);
        ExprSet depCnj;
        ExprSet indepCnj;

        for (auto & c : cnj)
          if (emptyIntersect(c, args)) indepCnj.insert(c);
          else depCnj.insert(c);

        if (indepCnj.empty()) return exp;

        indepCnj.insert(simplifyExists(replaceAll(exp, exp->last(), conjoin(depCnj, efac))));
        return conjoin (indepCnj, efac);
      }
      return exp;
    }
  };

  inline static Expr simplifyExists (Expr exp)
  {
    RW<SimplifyExists> rw(new SimplifyExists(exp->getFactory()));
    return dagVisit (rw, exp);
  }

  static Expr createQuantifiedFormulaRestr(Expr def, ExprVector& vars, bool forall);
  inline static Expr simplifyArr (Expr exp)
  {
    ExprVector forallVars;
    ExprMap repls;
    bool origForall = false;
    if (isOpX<FORALL>(exp))
    {
      origForall = true;
      for (int i = 0; i < exp->arity() - 1; i++)
      forallVars.push_back(bind::fapp(exp->arg(i)));
    }
    RW<SimplifyArrExpr> rw(new SimplifyArrExpr(forallVars, repls));
    Expr tmp = dagVisit (rw, exp);

    for (auto it = forallVars.begin(); it != forallVars.end(); )
    {
      if (repls[*it] != NULL) it = forallVars.erase(it);
      else ++it;
    }

    tmp = replaceAll(tmp, repls);
    if (forallVars.empty())
    {
      if (origForall) tmp = tmp->last();
    }
    else tmp = createQuantifiedFormulaRestr (tmp->last(), forallVars, true);

    return tmp;
  }

  inline static Expr simplifyArithm (Expr exp, bool keepRedundandDisj = false, bool keepRedundandConj = false)
  {
    RW<SimplifyArithmExpr> rw(new
      SimplifyArithmExpr(exp, keepRedundandDisj, keepRedundandConj));
    return dagVisit (rw, exp);
  }

  inline static Expr simplifyBool (Expr exp)
  {
    RW<SimplifyBoolExpr> rw(new SimplifyBoolExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }

  inline static void simplBoolReplCnjHlp(ExprVector& hardVars, ExprSet& cnjs, ExprVector& facts, ExprVector& repls)
  {
    bool toRestart;
    ExprSet toInsert;

    for (auto it = cnjs.begin(); it != cnjs.end(); )
    {
      if (isOpX<TRUE>(*it))
      {
        it = cnjs.erase(it);
        continue;
      }

      Expr a = replaceAll(*it, facts, repls);

      if (isOpX<IMPL>(a))
      {
        Expr lhs = simplifyBool(a->left());
        bool isTrue = isOpX<TRUE>(lhs);
        bool isFalse = isOpX<FALSE>(lhs);

        if (isTrue) a = simplifyBool(a->right());
        else if (isFalse) continue;
      }

      if (isOpX<EQ>(a))
      {
        // TODO: this could be symmetric

        Expr lhs = simplifyBool(a->left());
        bool isTrue = isOpX<TRUE>(lhs);
        bool isFalse = isOpX<FALSE>(lhs);

        if (isTrue) a = simplifyBool(a->right());
        else if (isFalse)
        {
          a = simplifyBool(mkNeg(a->right()));
        }
      }

      ExprSet splitted;
      getConj(a, splitted);
      toRestart = false;

      for (auto & c : splitted)
      {
        if (bind::isBoolConst(c))
        {
          bool nothard = find(hardVars.begin(), hardVars.end(), c) == hardVars.end();
          if (nothard)
          {
            toRestart = true;
            facts.push_back(c);
            repls.push_back(mk<TRUE>(a->getFactory()));
            facts.push_back(mkNeg(c));
            repls.push_back(mk<FALSE>(a->getFactory()));
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else if (isOpX<NEG>(c) && bind::isBoolConst(c->left()))
        {
          bool nothardLeft = find(hardVars.begin(), hardVars.end(), c->left()) == hardVars.end();
          if (nothardLeft)
          {
            toRestart = true;
            facts.push_back(c);
            repls.push_back(mk<TRUE>(a->getFactory()));
            facts.push_back(c->left());
            repls.push_back(mk<FALSE>(a->getFactory()));
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else
        {
          toInsert.insert(c);
        }
      }

      it = cnjs.erase(it);
      if (toRestart) break;
    }

    cnjs.insert(toInsert.begin(), toInsert.end());
    if (toRestart)
    {
      simplBoolReplCnjHlp(hardVars, cnjs, facts, repls);
    }
  }

  // simplification based on boolean replacements
  inline static void simplBoolReplCnj(ExprVector& hardVars, ExprSet& cnjs)
  {
    ExprVector facts;
    ExprVector repls;
    simplBoolReplCnjHlp(hardVars, cnjs, facts, repls);
  }

  // rewrites v1 to contain v1 \ v2
  template<typename Range> static void minusSets(ExprSet& v1, Range& v2){
    for (auto it = v1.begin(); it != v1.end(); ){
      if (find(v2.begin(), v2.end(), *it) != v2.end())
        it = v1.erase(it);
      else ++it;
    }
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

  static Expr rewriteMultAdd (Expr exp);

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
        getAddTerm(additiveInverse(*it), terms);
      }
    }
    else if (isOpX<UN_MINUS>(a))
    {
      ExprVector tmp;
      getAddTerm(a->left(), tmp);
      for (auto & t : tmp)
        terms.push_back(additiveInverse(t));
    }
    else if (isOpX<MULT>(a))
    {
      Expr tmp = rewriteMultAdd(a);
      if (tmp == a) terms.push_back(a);
      else getAddTerm(tmp, terms);
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
      if (isOpX<MULT>(exp) && exp->arity() == 2)
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

  struct FindArray : public std::unary_function<Expr, VisitAction>
  {
    bool found;

    FindArray () : found (false) {}

    VisitAction operator() (Expr exp)
    {
      if (found)
      {
        return VisitAction::skipKids ();
      }
      else if (bind::isConst<ARRAY_TY> (exp))
      {
        found = true;
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline bool findArray (Expr e1)
  {
    FindArray fn;
    dagVisit (fn, e1);
    return fn.found;
  }

  inline static Expr simplifiedAnd (Expr a, Expr b){
    ExprSet conjs;
    getConj(a, conjs);
    getConj(b, conjs);
    return conjoin(conjs, a->getFactory());
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
        Expr orredExpr = simplifyArithmDisjunctions(mk<OR>(a, b), false);
        if (!isOpX<TRUE>(orredExpr))
          ps.insert(orredExpr);
      }
    }
  }

  // ab \/ cde \/ f =>
  //                    (a \/ c \/ f) /\ (a \/ d \/ f) /\ (a \/ e \/ f) /\
  //                    (b \/ c \/ f) /\ (b \/ d \/ f) /\ (b \/ e \/ f)
  inline static Expr rewriteOrAnd(Expr exp, bool approx = false)
  {
    int maxConjs = 0;
    ExprSet disjs;
    getDisj(exp, disjs);
    if (disjs.size() == 1)
      return disjoin(disjs, exp->getFactory());

    vector<ExprSet> dconjs;
    for (auto &a : disjs)
    {
      ExprSet conjs;
      getConj(a, conjs);
      dconjs.push_back(conjs);
      if (maxConjs < conjs.size()) maxConjs = conjs.size();
    }

    if (disjs.size() > 3 && maxConjs > 3)
    {
      approx = true;
    }

    if (approx)
    {
      ExprSet newDisjs;
      for (auto &d : dconjs)
        for (auto &c : d)
          newDisjs.insert(c);
      return disjoin(newDisjs, exp->getFactory());
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

  inline static Expr cloneVar(Expr var, Expr new_name) // ... and give a new_name to the clone
  {
//    return replaceAll(var, var->left()->left(), new_name);
    if (bind::isIntConst(var))
      return bind::intConst(new_name);
    else if (bind::isRealConst(var))
      return bind::realConst(new_name);
    else if (bind::isBoolConst(var))
      return bind::boolConst(new_name);
    else if (bind::isConst<ARRAY_TY> (var))
      return bind::mkConst(new_name, mk<ARRAY_TY> (
             var->left()->right()->left(),
             var->left()->right()->right()));
    else if (bind::isAdtConst(var))
    {
      ExprVector type;
      type.push_back(var->last()->last());
      Expr e = bind::fapp(bind::fdecl (new_name, type));
      return e;
    }
    else
      assert(0);
    return NULL;
  }

  inline static bool hasBoolSort(Expr e)
  {
    if (bind::isBoolConst(e) || isOp<BoolOp>(e)) return true;
    return false;
  }

  inline static Expr convertToGEandGT(Expr fla)
  {
    Expr lhs = fla->left();
    Expr rhs = fla->right();

    if (isOpX<NEG>(fla)) return mkNeg(convertToGEandGT(lhs));

    if (isOpX<LT>(fla)) return mk<GT>(rhs, lhs);

    if (isOpX<LEQ>(fla)) return mk<GEQ>(rhs, lhs);

    if (isOpX<EQ>(fla))
    {
      if (hasBoolSort(lhs)) return
          mk<OR>(mk<AND>(lhs, rhs),
                 mk<AND>(mkNeg(lhs), mkNeg(rhs)));
      else if (isNumeric(lhs)) return mk<AND>(
          mk<GEQ>(lhs, rhs), mk<GEQ>(rhs, lhs));
      else return fla;
    }

    if (isOpX<NEQ>(fla))
    {
      if (hasBoolSort(lhs)) return
          mk<OR>(mk<AND>(lhs, mkNeg(rhs)),
                 mk<AND>(mkNeg(lhs), rhs));
      else if (isNumeric(lhs)) return mk<OR>(
          mk<GT>(lhs, rhs), mk<GT>(rhs, lhs));
      else return fla;
    }

    if (isOpX<AND>(fla) || isOpX<OR>(fla))
    {
      ExprSet args;
      for (int i = 0; i < fla->arity(); i++){
        args.insert(convertToGEandGT(fla->arg(i)));
      }

      return isOpX<AND>(fla) ? conjoin (args, fla->getFactory()) :
        disjoin (args, fla->getFactory());
    }
    return fla;
  }

  /* find expressions of type expr = arrayVar in e and store it in output */
  inline static void getArrayEqualExprs(Expr e, Expr arrayVar, ExprVector & output)
  {
    if (e->arity() == 1) {
      return;

    } else if (e->arity() == 2) {
      Expr lhs = e->left();
      Expr rhs = e->right();
      if (lhs == arrayVar) {
        output.push_back(rhs);
        return;

      } else if (rhs == arrayVar) {
        output.push_back(lhs);
        return;
      }
    }

    for (int i = 0; i < e->arity(); i++) {
      getArrayEqualExprs(e->arg(i), arrayVar, output);
    }
  }

  /* find all expressions in e of type expr = arrayVar */
  /* and replace it by STORE(expr, itr, val) = arrayVar*/
  inline static Expr propagateStore(Expr e, Expr itr, Expr val, Expr arrayVar)
  {
    Expr retExpr = e;
    ExprVector exprvec;
    getArrayEqualExprs(e, arrayVar, exprvec);
    for (auto & ev : exprvec)
      retExpr = replaceAll(retExpr, ev, mk<STORE>(ev, itr, val));
    return retExpr;
  }

  struct ITElifter
  {
    ITElifter () {};

    Expr operator() (Expr exp)
    {
      // currently, can lift only one ITE
      if (isOpX<FAPP>(exp) || isOp<ComparissonOp>(exp))
      {
        ExprVector vars1;
        ExprVector vars2;
        Expr cond = NULL;
        int i = 0;
        if (isOpX<FAPP>(exp))
        {
          vars1.push_back(exp->arg(0));
          vars2.push_back(exp->arg(0));
          i = 1;
        }
        for (; i < exp->arity(); i++)
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

        if (isOpX<FAPP>(exp))
          return mk<ITE>(cond, mknary<FAPP>(vars1), mknary<FAPP>(vars2));
        else
        // isOp<ComparissonOp>(exp) here; thus vars1.size() == vars2.size() == 2
          return mk<ITE>(cond, reBuildCmp(exp, vars1[0], vars1[1]), reBuildCmp(exp, vars2[0], vars2[1]));
      }
      return exp;
    }
  };

  inline static Expr liftITEs (Expr exp)
  {
    RW<ITElifter> rw(new ITElifter());
    return dagVisit (rw, exp);
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
      return mkNeg(unfoldITE(term->last()));
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
      if (isOpX<PLUS>(rhs))
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
      if (isOpX<PLUS>(lhs))
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
      if (isOpX<STORE>(lhs))
      {
        Expr arrVar = lhs->left();
        if (isOpX<ITE>(arrVar))
        {
          Expr ifExpr =  unfoldITE(reBuildCmp(term, arrVar->right(), rhs));
          Expr elseExpr = unfoldITE(reBuildCmp(term, arrVar->last(), rhs));

          ifExpr = propagateStore(ifExpr, lhs->right(), lhs->last(), rhs);
          elseExpr = propagateStore(elseExpr, lhs->right(), lhs->last(), rhs);

          Expr condExpr = unfoldITE (arrVar->left());
          Expr retExpr = mk<OR> (mk<AND>(condExpr, ifExpr), mk<AND>(mkNeg(condExpr), elseExpr));

          return retExpr;
        }
      }
      if (isOpX<STORE>(rhs))
      {
        Expr arrVar = rhs->left();
        if (isOpX<ITE>(arrVar))
        {
          Expr ifExpr = unfoldITE (reBuildCmp(term, arrVar->right(), lhs));
          Expr elseExpr = unfoldITE (reBuildCmp(term, arrVar->last(), lhs));

          ifExpr = propagateStore(ifExpr, rhs->right(), rhs->last(), lhs);
          elseExpr = propagateStore(elseExpr, rhs->right(), rhs->last(), lhs);

          Expr condExpr = unfoldITE (arrVar->left());
          Expr retExpr = mk<OR> (mk<AND>(condExpr, ifExpr), mk<AND>(mkNeg(condExpr), elseExpr));

          return retExpr;
        }
      }
      if (isOpX<SELECT>(rhs))
      {
        Expr arrVar = rhs->left();
        if (isOpX<ITE>(arrVar))
        {
          return unfoldITE (reBuildCmp(term,
                 mk<ITE>(arrVar->left(),
                         mk<SELECT>(arrVar->right(), rhs->right()),
                         mk<SELECT>(arrVar->last(), rhs->right())), lhs));
        }
      }
    }
    return term;
  }

  struct MoveInsideITEr
  {
    MoveInsideITEr () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<MOD>(exp))
      {
        Expr ite = exp->arg(0);
        if (isOpX<ITE>(ite))
        {
          return mk<ITE>(ite->arg(0),
                         mk<MOD>(ite->arg(1), exp->arg(1)),
                         mk<MOD>(ite->arg(2), exp->arg(1)));
        }
      }
      if (isOpX<MULT>(exp))
      {
        ExprVector args;
        Expr ite;
        for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it)
        {
          if (isOpX<ITE>(*it))
          {
            if (ite != NULL) return exp;
            ite = *it;
          }
          else
          {
            args.push_back(*it);
          }
        }

        if (ite == NULL) return exp;

        Expr multiplier = mkmult (args, exp->getFactory());
        return mk<ITE>(ite->arg(0),
                       mk<MULT>(multiplier, ite->arg(1)),
                       mk<MULT>(multiplier, ite->arg(2)));
      }

      return exp;
    }
  };

  inline static Expr moveInsideITE (Expr exp)
  {
    RW<MoveInsideITEr> a(new MoveInsideITEr());
    return dagVisit (a, exp);
  }

  struct RAVSUBEXPR: public std::unary_function<Expr,VisitAction>
  {
    Expr s;
    Expr t;
    Expr p;

    RAVSUBEXPR (Expr _s, Expr _t, Expr _p) : s(_s), t(_t), p(_p) {}
    VisitAction operator() (Expr exp) const
    {
      return exp == s ?
        VisitAction::changeTo (replaceAll(exp, t, p)) :
        VisitAction::doKids ();
    }
  };

  // -- replace all occurrences of t by p in a subexpression s  of exp
  inline Expr replaceInSubexpr (Expr exp, Expr s, Expr t, Expr p)
  {
    RAVSUBEXPR rav(s, t, p);
    return dagVisit (rav, exp);
  }

  struct NegAndRewriter
  {
    NegAndRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<NEG>(exp) && isOpX<AND>(exp->arg(0)))
      {
        ExprSet cnjs;
        getConj(exp->arg(0), cnjs);
        ExprSet neggedCnjs;
        for (auto & c : cnjs) neggedCnjs.insert(mkNeg(c));
        return disjoin(neggedCnjs, exp->getFactory());
      }
      return exp;
    }
  };

  inline static Expr rewriteSelectStore(Expr exp);

  struct SelectStoreRewriter
  {
    SelectStoreRewriter () {};

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
      if (isOpX<EQ>(exp) && isOpX<STORE>(exp->right()))
      {
        ExprSet tmp;
        tmp.insert(rewriteSelectStore(mk<EQ>(exp->left(), exp->right()->left())));
        tmp.insert(mk<EQ>(exp->right()->last(), mk<SELECT>(exp->left(), exp->right()->right())));
        return conjoin (tmp, exp->getFactory());
      }
      if (isOpX<EQ>(exp) && isOpX<STORE>(exp->left()))
      {
        ExprSet tmp;
        tmp.insert(rewriteSelectStore(mk<EQ>(exp->right(), exp->left()->left())));
        tmp.insert(mk<EQ>(exp->left()->last(), mk<SELECT>(exp->right(), exp->left()->right())));
        return conjoin (tmp, exp->getFactory());
      }
      return exp;
    }
  };

  struct SelectReplacer : public std::unary_function<Expr, VisitAction>
  {
    ExprMap& sels;
    SelectReplacer (ExprMap& _sels) :  sels(_sels) {};

    Expr operator() (Expr exp)
    {
      if (isOpX<SELECT>(exp))
      {
        if (sels[exp] != NULL) return sels[exp];
        Expr repl = bind::intConst(mkTerm<string> ("sel_" + lexical_cast<string>(sels.size()), exp->getFactory()));
        sels[exp] = repl;
        return repl;
      }
      return exp;
    }
  };

  inline static Expr replaceSelects(Expr exp, ExprMap& sels)
  {
    RW<SelectReplacer> a(new SelectReplacer(sels));
    return dagVisit (a, exp);
  }

  struct QuantifiedVarsFilter : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& vars;

    QuantifiedVarsFilter (ExprSet& _vars): vars(_vars) {};

    VisitAction operator() (Expr exp)
    {
      if (isOp<FORALL>(exp) || isOp<EXISTS>(exp))
      {
        for (int i = 0; i < exp->arity() - 1; i++)
        {
          vars.insert(bind::fapp(exp->arg(i)));
        }
      }
      return VisitAction::doKids ();
    }
  };

  inline void getQuantifiedVars (Expr exp, ExprSet& vars)
  {
    QuantifiedVarsFilter qe (vars);
    dagVisit (qe, exp);
  }

  inline static void getQuantifiedFormulas (Expr a, ExprSet &flas)
  {
    if (isOpX<FORALL>(a) || isOpX<EXISTS>(a))
      flas.insert(a);
    else // TODO: remove/generalize later
      for (unsigned i = 0; i < a->arity(); i++)
        getQuantifiedFormulas(a->arg(i), flas);
  }

  // rewrite just equalities
  template<typename Range> static Expr simpleQE(Expr exp, Range& quantified)
  {
    ExprFactory& efac = exp->getFactory();
    ExprSet cnjsSet;
    getConj(exp, cnjsSet);
    ExprVector cnjs;
    cnjs.insert(cnjs.end(), cnjsSet.begin(), cnjsSet.end());
    for (auto & var : quantified)
    {
      ExprSet eqs;
      for (unsigned it = 0; it < cnjs.size(); )
      {
        Expr cnj = cnjs[it];
        if (!isOpX<EQ>(cnj) || !contains(cnj, var))
          { it++; continue;}

        Expr normalized = cnj;
        if (isNumeric(var) && isNumeric(cnj->left()))
        {
          normalized = simplifyArithm(
            mk<EQ>(mk<PLUS>(cnj->arg(0), additiveInverse(cnj->arg(1))),
              mkTerm (mpz_class (0), efac)));
          normalized = ineqSimplifier(var, normalized);
        }

        // after the normalization, var can be eliminated
        if (!isOpX<EQ>(normalized) || !contains(normalized, var))
          { it++; continue;}

        if (!contains (normalized->right(), var))
        {
          if (var == normalized->left())
          {
            eqs.insert(normalized->right());
            cnjs.erase (cnjs.begin()+it);
            continue;
          }
          else if (isOpX<MULT>(normalized->left()) && isOpX<MPZ>(normalized->left()->left()))
          {
            cnjs.push_back(mk<EQ>(mk<MOD>(normalized->right(), normalized->left()->left()),
                               mkTerm (mpz_class (0), efac)));
          }
        }

//        errs() << "WARNING: COULD NOT NORMALIZE w.r.t. " << *var << ": "
//               << *normalized << "     [[  " << *cnj << "  ]]\n";

        cnjs[it] = normalized;
        it++;
      }

      if (eqs.empty()) continue;

      Expr repl = *eqs.begin();
      int min_sz = INT_MAX;

      // first, search for a non-constant replacement, if possible
      for (auto cnj = std::next(eqs.begin()); cnj != eqs.end(); cnj++)
        if (treeSize(*cnj) < min_sz && !isOpX<MPZ>(*cnj))
          { repl = *cnj; min_sz = treeSize(*cnj); }

      // second, make sure that all replacements are equal
      for (auto cnj = eqs.begin(); cnj != eqs.end(); cnj++)
        if (*cnj != repl) cnjs.push_back(mk<EQ>(repl, *cnj));

      // finally, replace the remaining cnjs
      for (unsigned it = 0; it < cnjs.size(); it++)
        cnjs[it] = replaceAll(cnjs[it], var, repl);

    }

    return (conjoin(cnjs, exp->getFactory()));
  }

  struct QESubexpr
  {
    ExprVector& quantified;
    QESubexpr (ExprVector& _quantified): quantified(_quantified) {};

    Expr operator() (Expr exp)
    {
      if (isOpX<AND>(exp) && !containsOp<OR>(exp))
      {
        return simpleQE(exp, quantified);
      }
      return exp;
    }
  };

  inline static Expr simpleQERecurs(Expr exp, ExprVector& quantified)
  {
    RW<QESubexpr> a(new QESubexpr(quantified));
    return dagVisit (a, exp);
  }

  inline static Expr rewriteNegAnd(Expr exp)
  {
    RW<NegAndRewriter> a(new NegAndRewriter());
    return dagVisit (a, exp);
  }

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

  inline static void getSelects (Expr a, ExprSet &sels)
  {
    if (isOpX<SELECT>(a)){
      sels.insert(a);
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
      getSelects(a->arg(i), sels);
    }
  }

  inline static void getStores (Expr a, ExprSet &st)
  {
    if (isOpX<STORE>(a)){
      st.insert(a);
      getStores(a->left(), st);
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getStores(a->arg(i), st);
    }
  }

  // very simple check if tautology (SMT-based check is expensive)
  inline static bool isTautology(Expr fla)
  {
    if (isOpX<EQ>(fla))
      if (fla->arg(0) == fla->arg(1)) return true;

    if (isOp<ComparissonOp>(fla))
      if (isOpX<MPZ>(fla->arg(0)) && isOpX<MPZ>(fla->arg(1)))
        return evaluateCmpConsts(fla,
          lexical_cast<cpp_int>(fla->arg(0)), lexical_cast<cpp_int>(fla->arg(1)));

    ExprSet cnjs;
    getConj(fla, cnjs);
    if (cnjs.size() < 2) return false;

    bool res = true;
    for (auto &a : cnjs) res &= isTautology(a);

    return res;
  }

  inline static bool isLinearCombination(Expr term)
  {
    // an approximation of..
    if (isNumericConst(term)) {
      return false;
    }
    else if (bind::isIntConst(term)) {
      return true;
    }
    else if (isOpX<MULT>(term)) {
      bool res = false;
      for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it){
        res = res || isLinearCombination(*it);
      }
      return res;
    }
    else if (isOpX<PLUS>(term) || isOpX<MINUS>(term) || isOpX<UN_MINUS>(term)) {
      bool res = true;
      for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it){
        res = res && isLinearCombination(*it);
      }
      return res;
    }
    return false;
  }

  // similar to simplifyArithmDisjunctions
  inline static Expr simplifyArithmConjunctions(Expr fla, bool keep_redundand = false)
  {
    ExprFactory& efac = fla->getFactory();
    ExprSet cnjs, newCnjs;
    getConj(fla, cnjs);
    if (cnjs.size() == 1) return *cnjs.begin();
    ExprSet lin_coms;

    // search for a var, const*var or whatever exists in any conjunct
    for (auto & d : cnjs) {
      if (!isOp<ComparissonOp>(d) ||
          !isNumeric(d->arg(0))) {
        newCnjs.insert(d);
        continue;
      }

      Expr tmp = simplifyArithm(
        reBuildCmp(d, mk<PLUS>(d->arg(0), additiveInverse(d->arg(1))),
                   mkTerm (mpz_class (0), efac)));
      tmp = ineqReverter(tmp);

      newCnjs.insert(tmp);
      lin_coms.insert(tmp->arg(0));
    }

    if (lin_coms.size() == 0) return conjoin(cnjs, efac);

    for (auto &lin_com : lin_coms) {

      cpp_int cur_max_gt;
      cpp_int cur_max_ge;
      cpp_int cur_min_lt;
      cpp_int cur_min_le;

      bool cur_max_gt_bl = false;
      bool cur_max_ge_bl = false;
      bool cur_min_lt_bl = false;
      bool cur_min_le_bl = false;

      set<cpp_int> all_diseqs;

      for (auto it = newCnjs.begin(); it != newCnjs.end(); ) {
        auto d = *it;

        if (!isOp<ComparissonOp>(d) ||
            d->arg(0) != lin_com ||
            !isOpX<MPZ>(d->arg(1))) {
          ++it;
          continue;
        }

        cpp_int c = lexical_cast<cpp_int>(d->arg(1));

        if (isOpX<NEQ>(d))  {
          all_diseqs.insert(c);
        }
        if (isOpX<LEQ>(d)) {
          cur_min_le = cur_min_le_bl ? min(cur_min_le, c) : c;
          cur_min_le_bl = true;
        }
        if (isOpX<GEQ>(d)) {
          cur_max_ge = cur_max_ge_bl ? max(cur_max_ge, c) : c;
          cur_max_ge_bl = true;
        }
        if (isOpX<LT>(d)) {
          cur_min_lt = cur_min_lt_bl ? min(cur_min_lt, c) : c;
          cur_min_lt_bl = true;
        }
        if (isOpX<GT>(d)) {
          cur_max_gt = cur_max_gt_bl ? max(cur_max_gt, c) : c;
          cur_max_gt_bl = true;
        }
        if (isOpX<EQ>(d)) {
          cur_max_ge = cur_max_ge_bl ? max(cur_max_ge, c) : c;
          cur_min_le = cur_min_le_bl ? min(cur_min_le, c) : c;
          cur_max_ge_bl = true;
          cur_min_le_bl = true;
        }
        if (keep_redundand) it++;
        else newCnjs.erase (it++);
      }

      if (cur_min_le_bl)
        while (true) {
          auto tmp = cur_min_le;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_min_le) {
              cur_min_le--;
              if (keep_redundand)
                newCnjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (cur_min_le)), efac)));
              it = all_diseqs.erase(it);
            } else if (*it > cur_min_le) { // remove redundand, e.g., (x != 7 /\ x <= 5)
              if (keep_redundand)
                newCnjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_le) break;
        }

      if (cur_min_lt_bl)
        while (true) {
          auto tmp = cur_min_lt;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_min_lt - 1) {
              cur_min_lt--;
              if (keep_redundand)
                newCnjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (cur_min_lt)), efac)));
              it = all_diseqs.erase(it);
            } else if (*it >= cur_min_lt) {  // remove redundand, e.g., (x != 5 /\ x < 5)
              if (keep_redundand)
                newCnjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_lt) break;
        }

      if (cur_max_ge_bl)
        while (true) {
          auto tmp = cur_max_ge;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_max_ge) {
              cur_max_ge++;
              if (keep_redundand)
                newCnjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (cur_max_ge)), efac)));
              it = all_diseqs.erase(it);
            } else if (*it < cur_max_ge) { // remove redundand, e.g., (x != 4 /\ x >= 5)
              if (keep_redundand)
                newCnjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_ge) break;
        }

      if (cur_max_gt_bl)
        while (true) {
          auto tmp = cur_max_gt;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_max_gt + 1) {
              cur_max_gt++;
              if (keep_redundand)
                newCnjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (cur_max_gt)), efac)));
              it = all_diseqs.erase(it);
            } else if (*it <= cur_max_gt) { // remove redundand, e.g., (x != 5 /\ x > 5)
              if (keep_redundand)
                newCnjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_gt) break;
        }

      for (auto c : all_diseqs) {
        newCnjs.insert (mk<NEQ>(lin_com, mkTerm (mpz_class (string (c)), efac)));
      }

      if ((cur_max_gt_bl && cur_min_lt_bl && cur_max_gt >= cur_min_lt - 1) || // e.g., (x > 3 /\ x < 4)
          (cur_max_ge_bl && cur_min_lt_bl && cur_max_ge >= cur_min_lt) ||
          (cur_max_gt_bl && cur_min_le_bl && cur_max_gt >= cur_min_le) ||
          (cur_max_ge_bl && cur_min_le_bl && cur_max_ge >= cur_min_le + 1))
        return mk<FALSE>(efac);

      if (cur_max_ge_bl && cur_min_le_bl && cur_max_ge == cur_min_le && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkTerm (mpz_class (string (cur_min_le)), efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_gt_bl && cur_min_le_bl && cur_max_gt + 1 == cur_min_le && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkTerm (mpz_class (string (cur_min_le)), efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_ge_bl && cur_min_lt_bl && cur_max_ge + 1 == cur_min_lt && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkTerm (mpz_class (string (cur_max_ge)), efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_gt_bl && cur_min_lt_bl && cur_max_gt + 2 == cur_min_lt && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkTerm (mpz_class (string (cur_max_gt + 1)), efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_min_le_bl && cur_min_lt_bl) {
        if (cur_min_le >= cur_min_lt) {
          newCnjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (cur_min_lt)), efac)));
        }
        else {
          newCnjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (cur_min_le)), efac)));
        }
      }
      else {
        if (cur_min_le_bl) {
          newCnjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (cur_min_le)), efac)));
        }
        if (cur_min_lt_bl) {
          newCnjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (cur_min_lt)), efac)));
        }
      }

      if (cur_max_ge_bl && cur_max_gt_bl) {
        if (cur_max_ge <= cur_max_gt) {    // e.g., x > 5 /\ x >= 5
          newCnjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (cur_max_gt)), efac)));
        }
        else {
          newCnjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (cur_max_ge)), efac)));
        }
      }
      else {
        if (cur_max_ge_bl) {
          newCnjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (cur_max_ge)), efac)));
        }
        if (cur_max_gt_bl) {
          newCnjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (cur_max_gt)), efac)));
        }
      }
    }

    return conjoin(newCnjs, efac);
  }

  // symmetric to simplifyArithmConjunctions
  inline static Expr simplifyArithmDisjunctions(Expr fla, bool keep_redundand = false)
  {
    ExprFactory& efac = fla->getFactory();
    ExprSet dsjs, newDsjs;
    getDisj(fla, dsjs);
    if (dsjs.size() == 1) return *dsjs.begin();

    ExprSet lin_coms;

    // search for a var, const*var or whatever exists in any disjunct
    for (auto & d : dsjs) {

      if (!isOp<ComparissonOp>(d) ||
          !isNumeric(d->arg(0))) {
        newDsjs.insert(d);
        continue;
      }

      Expr tmp = simplifyArithm(
          reBuildCmp(d, mk<PLUS>(d->arg(0), additiveInverse(d->arg(1))),
                     mkTerm (mpz_class (0), efac)));
      tmp = ineqReverter(tmp);
      newDsjs.insert(tmp);
      lin_coms.insert(tmp->arg(0));
    }

    if (lin_coms.size() == 0) return disjoin(dsjs, efac);

    for (auto &lin_com : lin_coms) {

      cpp_int cur_min_gt;
      cpp_int cur_min_ge;
      cpp_int cur_max_lt;
      cpp_int cur_max_le;

      bool cur_min_gt_bl = false;
      bool cur_min_ge_bl = false;
      bool cur_max_lt_bl = false;
      bool cur_max_le_bl = false;

      set<cpp_int> all_eqs;

      for (auto it = newDsjs.begin(); it != newDsjs.end(); ) {
        auto d = *it;

        if (!isOp<ComparissonOp>(d) ||
            d->arg(0) != lin_com ||
            !isOpX<MPZ>(d->arg(1))) {
          ++it;
          continue;
        }

        cpp_int c = lexical_cast<cpp_int>(d->arg(1));

        if (isOpX<EQ>(d))  {
          all_eqs.insert(c);
        }
        if (isOpX<LEQ>(d)) {
          cur_max_le = cur_max_le_bl ? max(cur_max_le, c) : c;
          cur_max_le_bl = true;
        }
        if (isOpX<GEQ>(d)) {
          cur_min_ge = cur_min_ge_bl ? min(cur_min_ge, c) : c;
          cur_min_ge_bl = true;
        }
        if (isOpX<LT>(d))  {
          cur_max_lt = cur_max_lt_bl ? max(cur_max_lt, c) : c;
          cur_max_lt_bl = true;
        }
        if (isOpX<GT>(d))  {
          cur_min_gt = cur_min_gt_bl ? min(cur_min_gt, c) : c;
          cur_min_gt_bl = true;
        }
        if (isOpX<NEQ>(d)) {
          cur_min_gt = cur_min_gt_bl ? min(cur_min_gt, c) : c;
          cur_max_lt = cur_max_lt_bl ? max(cur_max_lt, c) : c;
          cur_min_gt_bl = true;
          cur_max_lt_bl = true;
        }
        if (keep_redundand) it++;
        else newDsjs.erase (it++);
      }

      if (cur_max_le_bl)
        while (true) {
          auto tmp = cur_max_le;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_max_le + 1) {
              cur_max_le++;
              if (keep_redundand)
                newDsjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (cur_max_le)), efac)));
              it = all_eqs.erase(it);
            } else if (*it <= cur_max_le) { // remove redundand, e.g., (x = 3 \/ x <= 5)
              if (keep_redundand)
                newDsjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_le) break;
        }

      if (cur_max_lt_bl)
        while (true) {
          auto tmp = cur_max_lt;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_max_lt) {
              cur_max_lt++;
              if (keep_redundand)
                newDsjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (cur_max_lt)), efac)));
              it = all_eqs.erase(it);
            } else if (*it < cur_max_lt) {  // remove redundand, e.g., (x = 4 \/ x < 5)
              if (keep_redundand)
                newDsjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_lt) break;
        }

      if (cur_min_ge_bl)
        while (true) {
          auto tmp = cur_min_ge;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_min_ge - 1) {
              cur_min_ge--;
              if (keep_redundand)
                newDsjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (cur_min_ge)), efac)));
              it = all_eqs.erase(it);
            } else if (*it >= cur_min_ge) { // remove redundand, e.g., (x = 9 \/ x >= 5)
              if (keep_redundand)
                newDsjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_ge) break;
        }

      if (cur_min_gt_bl)
        while (true) {
          auto tmp = cur_min_gt;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_min_gt) {
              cur_min_gt--;
              if (keep_redundand)
                newDsjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (cur_min_gt)), efac)));
              it = all_eqs.erase(it);
            } else if (*it > cur_min_gt) { // remove redundand, e.g., (x = 6 \/ x > 5)
              if (keep_redundand)
                newDsjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (*it)), efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_gt) break;
        }

      for (auto c : all_eqs) {
        newDsjs.insert (mk<EQ>(lin_com, mkTerm (mpz_class (string (c)), efac)));
      }

      if ((cur_min_gt_bl && cur_max_lt_bl && cur_min_gt <= cur_max_lt - 1) ||
          (cur_min_ge_bl && cur_max_lt_bl && cur_min_ge <= cur_max_lt) ||
          (cur_min_gt_bl && cur_max_le_bl && cur_min_gt <= cur_max_le) ||
          (cur_min_ge_bl && cur_max_le_bl && cur_min_ge <= cur_max_le + 1))
        return mk<TRUE>(efac);

      if (cur_min_gt_bl && cur_max_lt_bl && cur_min_gt == cur_max_lt && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkTerm (mpz_class (string (cur_max_lt)), efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_ge_bl && cur_max_lt_bl && cur_min_ge - 1 == cur_max_lt && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkTerm (mpz_class (string (cur_max_lt)), efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_gt_bl && cur_max_le_bl && cur_min_gt - 1 == cur_max_le && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkTerm (mpz_class (string (cur_min_gt)), efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_ge_bl && cur_max_le_bl && cur_min_ge - 2 == cur_max_le && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkTerm (mpz_class (string (cur_min_ge - 1)), efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_max_le_bl && cur_max_lt_bl) {
        if (cur_max_le >= cur_max_lt) {
          newDsjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (cur_max_le)), efac)));
        }
        else {
          newDsjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (cur_max_lt)), efac)));
        }
      }
      else {
        if (cur_max_le_bl) {
          newDsjs.insert(mk<LEQ>(lin_com, mkTerm (mpz_class (string (cur_max_le)), efac)));
        }
        if (cur_max_lt_bl) {
          newDsjs.insert(mk<LT>(lin_com, mkTerm (mpz_class (string (cur_max_lt)), efac)));
        }
      }

      if (cur_min_ge_bl && cur_min_gt_bl) {
        if (cur_min_ge <= cur_min_gt) {
          newDsjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (cur_min_ge)), efac)));
        }
        else {
          newDsjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (cur_min_gt)), efac)));
        }
      }
      else {
        if (cur_min_ge_bl) {
          newDsjs.insert(mk<GEQ>(lin_com, mkTerm (mpz_class (string (cur_min_ge)), efac)));
        }
        if (cur_min_gt_bl) {
          newDsjs.insert(mk<GT>(lin_com, mkTerm (mpz_class (string (cur_min_gt)), efac)));
        }
      }
    }

    return disjoin(newDsjs, efac);
  }

  inline static Expr normalizeAtom(Expr fla, ExprVector& intVars)
  {
    if (isOp<ComparissonOp>(fla))
    {
      Expr lhs = fla->left();
      Expr rhs = fla->right();

      ExprVector all;
      ExprVector allrhs;

      getAddTerm(lhs, all);
      getAddTerm(rhs, allrhs);
      for (auto & a : allrhs)
      {
        all.push_back(additiveInverse(a));
      }
      ExprSet newlhs;
      for (auto &v : intVars)
      {
        cpp_int coef = 0;
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

            cpp_int c = 1;
            bool success = true;
            for (auto & a : ops)
            {
              if (s1 == lexical_cast<string>(a))
              {
                // all good!
              }
              else if (isOpX<MPZ>(a))
              {
                c = c * lexical_cast<cpp_int>(a);
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
        if (coef != 0) newlhs.insert(mk<MULT>(mkTerm (mpz_class (string(coef)), fla->getFactory()), v));
      }

      bool success = true;
      cpp_int intconst = 0;

      for (auto &e : all)
      {
        if (isOpX<MPZ>(e))
        {
          intconst += lexical_cast<cpp_int>(e);
        }
        else if (isOpX<MULT>(e))
        {
          // GF: sometimes it fails (no idea why)
          cpp_int thisTerm = 1;
          for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
          {
            if (isOpX<MPZ>(*it))
              thisTerm *= lexical_cast<cpp_int>(*it);
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

      if (success && newlhs.size() == 0)
      {
        return (evaluateCmpConsts(fla, 0, -intconst)) ? mk<TRUE>(fla->getFactory()) :
                                                        mk<FALSE>(fla->getFactory());
      }

      if (success)
      {
        Expr pl = (newlhs.size() == 1) ? *newlhs.begin(): mknary<PLUS>(newlhs);
        Expr c = mkTerm (mpz_class (string (-intconst)), fla->getFactory());
        return reBuildCmp(fla, pl, c);
      }
    }
    return fla;
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

  inline static bool getLinCombCoefs(Expr ex, set<cpp_int>& intCoefs)
  {
    bool res = true;
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        res = res && getLinCombCoefs(*it, intCoefs);
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
            if (isOpX<MPZ>((*it)->left()))
              intCoefs.insert(lexical_cast<cpp_int> ((*it)->left()));
            else return false;
          }
        }
      }
      else if (isOpX<MULT>(lhs))
      {
        if (isOpX<MPZ>(lhs->left()))
          intCoefs.insert(lexical_cast<cpp_int> (lhs->left()));
        else return false;
      }
      else
      {
        return false;
      }
    }
    return res;
  }

  inline static void getLinCombConsts(Expr ex, set<cpp_int>& intConsts)
  {
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        getLinCombConsts(*it, intConsts);
      }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      intConsts.insert(lexical_cast<cpp_int> (ex->right()));
    }
  }

  inline static bool isSymmetric (Expr exp)
  {
    return isOpX<EQ>(exp);
  }

  struct BoolEqRewriter
  {
    BoolEqRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<EQ>(exp))
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();
        if (bind::isBoolConst(lhs) || bind::isBoolConst(rhs) ||
            isOpX<NEG>(lhs) || isOpX<NEG>(rhs))
        {
          return mk<AND>(mk<OR>(mkNeg(lhs), rhs),
                         mk<OR>(lhs, mkNeg(rhs)));
        }
        return exp;
      }
      return exp;
    }
  };

  struct AccessRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& accs;

    AccessRetriever (ExprSet& _accs) :  accs(_accs) {};

    VisitAction operator() (Expr exp)
    {
      if ((isOpX<SELECT>(exp) || isOpX<STORE>(exp)) && !findArray(exp->right()))
      {
        accs.insert(exp->right());
      }
      return VisitAction::doKids ();
    }
  };

  inline Expr rewriteBoolEq (Expr exp)
  {
    RW<BoolEqRewriter> tr(new BoolEqRewriter());
    return dagVisit (tr, exp);
  }

  inline void retrieveAccFuns (Expr exp, ExprSet& accs)
  {
    AccessRetriever dr (accs);
    dagVisit (dr, exp);
  }

  inline static Expr mergeIneqs (Expr e1, Expr e2)
  {
    if (isOpX<NEG>(e1)) e1 = mkNeg(e1->last());
    if (isOpX<NEG>(e2)) e2 = mkNeg(e2->last());

    if (isOpX<GEQ>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->left())
      return mk<GEQ>(e1->left(), e2->right());
    if (isOpX<GT>(e1) && isOpX<GT>(e2) && e1->right() == e2->left())
      return mk<GT>(e1->left(), e2->right());
    if (isOpX<GEQ>(e1) && isOpX<GT>(e2) && e1->right() == e2->left())
      return mk<GT>(e1->left(), e2->right());
    if (isOpX<GT>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->left())
      return mk<GT>(e1->left(), e2->right());
    if (isOpX<GT>(e1) && isOpX<GEQ>(e2) && (e1->left() == e2->right()))
      return mk<GT>(e2->left(), e1->right());

    if (isOpX<LEQ>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->left())
      return mk<LEQ>(e1->left(), e2->right());
    if (isOpX<LT>(e1) && isOpX<LT>(e2) && e1->right() == e2->left())
      return mk<LT>(e1->left(), e2->right());
    if (isOpX<LEQ>(e1) && isOpX<LT>(e2) && e1->right() == e2->left())
      return mk<LT>(e1->left(), e2->right());
    if (isOpX<LT>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->left())
      return mk<LT>(e1->left(), e2->right());

    if (isOpX<LEQ>(e1) && isOpX<LEQ>(e2) && e2->right() == e1->left())
      return mk<LEQ>(e2->left(), e1->right());
    if (isOpX<LT>(e2) && isOpX<LT>(e1) && e2->right() == e1->left())
      return mk<LT>(e2->left(), e1->right());
    if (isOpX<LEQ>(e2) && isOpX<LT>(e1) && e2->right() == e1->left())
      return mk<LT>(e2->left(), e1->right());
    if (isOpX<LT>(e2) && isOpX<LEQ>(e1) && e2->right() == e1->left())
      return mk<LT>(e2->left(), e1->right());

    if (isOpX<LEQ>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->right())
      return mk<LEQ>(e1->left(), e2->left());
    if (isOpX<LT>(e1) && isOpX<GT>(e2) && e1->right() == e2->right())
      return mk<LT>(e1->left(), e2->left());
    if (isOpX<LEQ>(e1) && isOpX<GT>(e2) && e1->right() == e2->right())
      return mk<LT>(e1->left(), e2->left());
    if (isOpX<LT>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->right())
      return mk<LT>(e1->left(), e2->left());

    if (isOpX<LEQ>(e1) && isOpX<GEQ>(e2) && e1->left() == e2->left())
      return mk<LEQ>(e2->right(), e1->right());
    if (isOpX<LT>(e1) && isOpX<GT>(e2) && e1->left() == e2->left())
      return mk<LT>(e2->right(), e1->right());
    if (isOpX<LEQ>(e1) && isOpX<GT>(e2) && e1->left() == e2->left())
      return mk<LT>(e2->right(), e1->right());
    if (isOpX<LT>(e1) && isOpX<GEQ>(e2) && e1->left() == e2->left())
      return mk<LT>(e2->right(), e1->right());

    if (isOpX<GEQ>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->right())
      return mk<GEQ>(e1->left(), e2->left());
    if (isOpX<GT>(e1) && isOpX<LT>(e2) && e1->right() == e2->right())
      return mk<GT>(e1->left(), e2->left());
    if (isOpX<GEQ>(e1) && isOpX<LT>(e2) && e1->right() == e2->right())
      return mk<GT>(e1->left(), e2->left());
    if (isOpX<GT>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->right())
      return mk<GT>(e1->left(), e2->left());

    // TODO: support more cases
    return NULL;
  }

  inline static Expr mergeIneqsWithVar (Expr e, Expr var)
  {
    ExprSet cnjs;
    ExprVector cnjs2;
    ExprSet cnjs3;
    getConj(e, cnjs);
    for (auto & a : cnjs)
      if (contains(a, var)) cnjs2.push_back(a);
      else cnjs3.insert(a);

    if (cnjs2.size() != 2) return e;

    if(mergeIneqs(cnjs2[0], cnjs2[1]) == NULL) return NULL;

    cnjs3.insert(mergeIneqs(cnjs2[0], cnjs2[1]));
    return conjoin(cnjs3, e->getFactory());
  }

  template <typename T> static void computeTransitiveClosure(ExprSet& r, ExprSet& tr)
  {
    for (auto &a : r)
    {
      if (isOpX<T>(a))
      {
        for (auto &b : tr)
        {
          if (isOpX<T>(b))
          {
            if (a->left() == b->right()) tr.insert(mk<T>(b->left(), a->right()));
            if (b->left() == a->right()) tr.insert(mk<T>(a->left(), b->right()));

            if (isSymmetric(a))
            {
              if (a->left()  == b->left())  tr.insert(mk<T>(a->right(), b->right()));
              if (a->right() == b->right()) tr.insert(mk<T>(a->left(),  b->left()));
            }
          }
        }
      }
      tr.insert(a);
    }
  }

  struct TransClAdder
  {
    TransClAdder () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<AND>(exp))
      {
        ExprSet cnjs;
        ExprSet trCnjs;
        getConj(exp, cnjs);
        computeTransitiveClosure<EQ>(cnjs, trCnjs);
        computeTransitiveClosure<LEQ>(cnjs, trCnjs);
        computeTransitiveClosure<GEQ>(cnjs, trCnjs);
        computeTransitiveClosure<LT>(cnjs, trCnjs);
        computeTransitiveClosure<GT>(cnjs, trCnjs);
        return conjoin(trCnjs, exp->getFactory());
      }

      return exp;
    }
  };

  inline static Expr enhanceWithMoreClauses (Expr exp)
  {
    RW<TransClAdder> tr(new TransClAdder());
    return dagVisit (tr, exp);
  }

  inline static Expr propagateEqualities (Expr exp)
  {
    ExprSet cnjs;
    ExprSet eqs;
    ExprSet trEqs;

    getConj(exp, cnjs);

    for (auto &a : cnjs) if (isOpX<EQ>(a)) eqs.insert(a);
    if (eqs.size() == 0) return exp;

    computeTransitiveClosure<EQ>(eqs, trEqs);

    for (auto &a : trEqs)
    {
      if (isOpX<EQ>(a))
      {
        bool toAdd = true;
        for (auto & c : cnjs)
        {
          if (isOpX<EQ>(c))
          {
            if (c->left() == a->left() && c->right() == a->right()) { toAdd = false; break; }
            if (c->left() == a->right() && c->right() == a->left()) { toAdd = false; break; }
          }
        }
        if (toAdd) cnjs.insert(a);
      }
// TODO: double-check if it is needed:
/*      else
      {
        Expr neg = mkNeg(a);
        for (auto &b : trEqs)
        {
          Expr repl1 = replaceAll(neg, b->left(), b->right());
          Expr repl2 = replaceAll(neg, b->right(), b->left());
          bool eq1 = (repl1 == neg);
          bool eq2 = (repl2 == neg);
          bool eq3 = (repl2 == repl1);

          if (eq1 && eq2 && eq3) cnjs.insert(a);
          else if (eq1) cnjs.insert (mkNeg (mk<AND>(neg, repl2)));
          else if (eq2) cnjs.insert (mkNeg (mk<AND>(neg, repl1)));
          else cnjs.insert(mkNeg (mk<AND>(neg, mk<AND>(repl1, repl2))));
        }
      } */
    }

    return conjoin(cnjs, exp->getFactory());
  }

  bool isConstExpr(Expr e) {
    using namespace expr::op::bind;
    if (isIntConst(e) || isBoolConst(e) || isRealConst(e)) return true;
    return false;
  }

  bool isLitExpr(Expr e) {
    int arity = e->arity();
    if (isConstExpr(e)) return false;
    if (arity == 0) return true;
    bool res = true;
    for (int i = 0; i < arity; i++) {
      res = res && isLitExpr(e->arg(i));
    }
    return res;
  }

  bool isConstAddModExpr(Expr e) {
    using namespace expr::op::bind;
    if (isOp<PLUS>(e) || isOp<MINUS>(e) || isOp<MOD>(e)) {
      if (isLitExpr(e->arg(0))) {
        return isConstAddModExpr(e->arg(1));
      }
      if (isLitExpr(e->arg(1))) {
        return isConstAddModExpr(e->arg(0));
      }
    }
    return isConstExpr(e);
  }

  bool isNonlinear(Expr e) {
    int arity = e->arity();
    if (isOp<MOD>(e)) {
      if (isLitExpr(e->arg(0))) {
        return !(isLitExpr(e->arg(1)) || !isConstExpr(e->arg(1)));
      }
      if (isLitExpr(e->arg(1))) {
        return !(isConstAddModExpr(e->arg(0)));
      }
      return true;
    }
    if (isOp<MULT>(e) || isOp<DIV>(e)) {
      if (isLitExpr(e->arg(0))) {
        return isNonlinear(e->arg(1));
      }
      if (isLitExpr(e->arg(1))) {
        return isNonlinear(e->arg(0));
      }
      return true;
    }
    bool res = false;
    for (int i = 0; i < arity; i++) {
      res = res || isNonlinear(e->arg(i));
    }
    return res;
  }

  struct QVMiner : public std::unary_function<Expr, VisitAction>
  {
    map<Expr, ExprVector>& vars;
    QVMiner (map<Expr, ExprVector>& _vars): vars(_vars) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<FORALL>(exp) || isOpX<EXISTS>(exp))
      {
        for (int i = 0; i < exp->arity() - 1; i++)
          vars[exp].push_back(bind::fapp(exp->arg(i)));

        reverse(vars[exp].begin(),vars[exp].end());

        for (auto & a : vars)
          if (contains(a.first, exp) && a.first != exp)
            vars[exp].insert(vars[exp].end(), a.second.begin(), a.second.end());
      }
      return VisitAction::doKids ();
    }
  };

  inline void getQVars (Expr exp, map<Expr, ExprVector>& vars)
  {
    QVMiner qvm (vars);
    dagVisit (qvm, exp);
  }

  struct QFregularizer
  {
    ExprVector& vars;
    QFregularizer (ExprVector& _vars): vars(_vars){};
    Expr operator() (Expr exp)
    {
      if (bind::isBVar(exp)) return vars[bind::bvarId(exp)];
      return exp;
    }
  };

  inline static Expr regularizeQF (Expr exp)
  {
    map<Expr, ExprVector> vars;
    getQVars(exp, vars);
    ExprMap replaced;
    for (auto & a : vars)
    {
      Expr sub = replaceAll(a.first, replaced);
      RW<QFregularizer> rw(new QFregularizer(a.second));
      Expr b = dagVisit (rw, sub);
      replaced[a.first] = b;
      exp = replaceAll(exp, sub, b);
    }

    return exp;
  }

  inline static bool findMatching(Expr pattern, Expr exp, ExprVector& vars, ExprMap& matching)
  {
    if (pattern == exp && (isOpX<FDECL>(pattern) || isOpX<MPZ>(pattern) ||
                           isOpX<TRUE>(exp) || isOpX<FALSE>(exp)))  return true;

    // currently, workaround:
    if (isOpX<FORALL>(pattern) && !isOpX<FORALL>(exp)) return false;
    if (isOpX<EXISTS>(pattern) && !isOpX<EXISTS>(exp)) return false;
    if (isOpX<FORALL>(exp) && !isOpX<FORALL>(pattern)) return false;
    if (isOpX<EXISTS>(exp) && !isOpX<EXISTS>(pattern)) return false;

    if (!isOpX<FORALL>(exp) && !isOpX<EXISTS>(exp) &&
        !isOpX<FORALL>(pattern) && !isOpX<EXISTS>(pattern))
      if (bind::typeOf(pattern) != bind::typeOf(exp))
      {
        return false;
      }

    if (pattern->arity() == 1 && find(vars.begin(), vars.end(), pattern) != vars.end())
    {
      if (matching[pattern] != NULL && matching[pattern] != exp)
      {
        return false;
      }
      else
      {
        matching[pattern] = exp;
        return true;
      }
    }

    if ((isOpX<EQ>(exp) && isOpX<EQ>(pattern)) ||
        (isOpX<NEQ>(exp) && isOpX<NEQ>(pattern)) ||
        (isOpX<LEQ>(exp) && isOpX<LEQ>(pattern)) ||
        (isOpX<GEQ>(exp) && isOpX<GEQ>(pattern)) ||
        (isOpX<LT>(exp) && isOpX<LT>(pattern)) ||
        (isOpX<GT>(exp) && isOpX<GT>(pattern)) ||
        (isOpX<NEG>(exp) && isOpX<NEG>(pattern)) ||
        (isOpX<AND>(exp) && isOpX<AND>(pattern)) ||
        (isOpX<OR>(exp) && isOpX<OR>(pattern)) ||
        (isOpX<IMPL>(exp) && isOpX<IMPL>(pattern)) ||
        (isOpX<ITE>(exp) && isOpX<ITE>(pattern)) ||
        (isOpX<PLUS>(exp) && isOpX<PLUS>(pattern)) ||
        (isOpX<MINUS>(exp) && isOpX<MINUS>(pattern)) ||
        (isOpX<UN_MINUS>(exp) && isOpX<UN_MINUS>(pattern)) ||
        (isOpX<MULT>(exp) && isOpX<MULT>(pattern)) ||
        (isOpX<STORE>(exp) && isOpX<STORE>(pattern)) ||
        (isOpX<SELECT>(exp) && isOpX<SELECT>(pattern)) ||
        (isOpX<FORALL>(exp) && isOpX<FORALL>(pattern)) ||
        (isOpX<EXISTS>(exp) && isOpX<EXISTS>(pattern)) ||
        (isOpX<FAPP>(exp) && isOpX<FAPP>(pattern) &&
          pattern->left() == exp->left()))
    {
      for (int i = 0; i < pattern->arity(); i++)
      {
        if (!findMatching(pattern->arg(i), exp->arg(i), vars, matching))
        {
          return false;
        }
      }
      return true;
    }
    return false;
  }

  struct SubexprMatcher : public std::unary_function<Expr, VisitAction>
  {
    bool found;
    ExprVector& vars;
    std::set<ExprMap>& matchingSet;
    Expr pattern;
    SubexprMatcher (Expr _p, ExprVector& _v, std::set<ExprMap>& _m) :
      found(false), pattern(_p), vars(_v), matchingSet(_m) {}

    VisitAction operator() (Expr exp)
    {
      ExprMap matching;
      if ((isOpX<FAPP>(exp) || isOp<ComparissonOp>(exp) ||
        isOp<BoolOp>(exp) || isOpX<SELECT>(exp) || isOpX<STORE>(exp)) &&
        !(containsOp<FORALL>(exp) || containsOp<EXISTS>(exp)) &&
        findMatching (pattern, exp, vars, matching))
      {
        found = true;
        matchingSet.insert(matching);
      }
      return VisitAction::doKids ();
    }
  };

  inline bool findMatchingSubexpr (Expr pattern, Expr exp, ExprVector& vars, std::set<ExprMap>& matchingSet)
  {
    SubexprMatcher fn (pattern, vars, matchingSet);
    dagVisit (fn, exp);
    return fn.found;
  }

  inline static bool evalLeq(Expr a, Expr b)
  {
    if (isOpX<MPZ>(a) && isOpX<MPZ>(b))
      return (lexical_cast<cpp_int>(a) <= lexical_cast<cpp_int>(b));
    else return (a == b); // GF: to extend
  }

  inline static void mutateHeuristic (Expr exp, ExprSet& guesses /*, int bnd = 100*/)
  {
    exp = unfoldITE(exp);
    ExprSet cnjs;
    getConj(exp, cnjs);
    ExprSet ineqs;
    ExprSet eqs;
    ExprSet disjs;
    for (auto c : cnjs)
    {
      if (isOpX<NEG>(c)) c = mkNeg(c->left());

      if (isOpX<EQ>(c))
      {
        if (isNumeric(c->left()))
        {
          eqs.insert(c);
          ineqs.insert(mk<LEQ>(c->right(), c->left()));
          ineqs.insert(mk<LEQ>(c->left(), c->right()));
        }
        else
        {
          guesses.insert(simplifyArithm(c));
        }
      }
      else if (isOp<ComparissonOp>(c))
      {
        if (isOpX<LEQ>(c)) ineqs.insert(c);
        else if (isOpX<GEQ>(c)) ineqs.insert(mk<LEQ>(c->right(), c->left()));
        else if (isOpX<GT>(c))
        {
          if (isOpX<MPZ>(c->left()))
            ineqs.insert(mk<LEQ>(c->right(), mkTerm (mpz_class (string (lexical_cast<cpp_int>(c->left())-1)), exp->getFactory())));
          else if(isOpX<MPZ>(c->right()))
            ineqs.insert(mk<LEQ>(mkTerm (mpz_class (string (lexical_cast<cpp_int>(c->right())+1)), exp->getFactory()), c->left()));
          else
            ineqs.insert(mk<LEQ>(c->right(), mk<MINUS>(c->left(), mkTerm (mpz_class (1), exp->getFactory()))));
        }
        else if (isOpX<LT>(c))
        {
          if (isOpX<MPZ>(c->left()))
            ineqs.insert(mk<LEQ>(mkTerm (mpz_class (string (lexical_cast<cpp_int>(c->left())+1)), exp->getFactory()), c->right()));
          else if(isOpX<MPZ>(c->right()))
            ineqs.insert(mk<LEQ>(c->left(), mkTerm (mpz_class (string (lexical_cast<cpp_int>(c->right())-1)), exp->getFactory())));
          else
            ineqs.insert(mk<LEQ>(c->left(), mk<MINUS>(c->right(), mkTerm (mpz_class (1), exp->getFactory()))));
        }
        else
        {
          assert (isOpX<NEQ>(c));
          guesses.insert(c);
        }
      }
/*      else if (isOpX<OR>(c))
      {
        ExprSet terms;
        getDisj(c, terms);
        ExprSet newTerms;
        for (auto t : terms)
        {
          if (newTerms.size() > 2) continue; // don't consider large disjunctions
          if (isOpX<NEG>(t)) t = mkNeg(t->left());
          if (!isOp<ComparissonOp>(t)) continue;
          if (!isNumeric(t->left())) continue;
          newTerms.insert(t);
        }
        c = disjoin(newTerms, c->getFactory());
        disjs.insert(c);
        guesses.insert(c);
      }*/
      else guesses.insert(c);
    }


    for (auto & z : eqs)
    {
      for (auto & in : ineqs)
      {
        //if (bnd > guesses.size()) return;
        if (!emptyIntersect(z, in)) continue;
        ineqs.insert(mk<LEQ>(mk<PLUS>(in->left(), z->left()), mk<PLUS>(in->right(), z->right())));
        ineqs.insert(mk<LEQ>(mk<PLUS>(in->left(), z->right()), mk<PLUS>(in->right(), z->left())));
      }

      for (auto & d : disjs)
      {
        //if (bnd > guesses.size()) return;
        ExprSet terms;
        getDisj(d, terms);
        ExprSet newTerms;
        for (auto c : terms)
        {
          if (isOp<ComparissonOp>(c))
          {
            if (emptyIntersect(z, c))
              newTerms.insert(reBuildCmp(c,
                mk<PLUS>(c->left(), z->left()), mk<PLUS>(c->right(), z->right())));
            else newTerms.insert(c);
          }
          else newTerms.insert(c);
        }
        if (newTerms.size() > 0)
          guesses.insert(disjoin(newTerms, d->getFactory()));
      }
    }

    for (auto & a : ineqs) guesses.insert(simplifyArithm(a));
//    guesses.insert(ineqs.begin(), ineqs.end());

    for (auto & e : eqs)
    {
      for (auto & in : ineqs)
      {
        //if (bnd > guesses.size()) return;
        assert(isOpX<LEQ>(in));
        Expr g;
        if (in->left() == e->left() && !evalLeq(e->right(), in->right()))
          g = mk<LEQ>(e->right(), in->right());
        else if (in->left() == e->right() && !evalLeq(e->left(), in->right()))
          g = mk<LEQ>(e->left(), in->right());
        else if (in->right() == e->left() && !evalLeq(in->left(), e->right()))
          g = mk<LEQ>(in->left(), e->right());
        else if (in->right() == e->right() && !evalLeq(in->left(), e->left()))
          g = mk<LEQ>(in->left(), e->left());

        if (g != NULL) guesses.insert(simplifyArithm(g));
      }
    }

    for (auto & in1 : ineqs)
    {
      for (auto & in2 : ineqs)
      {
//        if (bnd > guesses.size()) return;
        if (in1 == in2) continue;

        assert(isOpX<LEQ>(in1));
        assert(isOpX<LEQ>(in2));

        if (evalLeq(in1->right(), in2->left()) &&
            !evalLeq(in1->left(), in2->right()))
        {
          guesses.insert(simplifyArithm(mk<LEQ>(in1->left(), in2->right())));
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
      cpp_int coef = 0;
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

          cpp_int c = 1;
          bool success = true;
          for (auto & a : ops)
          {
            if (s1 == lexical_cast<string>(a))
            {
              // all good!
            }
            else if (isOpX<MPZ>(a))
            {
              c = c * lexical_cast<cpp_int>(a);
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
        newtermPos.insert(mk<MULT>(mkTerm (mpz_class (string (coef)), term->getFactory()), v));
      else if (coef == -1)
        newtermNeg.insert(v);
      else if (coef < 0)
        newtermNeg.insert(mk<MULT>(mkTerm (mpz_class (string (-coef)), term->getFactory()), v));
    }

    bool success = true;
    cpp_int intconst = 0;

    for (auto &e : all)
    {
      if (isOpX<MPZ>(e))
      {
        intconst += lexical_cast<cpp_int>(e);
      }
      else if (isOpX<MULT>(e))
      {
        cpp_int thisTerm = 1;
        for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
        {
          if (isOpX<MPZ>(*it))
            thisTerm *= lexical_cast<cpp_int>(*it);
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
      newtermPos.insert(mkTerm (mpz_class (string (intconst)), term->getFactory()));
    else if (intconst < 0)
      newtermNeg.insert(mkTerm (mpz_class (string (-intconst)), term->getFactory()));

    for (auto & a : newtermNeg)
      newtermPos.insert(additiveInverse(a));
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
          normalizeTerm(mk<PLUS>(e->left(), additiveInverse(e->right()))),
            mkTerm (mpz_class (0), efac));
      }
      return e;
    }
  };

  inline static Expr normalizeArithm (Expr exp)
  {
    ExprSet complex;
    findComplexNumerics(exp, complex);
    ExprMap repls;
    ExprMap replsRev;
    for (auto & a : complex)
    {
      Expr repl = bind::intConst(mkTerm<string>
        ("__repl_" + lexical_cast<string>(repls.size()), exp->getFactory()));
      repls[a] = repl;
      replsRev[repl] = a;
    }
    exp = replaceAll(exp, repls);
    RW<NormalizeArithmExpr> rw(new NormalizeArithmExpr(exp->getFactory()));
    exp = dagVisit (rw, exp);
    exp = replaceAll(exp, replsRev);
    return exp;
  }

  Expr static normalizeImplHlp (Expr e, ExprSet& lhs)
  {
    if (isOpX<IMPL>(e))
    {
      getConj(e->left(), lhs);
      return normalizeImplHlp(e->right(), lhs);
    }
    return e;
  }

  Expr static normalizeImpl (Expr e)
  {
    ExprSet lhs;
    Expr rhs = normalizeImplHlp(e, lhs);
    if (lhs.empty()) return e;
    for (auto & a : lhs) rhs = mk<IMPL>(a, rhs);
    return rhs;
  }

  Expr static createQuantifiedFormulaRestr (Expr def, ExprVector& vars, bool forall = true)
  {
    if (vars.empty()) return def;
    ExprVector args;
    for (auto & a : vars) args.push_back(a->last());
    args.push_back(def);
    if (forall) return mknary<FORALL>(args);
    else return mknary<EXISTS>(args);
  }

  Expr static createQuantifiedFormula (Expr def, ExprVector& toAvoid)
  {
    ExprVector vars;
    filter(def, bind::IsConst (), inserter(vars, vars.begin()));
    for (auto it = vars.begin(); it != vars.end(); )
      if (find(toAvoid.begin(), toAvoid.end(), (*it)->left()) != toAvoid.end())
        it = vars.erase(it);
      else
        ++it;
    if (vars.size() == 0)
      return def;
    return createQuantifiedFormulaRestr(def, vars);
  }

 struct PlusMinusConstSwapper
  {
    PlusMinusConstSwapper (){};

    Expr operator() (Expr exp)
    {
      if (isOpX<PLUS>(exp) || isOpX<MINUS>(exp))
      {
        ExprVector ops;
        ExprVector newOps;
        getAddTerm(exp, ops);
        for (auto & a : ops)
        {
          if (isOpX<MPZ>(a)) newOps.push_back(additiveInverse(a));
          else newOps.push_back(a);
        }
        return mkplus(newOps, exp->getFactory());
      }
      return exp;
    }
  };

  inline static Expr swapPlusMinusConst (Expr exp)
  {
    RW<PlusMinusConstSwapper> rw(new PlusMinusConstSwapper());
    return dagVisit (rw, exp);
  }

  bool static isConstPos(Expr e)
  {
    ExprVector ops;
    getAddTerm(e, ops);
    cpp_int i = 0;
    for (auto & a : ops)
      if (isOpX<MPZ>(a)) i += lexical_cast<cpp_int>(a);

    return i>0;
  }
}

#endif
