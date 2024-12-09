#ifndef EXPRSIMPL__HPP__
#define EXPRSIMPL__HPP__
#include <assert.h>

#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace expr::op::bind;
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
      (terms.size() == 0) ? mkMPZ (0, efac) :
      (terms.size() == 1) ? *terms.begin() :
      mknary<PLUS>(terms);
  }

  template<typename Range> static Expr mkmult(Range& terms, ExprFactory &efac){
    return
      (terms.size() == 0) ? mkMPZ (1, efac) :
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
    filter (a, IsConst (), inserter(av, av.begin()));
    return emptyIntersect(av, bv);
  }

  inline static bool emptyIntersect(Expr a, Expr b){
    ExprVector bv;
    filter (b, IsConst (), inserter(bv, bv.begin()));
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

  inline static Expr distribDisjoin(Expr d1, Expr d2)
  {
    ExprSet dsj1, dsj2, comm;
    getConj(d1, dsj1);
    getConj(d2, dsj2);
    for (auto it1 = dsj1.begin(); it1 != dsj1.end(); )
    {
      bool found = false;
      for (auto it2 = dsj2.begin(); it2 != dsj2.end(); )
      {
        if (*it1 == *it2)
        {
          found = true;
          comm.insert(*it1);
          it1 = dsj1.erase(it1);
          it2 = dsj2.erase(it2);
          break;
        }
        else ++it2;
      }
      if (!found) ++it1;
    }
    comm.insert(mk<OR>(conjoin(dsj1, d1->getFactory()),
                       conjoin(dsj2, d1->getFactory())));
    return conjoin(comm, d1->getFactory());
  }

  inline static void getArrInds (Expr a, ExprSet &inds)
  {
    if ((isOpX<SELECT>(a) || isOpX<STORE>(a))
        && !containsOp<SELECT>(a->right()) && !containsOp<STORE>(a->right()))
      inds.insert(a->right());

    for (unsigned i = 0; i < a->arity(); i++)
      getArrInds(a->arg(i), inds);
  }

  inline static void getITEs (Expr a, ExprVector &ites)
  {
    if (isOpX<ITE>(a)){
      ites.push_back(a);
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getITEs(a->arg(i), ites);
    }
  }

  inline static bool isBoolean(Expr a)
  {
    return typeOf(a) == mk<BOOL_TY>(a->getFactory());
  }

  inline static bool isNumeric(Expr a)
  {
    return typeOf(a) == mk<INT_TY>(a->getFactory());
  }

  inline static bool isNumericEq(Expr a)
  {
    return isOpX<EQ>(a) && isNumeric(a->left());
  }

  inline static bool isNumericConst(Expr e)
  {
    return isOpX<MPZ>(e) || isOpX<MPQ>(e);
  }

  inline static void findComplexNumerics (Expr a, ExprSet &terms)
  {
    if (isIntConst(a) || isOpX<MPZ>(a)) return;
    if (isNumeric(a) && !isOpX<ITE>(a))
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

  inline static void getChainOfStores (Expr a, ExprSet &stores)
  {
    if (isOp<STORE>(a))
    {
      stores.insert(a);
      getChainOfStores(a->left(), stores);
    }
    else if (isOpX<ITE>(a))
    {
      for (unsigned i = 1; i <= 2; i++)
        getChainOfStores(a->arg(i), stores);
    }
  }

  inline static void getMultOps (Expr a, ExprVector &ops)
  {
    if (isOpX<MULT>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getMultOps(a->arg(i), ops);
      }
    } else if (isOpX<UN_MINUS>(a) && isNumeric(a->left())){
      ops.push_back(mkMPZ ((-1), a->getFactory()));
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
      return mk<MULT>(mkMPZ (1, e->getFactory()), e);
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

      Expr num = mkMPZ (-coef, e->getFactory());
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
      return mkMPZ(-lexical_cast<cpp_int>(e), e->getFactory());
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
    else if (isOpX<ITE>(e)){
      return mk<ITE>(e->left(), additiveInverse(e->right()), additiveInverse(e->last()));
    }
//    return mk<MULT>(mkMPZ ((-1), e->getFactory()), e);
    return mk<UN_MINUS>(e);
  }

  /**
   * Commutativity in Addition
   */
  inline static Expr exprSorted(Expr e){
    if (!isNumeric(e)) return e;
    ExprVector addTrms;
    getAddTerm(e, addTrms);
    std::sort(addTrms.begin(), addTrms.end(), [](Expr& x, Expr& y) {return x < y;});
    return mkplus(addTrms, e->getFactory());
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

    if (isIntConst(tmp) || isRealConst(tmp))
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
      l = mkMPZ (0, e->getFactory());
    } else if (coef == 1){
      l = var;
    } else {
      l = mk<MULT>(mkMPZ(coef, e->getFactory()), var);
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
    vector<ExprSet::iterator> tmp;
    ExprSet newClauses;
    for (auto it1 = expClauses.begin(); it1 != expClauses.end(); ++it1){
      if (isOpX<LEQ>(*it1)){
        for (auto it2 = expClauses.begin(); it2 != expClauses.end(); ++it2){
          if (isOpX<GEQ>(*it2)){
            Expr e1l = exprSorted(mk<MINUS>((*it1)->left(), (*it1)->right()));
            Expr e2l = exprSorted(mk<MINUS>((*it2)->left(), (*it2)->right()));
            if ( e1l == e2l ){
              newClauses.insert(mk<EQ>(e1l, mkMPZ(0, e1l->getFactory())));
              if (clean){
                tmp.push_back (it1);
                tmp.push_back (it2);
                break;
              }
            }
          }
        }
      }
    }
    for (auto & it : tmp) expClauses.erase(it);
    expClauses.insert(newClauses.begin(), newClauses.end());
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

      if (merge) ineqMerger(substsMap, true);
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

  template<typename T> static void unique_push_back(T e, vector<T>& v) {
    if (find(v.begin(), v.end(), e) == v.end()) v.push_back(e);
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
    else if (isOpX<XOR>(fla) && fla->arity() == 2)
    {
      return mk<EQ>(fla->arg(0), fla->arg(1));
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
    if (c != 0) plsOps.push_back(mkMPZ(c, exp->getFactory()));
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

      Expr num = mkMPZ (coef, e->getFactory());
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
        return mkMPZ (0, e->getFactory());
    }
    return e;
  }

  inline static Expr simplifyIte (Expr exp)  // simple version, on the syntactic level
  {
    ExprFactory &efac = exp->getFactory();
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    ExprVector commonTerms;
    Expr b1;
    Expr b2;
    bool added = false;
    if (isNumeric(exp->right()))
    {
      getAddTerm(exp->right(), plusOpsLeft);
      getAddTerm(exp->last(), plusOpsRight);

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

      b1 = simplifyPlus(mkplus(plusOpsLeft, efac));
      b2 = simplifyPlus(mkplus(plusOpsRight, efac));
      if (b1 == b2)
      {
        if (lexical_cast<string>(b1) != "0")
          commonTerms.push_back(b1);
        added = true;
      }
    }
    else
    {
      b1 = exp->right();
      b2 = exp->last();
    }

    if (!added) // some redundancy with the ITE-handling in simplifyBool
    {
      if (isOpX<TRUE>(exp->left()))
        commonTerms.push_back(b1);
      else if (isOpX<FALSE>(exp->left()))
        commonTerms.push_back(b2);
      else
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

    if (constLeft != 0) plusOpsLeft.push_back(mkMPZ(constLeft, efac));
    if (constRight != 0) plusOpsRight.push_back(mkMPZ(constRight, efac));

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

    Expr l = mkplus(plusOpsLeft, efac);
    Expr r = mkplus(plusOpsRight, efac);

    // small ITE-optimization; to extend:
    if (isOpX<EQ>(exp) && isOpX<ITE>(l) && isOpX<MPZ>(r) &&
        isOpX<MPZ>(l->right()) && isOpX<MPZ>(l->last()) && l->right() != l->last())
    {
      if (l->right() == r) return l->left();
      if (l->left() == r) return mkNeg(l->left());
    }
    else if (isOpX<EQ>(exp) && isOpX<ITE>(r) && isOpX<MPZ>(l) &&
      isOpX<MPZ>(r->right()) && isOpX<MPZ>(r->last()) && r->right() != r->last())
    {
      if (r->right() == l) return r->left();
      if (r->left() == l) return mkNeg(r->left());
    }

    return reBuildCmp(exp, l, r);
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
      ret = mkMPZ (0, a->getFactory());
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
                if (b->left() == mkMPZ (0, a->getFactory())) {
                  ret = a;
                } else {
                  ret = mk<PLUS>(a,b->left());
                }
              } else

                if (mkMPZ ((-1), a->getFactory()) == b) {
                  ret = simplifiedPlus(a, mkMPZ (1, a->getFactory()));
                } else

                  if (b == mkMPZ (0, a->getFactory())) {
                    ret = a;
                  } else

                    if (a == mkMPZ (0, a->getFactory())){
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
        if (exp->left() == exp->right())
          return mk<TRUE>(efac);

        if (isOpX<TRUE>(exp->right()))
          return mk<TRUE>(efac);

        if (isOpX<FALSE>(exp->right()))
          return mkNeg(exp->left());

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

      if (exp->arity() == 2 && (isOpX<NEQ>(exp) || isOpX<XOR>(exp)))
      {
        if (exp->left() == exp->right())
          return mk<FALSE>(efac);

        if (isOpX<FALSE>(exp->right()))
          return exp->left();

        if (isOpX<FALSE>(exp->left()))
          return exp->right();

        if (isOpX<TRUE>(exp->right()))
        {
          return mkNeg(exp->left());
        }

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
    SimplifyArrExpr () {};

    Expr operator() (Expr exp)
    {
      // GF: to enhance

      if (isOpX<STORE>(exp))
      {
        ExprSet stores;
        getChainOfStores(exp->left(), stores);
        for (auto s : stores)
          if (exp->right() == s->right()) // cell overwritten
            exp = replaceAll(exp, s, s->left());
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

  inline static Expr simplifyArr (Expr exp)
  {
    if (containsOp<FORALL>(exp) || containsOp<EXISTS>(exp)) return exp;
    RW<SimplifyArrExpr> rw(new SimplifyArrExpr());
    return dagVisit (rw, exp);
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

  // helper used in `constantPropagationRec`:
  template<typename Range> static bool contradictionCheck(Expr bc, Expr defVal, Range& hardVars,
                                        ExprSet& cnjs, ExprSet& toInsertHard, ExprMap& repls)
  {
    if (emptyIntersect(bc, hardVars))
    {
      if (repls[bc] == NULL) repls[bc] = defVal;
      else if (repls[bc] != defVal)
      {
        cnjs.clear();
        cnjs.insert(mk<FALSE>(bc->getFactory()));      // contradiction is found, like b /\ ~b
        return true;
      }
      // otherwise, the constraint is already there
    }
    else toInsertHard.insert(isOpX<TRUE>(defVal) ? bc : mk<NEG>(bc));
    return false;
  }

  template<typename Range> static void constantPropagationRec(Range& hardVars, ExprSet& cnjs, ExprMap& repls, bool doArithm)
  {
    ExprSet toInsert, toInsertHard;
    for (auto it = cnjs.begin(); it != cnjs.end(); )
    {
      Expr a = *it;
      if (isOpX<TRUE>(a))
      {
        it = cnjs.erase(it);
        continue;
      }
      if (isOpX<FALSE>(a))
      {
        cnjs.clear();
        cnjs.insert(mk<FALSE>(a->getFactory()));
        return;
      }

      if (isOpX<IMPL>(a))
      {
        Expr lhs = a->left();

        if (isOpX<TRUE>(lhs)) a = a->right();
        else if (isOpX<FALSE>(lhs))
        {
          it = cnjs.erase(it);
          continue;
        }
      }

      if (isOpX<EQ>(a))
      {
        Expr lhs = a->left();
        Expr rhs = a->right();
        if ((isOpX<TRUE>(lhs) && isOpX<TRUE>(rhs)) ||
            (isOpX<FALSE>(lhs) && isOpX<FALSE>(rhs)))
        {
          it = cnjs.erase(it);
          continue;
        }
        else if (isOpX<TRUE>(lhs)) a = rhs;
        else if (isOpX<FALSE>(lhs)) a = mkNeg(rhs);
        else if (isOpX<TRUE>(rhs)) a = lhs;
        else if (isOpX<FALSE>(rhs)) a = mkNeg(lhs);
      }

      if (a->arity() == 2 && (isOpX<NEQ>(a) || isOpX<XOR>(a)))
      {
        Expr lhs = a->left();
        Expr rhs = a->right();
        if ((isOpX<TRUE>(lhs) && isOpX<FALSE>(rhs)) ||
            (isOpX<FALSE>(lhs) && isOpX<TRUE>(rhs)))
        {
          it = cnjs.erase(it);
          continue;
        }
        else if (isOpX<TRUE>(lhs)) a = mkNeg(rhs);
        else if (isOpX<FALSE>(lhs)) a = rhs;
        else if (isOpX<TRUE>(rhs)) a = mkNeg(lhs);
        else if (isOpX<FALSE>(rhs)) a = lhs;
      }

      ExprSet splitted;
      getConj(a, splitted);

      for (auto c : splitted)
      {
        if (isOpX<NEG>(c) && !isBoolConst(c->left()))
          c = mkNeg(c->left());

        if (doArithm && isOpX<EQ>(c))
        {
          Expr cons = NULL;
          Expr rest = NULL;
          if (isNumericConst(c->left()))
          {
            cons = c->left();
            rest = c->right();
          }
          else if (isNumericConst(c->right()))
          {
            cons = c->right();
            rest = c->left();
          }

          if (cons != NULL && IsConst()(rest))
          {
            if (emptyIntersect(rest, hardVars))
            {
              if (repls[rest] == NULL)
                repls[rest] = cons;
              else if (repls[rest] != cons)
              {
                cnjs.clear();
                cnjs.insert(mk<FALSE>(a->getFactory()));     // contradiction is found, like a = 0 /\ a = 1
                return;
              }
            }
            else
              toInsertHard.insert(c);
          }
          else toInsert.insert(c);
        }
        else if (isBoolConst(c))
        {
          if (contradictionCheck(c, mk<TRUE>(a->getFactory()), hardVars, cnjs, toInsertHard, repls))
            return;
        }
        else if (isOpX<NEG>(c) && isBoolConst(c->left()))
        {
          if (contradictionCheck(c->left(), mk<FALSE>(a->getFactory()), hardVars, cnjs, toInsertHard, repls))
            return;
        }
        else
          toInsert.insert(c);
      }

      it = cnjs.erase(it);
    }

    bool toRestart = false;
    for (auto & a : toInsert)
    {
      Expr b = replaceAll(a, repls);
      if (doArithm) b = simplifyArithm(b);
      b = simplifyBool(b);
      if (!toRestart && a != b) toRestart = true;
      cnjs.insert(b);
    }
    cnjs.insert(toInsertHard.begin(), toInsertHard.end());

    if (toRestart)
      constantPropagationRec(hardVars, cnjs, repls, doArithm);
  }

  // simplification based on boolean replacements
  template<typename Range> static void constantPropagation(Range& hardVars, ExprSet& cnjs, bool doArithm = true)
  {
    ExprMap repls;
    constantPropagationRec(hardVars, cnjs, repls, doArithm);
  }

  // simplification based on equivalence classes
  template<typename Range> static Expr simpEquivClasses(Range& hardVars, ExprSet& cnjs, ExprFactory& efac)
  {
    set<ExprVector*> equivs;
    Expr res = conjoin(cnjs, efac);

    // get classes
    for (auto it = cnjs.begin(); it != cnjs.end(); it = cnjs.erase(it))
    {
      Expr e = *it;
      if (isOpX<EQ>(e))
      {
        bool found = false;
        for (auto eq : equivs)
        {
          bool foundLeft = find(eq->begin(), eq->end(), e->left()) != eq->end();
          bool foundRight = find(eq->begin(), eq->end(), e->right()) != eq->end();
          if (foundLeft && !foundRight) { found = true; eq->push_back(e->right()); break; }
          else if (!foundLeft && foundRight) { found = true; eq->push_back(e->left()); break; }
        }
        if (!found)
        {
          ExprVector* n = new ExprVector();
          n->push_back(e->left());
          n->push_back(e->right());
          equivs.insert(n);
        }
      }
    }

    // do rewriting
    bool toRepeat = false;
    ExprSet removed;
    for (auto & eq : equivs)
    {
      Expr hardVar = NULL;
      for (auto & a : hardVars)
      {
        for (auto it = eq->begin(); it != eq->end(); ++it)
          if (contains(*it, a))          // for the case of selects
            { hardVar = *it; break; }
        if (hardVar != NULL) break;
      }

      if (hardVar == NULL) continue;

      for (auto it = eq->begin(); it != eq->end(); ++it)
      {
        ExprVector av;
        filter (*it, IsConst (), inserter(av, av.begin()));
        if (av.size() > 0 && emptyIntersect(av, hardVars) &&    // don't replace constants and hardVars
            emptyIntersect(hardVar, removed) && IsConst()(*it))
        {
          removed.insert(*it);
          res = replaceAll(res, *it, hardVar);
          toRepeat = true;
        }
      }
      free(eq);
    }
    res = simplifyBool(res);
    if (toRepeat)
    {
      getConj(res, cnjs);
      return simpEquivClasses(hardVars, cnjs, efac);
    }
    return res;
  }

  struct SimplifyQuantsExpr
  {
    SimplifyQuantsExpr () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<EXISTS>(exp) || isOpX<FORALL>(exp))
      {
        ExprVector args;
        for (int i = 0; i < exp->arity() - 1; i++)
        {
          Expr v = exp->arg(i);
          if (contains(exp->last(), v))
            args.push_back(v);
        }
        if (args.empty()) return exp->last();
        args.push_back(exp->last());
        if (isOpX<FORALL>(exp)) return mknary<FORALL>(args);
        else return mknary<EXISTS>(args);
      }
      return exp;
    }
  };

  inline static Expr simplifyQuants (Expr exp)
  {
    RW<SimplifyQuantsExpr> rw(new SimplifyQuantsExpr());
    return dagVisit (rw, exp);
  }

  // rewrites v1 to contain v1 \ v2
  template<typename Range> static void minusSets(ExprSet& v1, Range& v2){
    for (auto it = v1.begin(); it != v1.end(); ){
      if (find(v2.begin(), v2.end(), *it) != v2.end())
        it = v1.erase(it);
      else ++it;
    }
  }

  // rewrites v1 to contain only v2
  template<typename Range1, typename Range2> static void keepOnly(Range1& v1, Range2& v2){
    for (auto it = v1.begin(); it != v1.end(); ){
      if (find(v2.begin(), v2.end(), *it) == v2.end())
        it = v1.erase(it);
      else ++it;
    }
  }

  // is v1 a subset of v2?
  template<typename Range1, typename Range2> static bool isSubset(Range1& v1, Range2& v2){
    for (auto it = v1.begin(); it != v1.end(); ++it)
      if (find(v2.begin(), v2.end(), *it) == v2.end())
        return false;
    return true;
  }

  void getQVars (Expr exp, map<Expr, ExprVector>& vars);

  template<typename Range> static Expr weakenForVars(Expr fla, Range& vars)
  {
    ExprSet cnj;
    getConj(fla, cnj);
//    ineqMerger(cnj, true);

    for (auto it = cnj.begin(); it != cnj.end(); )
    {
      ExprVector av;
      filter (*it, bind::IsConst (), inserter(av, av.begin()));
      map<Expr, ExprVector> qv;
      getQVars (*it, qv);
      for (auto & a : qv)
        for (auto & b : a.second)
          for (auto it1 = av.begin(); it1 != av.end(); )
            if (*it1 == b) {
              it1 = av.erase(it1); break; }
            else ++it1;

      if (emptyIntersect(av, vars)) ++it;
      else it = cnj.erase(it);
    }
    return simplifyBool(conjoin(cnj, fla->getFactory()));
  }

  template<typename Range> static Expr weakenForHardVars(Expr fla, Range& vars)
  {
    ExprSet qVars;
    filter (fla, bind::IsConst (), inserter (qVars, qVars.begin()));
    minusSets(qVars, vars);
    return weakenForVars(fla, qVars);
  }

  void getExtraVars(Expr fla, ExprVector& vars, ExprSet& allVars)
  {
    filter (fla, bind::IsConst (), inserter (allVars, allVars.begin()));
    minusSets(allVars, vars);
    map<Expr, ExprVector> qv;
    getQVars (fla, qv);
    for (auto & q : qv) minusSets(allVars, q.second);
  }

  bool hasOnlyVars(Expr fla, ExprVector& vars)
  {
    ExprSet allVars;
    getExtraVars(fla, vars, allVars);
    return allVars.empty();
  }

  template <typename T, typename R> static int getVarIndex(T e, R& vec)
  {
    int i = 0;
    for (auto & v : vec)
    {
      if (v == e) return i;
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
      {
        bool toadd = true;
        for (auto it = terms.begin(); it != terms.end(); )
        {
          if (*it == t)
          {
            terms.erase(it);
            toadd = false;
            break;
          }
          else ++it;
        }
        if (toadd) terms.push_back(additiveInverse(t));
      }
    }
    else if (isOpX<MULT>(a))
    {
      Expr tmp = rewriteMultAdd(a);
      if (tmp == a) terms.push_back(a);
      else getAddTerm(tmp, terms);
    }
    else if (lexical_cast<string>(a) != "0")
    {
      bool found = false;
      for (auto it = terms.begin(); it != terms.end(); )
      {
        if (additiveInverse(*it) == a)
        {
          terms.erase(it);
          found = true;
          break;
        }
        else ++it;
      }
      if (!found) terms.push_back(a);
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

  struct FindNonlinAndRewrite
  {
    ExprVector& vars;
    ExprMap& extraVars;
    bool arrays;

    FindNonlinAndRewrite (ExprVector& _vars, ExprMap& _extraVars, bool _arrays) :
      vars(_vars), extraVars(_extraVars), arrays(_arrays) {};

    Expr operator() (Expr t)
    {
      if (isOpX<MULT>(t))
      {
        // using the communativity of multiplication
        ExprVector ops;
        getMultOps(t, ops);

        ExprVector nonlinPart;
        cpp_int linPart = 1;
        for (auto & a : ops)
        {
          ExprVector av;
          filter (a, IsConst (), inserter(av, av.begin()));
          if (av.size() == 0)
          {
            linPart = linPart * lexical_cast<cpp_int>(a);
            continue;
          }
          for (auto & b : av)
          {
            if (find(vars.begin(), vars.end(), b) == vars.end())
            {
              bool found = false;
              for (auto & c : extraVars) if (c.second == b) { found = true; break; }
              if (! found)
              {
//                errs () << "WARNING. Wrong symbol at " << *t << ".\n";
                return mk<TRUE>(t->getFactory());
              }
            }
          }
          nonlinPart.push_back(a);
        }

        if (linPart == 0) return mkMPZ (0, t->getFactory());
        if (nonlinPart.size() <= 1) return t;

        Expr multedVars = mkmult(nonlinPart, t->getFactory());
        if (extraVars[multedVars] == NULL)
        {
          Expr new_name = mkTerm<string> ("__e__" + to_string(extraVars.size()), t->getFactory());
          Expr var = intConst(new_name);
          extraVars[multedVars] = var;
        }

        if (linPart == 1) return extraVars[multedVars];
        else return mk<MULT>( mkMPZ(linPart, t->getFactory()), extraVars[multedVars]);
      }
      else if (isOpX<MOD>(t) || isOpX<IDIV>(t) || isOpX<DIV>(t) || (arrays && isOpX<SELECT>(t)))
      {
        int indl = getVarIndex(t->left(), vars);
        int indr = getVarIndex(t->right(), vars);

        Expr key = t;
        if (indl >= 0) key = replaceAll(key, t->left(), vars[indl]);
        if (indr >= 0) key = replaceAll(key, t->right(), vars[indr]);

        if (isOpX<MPZ>(t->left()) && lexical_cast<cpp_int>(t->left()) == 0)
          return mkMPZ (0, t->getFactory());

        if (extraVars[key] == NULL)
        {
          Expr new_name = mkTerm<string> ("__e__" + to_string(extraVars.size()), t->getFactory());
          Expr var = intConst(new_name);
          extraVars[key] = var;
        }
        return extraVars[key];
      }
      return t;
    }
  };

  inline static Expr findNonlinAndRewrite (Expr exp, ExprVector& vars, ExprMap& extraVars, bool arrays = false)
  {
    RW<FindNonlinAndRewrite> mu(new FindNonlinAndRewrite(vars, extraVars, arrays));
    return dagVisit (mu, exp);
  }

  struct FindNonlin : public std::unary_function<Expr, VisitAction>
  {
    bool found;

    FindNonlin () : found (false) {}

    VisitAction operator() (Expr exp)
    {
      if (found)
      {
        found = true;
        return VisitAction::skipKids ();
      }
      else if (isOpX<MULT>(exp) || isOpX<MOD>(exp) || isOpX<DIV>(exp) || isOpX<IDIV>(exp))
      {
        int v = 0;
        for (unsigned j = 0; j < exp->arity(); j++)
        {
          Expr q = exp->arg(j);
          if (isIntConst(q)) v++;     // GF: a simple counter, to extend
        }

        if (v > 1)
        {
          found = true;
          return VisitAction::skipKids ();
        }
      }
      return VisitAction::doKids ();
    }
  };

  inline bool findNonlin (Expr e1)
  {
    FindNonlin fn;
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

  inline ExprSet orifyCmpConstraintsSet(ExprSet& es, int bnd = 10)
  {
    assert (es.size() > 0);
    if (es.size() == 1)
    {
      ExprSet newDsjs;
      getDisj(*es.begin(), newDsjs);
      return newDsjs;
    }

    bool toDisj;
    ExprFactory &efac = (*es.begin())->getFactory();
    Expr lhs;
    int lowerBnd = INT_MIN;
    int upperBnd = INT_MAX;
    for (auto & a : es)
    {
      toDisj = false;
      if (!isOp<ComparissonOp>(a)) break;
      if (isOpX<EQ>(a))
      {
        ExprSet newDsjs;
        newDsjs.insert(a);
        return newDsjs;
      }

      if (lhs == NULL) lhs = a->left();
      else
        if (0 != lexical_cast<string>(lhs).compare(lexical_cast<string>(a->left()))) break;

      if (!isOpX<MPZ>(a->right())) break;

      if (isOpX<GEQ>(a)) lowerBnd = max(lowerBnd, lexical_cast<int>(a->right()));
      else if (isOpX<GT>(a)) lowerBnd = max(lowerBnd, lexical_cast<int>(a->right()) + 1);
      else if (isOpX<LEQ>(a)) upperBnd = min(upperBnd, lexical_cast<int>(a->right()));
      else if (isOpX<LT>(a)) upperBnd = min(upperBnd, lexical_cast<int>(a->right()) - 1);

      toDisj = true;
    }

    ExprSet newDsjs;
    if (toDisj)
    {
      for (int i = 0; i < min(bnd, upperBnd - lowerBnd); i++)
      {
        newDsjs.insert(mk<EQ>(lhs, mkTerm (mpz_class (lowerBnd + i), efac)));
      }
      if (upperBnd - lowerBnd > bnd)
      {
        newDsjs.insert(mk<AND>
                (mk<GEQ>(lhs, mkTerm (mpz_class (lowerBnd + bnd), efac)),
                 mk<LEQ>(lhs, mkTerm (mpz_class (upperBnd), efac))));
      }
    }
    else
    {
      newDsjs.insert(conjoin(es, efac));
    }
    return newDsjs;
  }

  Expr projectITE(Expr ite, Expr var)
  {
    if (isOpX<ITE>(ite))
    {
      return mk<ITE>(ite->arg(0), projectITE(ite->arg(1), var), projectITE(ite->arg(2), var));
    }
    else
    {
      ExprSet cnjs;
      getConj(ite, cnjs);
      for (auto & a : cnjs)
      {
        if (a->left() == var) return a->right();
        else if (a->right() == var) return a->left();
      }

      assert(0);
    }
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
    if (disjs.size() <= 1)
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
    if (isIntConst(var))
      return intConst(new_name);
    else if (isRealConst(var))
      return realConst(new_name);
    else if (isBoolConst(var))
      return boolConst(new_name);
    else if (isConst<ARRAY_TY> (var))
      return mkConst(new_name, mk<ARRAY_TY> (
             mk<INT_TY> (new_name->getFactory()),
             mk<INT_TY> (new_name->getFactory()))); // GF: currently, only Arrays over Ints

    else return NULL;
  }

  inline static void cloneVector(ExprVector& src, ExprVector& dst, string new_prefix)
  {
    assert (dst.empty());
    for (int i = 0; i < src.size(); i++)
    {
      Expr new_name = mkTerm<string> (new_prefix + lexical_cast<string>(src[i]), src[i]->getFactory());
      dst.push_back(cloneVar(src[i], new_name));
    }
  }

  inline static bool isBool(Expr e)
  {
    return typeOf(e) == mk<BOOL_TY>(e->getFactory());
  }

  inline Expr rewriteDivConstraints(Expr fla)
  {
    // heuristic for the divisibility constraints
    assert (isOp<ComparissonOp>(fla));
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getAddTerm(fla->left(), plusOpsLeft);
    getAddTerm(fla->right(), plusOpsRight);
    Expr lhs = NULL;
    for (auto & a : plusOpsRight) plusOpsLeft.push_back(additiveInverse(a));
    plusOpsRight.clear();
    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      if (isOpX<IDIV>(*it1))
      {
        lhs = *it1;
        plusOpsLeft.erase(it1);
        for (auto & a : plusOpsLeft) plusOpsRight.push_back(additiveInverse(a));
        break;
      }
      if (isOpX<UN_MINUS>(*it1) && isOpX<IDIV>((*it1)->left()))
      {
        lhs = (*it1)->left();
        plusOpsLeft.erase(it1);
        for (auto & a : plusOpsLeft) plusOpsRight.push_back(a);
        break;
      }
      ++it1;
    }

    if (lhs == NULL) return fla;
    Expr rhs = mkplus(plusOpsRight, fla->getFactory());

    if (isOpX<EQ>(fla))
      return mk<AND>(mk<GEQ>(lhs->left(), mk<MULT>(lhs->right(), rhs)),
        mk<GT>(mk<PLUS> (mk<MULT>(lhs->right(), rhs), lhs->right()), lhs->left()));
    else if (isOpX<NEQ>(fla))
      return mk<OR>(mk<GT>(mk<MULT>(lhs->right(), rhs), lhs->left()),
        mk<GEQ>(lhs->left(), mk<PLUS> (mk<MULT>(lhs->right(), rhs), lhs->right())));
    return fla;
  }

  inline Expr rewriteModConstraints(Expr fla)
  {
    // heuristic for the divisibility constraints
    assert (isOp<ComparissonOp>(fla));
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getAddTerm(fla->left(), plusOpsLeft);
    getAddTerm(fla->right(), plusOpsRight);
    Expr lhs = NULL;
    for (auto & a : plusOpsRight) plusOpsLeft.push_back(additiveInverse(a));
    plusOpsRight.clear();
    cpp_int c1, c2;
    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      if (isOpX<MOD>(*it1))
      {
        Expr d = simplifyArithm((*it1)->last());
        if (isNumericConst(d))
        {
          lhs = replaceAll(*it1, (*it1)->last(), d);
          c1 = lexical_cast<cpp_int>(d);
          plusOpsLeft.erase(it1);
          for (auto & a : plusOpsLeft) plusOpsRight.push_back(additiveInverse(a));
          plusOpsLeft.clear();
          break;
        }
      }
      ++it1;
    }
    if (!plusOpsLeft.empty() || lhs == NULL) return fla;

    Expr rhs = mkplus(plusOpsRight, fla->getFactory());
    rhs = simplifyArithm(rhs);
    if (isNumericConst(rhs)) c2 = lexical_cast<cpp_int>(rhs);
    else return fla;

    ExprSet dsjs;
    for (auto i = 0; i < c1; i++)
      if (evaluateCmpConsts(fla, i, c2))
        dsjs.insert(mk<EQ>(lhs, mkMPZ(i, fla->getFactory())));

    fla = disjoin(dsjs, fla->getFactory());
    return fla;
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
      if (isBool(lhs)) return
          mk<OR>(mk<AND>(lhs, rhs),
                 mk<AND>(mkNeg(lhs), mkNeg(rhs)));
      else if (isNumeric(lhs)) {
        // heuristic for the divisibility constraints
        if (isOpX<IDIV>(rhs) || isOpX<IDIV>(lhs)) {
          return rewriteDivConstraints(fla);
        }
        else
          return mk<AND>(mk<GEQ>(lhs, rhs), mk<GEQ>(rhs, lhs));
      }
      else return fla;
    }

    if (isOpX<NEQ>(fla))
    {
      if (isBool(lhs)) return
          mk<OR>(mk<AND>(lhs, mkNeg(rhs)),
                 mk<AND>(mkNeg(lhs), rhs));
      else  if (isNumeric(lhs)) {
        if (isOpX<IDIV>(rhs) || isOpX<IDIV>(lhs)) {
          return rewriteDivConstraints(fla);
        }
        else return mk<OR>(
          mk<GT>(lhs, rhs), mk<GT>(rhs, lhs));
      }
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
    if (isOpX<ITE>(term) && isBool (term->last()))
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

  struct SelectStoreRewriterHelpRepairer
  {
    Expr ind;
    ExprFactory& efac;
    SelectStoreRewriterHelpRepairer (Expr _ind) :
      ind(_ind), efac(ind->getFactory()) {};

    Expr operator() (Expr exp)
    {
      if (isOpX<EQ>(exp) && isOpX<SELECT>(exp->right()))
      {
        Expr cmp = simplifyCmp(mk<EQ>(ind, exp->right()->right()));
        return simplifyIte(mk<ITE>(cmp,
          mk<TRUE>(efac), exp));
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

      // to avoid this, try unfoldITE first
      if (containsOp<ITE>(exp)) return exp;

      Expr sel, val;
      if (isOpX<EQ>(exp))
      {
        if (isOpX<STORE>(exp->right())) { sel = exp->right(); val = exp->left(); }
        if (isOpX<STORE>(exp->left()))  { sel = exp->left(); val = exp->right(); }
      }

      if (sel != NULL)
      {
        Expr main = mk<EQ>(sel->last(), mk<SELECT>(val, sel->right()));
        if (containsOp<STORE>(sel->left()))
        {
          Expr nested = rewriteSelectStore(mk<EQ>(val, sel->left()));
          RW<SelectStoreRewriterHelpRepairer>
              a(new SelectStoreRewriterHelpRepairer(sel->right()));
          return mk<AND>(dagVisit (a, nested), main);
        }
        return main;
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
        Expr repl = intConst(mkTerm<string> ("sel_" + lexical_cast<string>(sels.size()), exp->getFactory()));
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
          vars.insert(fapp(exp->arg(i)));
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

  template<typename Range> static Expr mkQFla (Expr def, Range& vars, bool forall = true)
  {
    if (vars.empty()) return def;
    ExprVector args;
    for (auto & a : vars) args.push_back(a->last());
    args.push_back(def);
    if (forall) return mknary<FORALL>(args);
    else return mknary<EXISTS>(args);
  }

  // rewrite just equalities
  template<typename Range> static Expr simpleQE(Expr exp, Range& quantified)
  {
    ExprFactory& efac = exp->getFactory();
    ExprSet cnjsSet, dsjsSet;
    getDisj(exp, dsjsSet);
    if (dsjsSet.size() > 1)
    {
      ExprSet newDsjs;
      for (auto & d : dsjsSet) newDsjs.insert(simpleQE(d, quantified));
      return disjoin(newDsjs, efac);
    }
    getConj(exp, cnjsSet);
    ExprVector cnjs;
    cnjs.insert(cnjs.end(), cnjsSet.begin(), cnjsSet.end());
    for (auto & var : quantified)
    {
      ExprSet eqs;
      Expr store; // todo: extend to ExprSet

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
              mkMPZ (0, efac)));
          normalized = ineqSimplifier(var, normalized);
        }
        else if (var == normalized->right())
        {
          normalized = mk<EQ>(var, normalized->left());
        }

        // after the normalization, var can be eliminated
        if (!isOpX<EQ>(normalized) || !contains(normalized, var))
          { it++; continue;}

        if (var == normalized->left())
        {
          eqs.insert(normalized->right());
          cnjs.erase (cnjs.begin()+it);
          continue;
        }
        else if (isOpX<MULT>(normalized->left()) && isOpX<MPZ>(normalized->left()->left()))
        {
          cnjs.push_back(mk<EQ>(mk<MOD>(normalized->right(), normalized->left()->left()),
                             mkMPZ (0, efac)));
        }
        else { it++; continue;}

        if (store == NULL && containsOp<STORE>(normalized) && isOpX<EQ>(normalized) &&
            emptyIntersect(normalized->left(), quantified) &&
            isOpX<STORE>(normalized->right()) && var == normalized->right()->left()) {
          // one level of storing (to be extended)
          store = normalized;
        }

//        errs() << "WARNING: COULD NOT NORMALIZE w.r.t. " << *var << ": "
//               << *normalized << "     [[  " << *cnj << "  ]]\n";

        cnjs[it] = normalized;
        it++;
      }

      if (store != NULL) {
        // assume "store" = (A = store(var, x, y))
        for (unsigned it = 0; it < cnjs.size(); it++) {
          ExprVector se;
          filter (cnjs[it], IsSelect (), inserter(se, se.begin()));
          for (auto s : se) {
            if (contains(store, s)) continue;
            if (s->left() == var) {
              Expr cmp = simplifyCmp(mk<EQ>(store->right()->right(), s->right()));
              cnjs[it] = replaceAll(cnjs[it], s, simplifyIte(
                         mk<ITE>(cmp,
                                 store->right()->last(),
                                 mk<SELECT>(store->left(), s->right()))));
            }
          }
        }
      }

      if (eqs.empty()) continue;

      Expr repl = *eqs.begin();
      bool no_qv = emptyIntersect(repl, quantified);
      int min_sz = treeSize(repl);
      int is_const = isOpX<MPZ>(repl);

      // first, search for a non-constant replacement without quantified vars, if possible
      for (auto cnj = std::next(eqs.begin()); cnj != eqs.end(); cnj++) {
        bool no_qv_cur = emptyIntersect(*cnj, quantified);
        int sz_cur = treeSize(*cnj);
        int is_const_cur = isOpX<MPZ>(*cnj);
        if (no_qv < no_qv_cur || (no_qv_cur && is_const) || (sz_cur < min_sz && !is_const_cur)) {
          repl = *cnj;
          min_sz = sz_cur;
          no_qv = no_qv_cur;
          is_const = is_const_cur;
        }
      }

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
    return dagVisit (a, unfoldITE(simplifyArr(exp)));
  }

  inline void getNondets (Expr e, std::map<Expr, ExprSet>& nondets)
  {
    ExprSet lin;
    getConj(e, lin);
    std::map<Expr, ExprSet> constraints;
    for (auto & a : lin)
    {
      if (isOpX<GT>(a) || isOpX<LT>(a) || isOpX<GEQ>(a) || isOpX<LEQ>(a) || isOpX<ITE>(a) || isOpX<OR>(a))
      {
        ExprVector av;
        filter (a, bind::IsConst (), inserter(av, av.begin()));
        if (av.size() == 0 || av.size() > 1) continue;
        // current limitation: only nondeterminism w.r.t. one variable; to extend

        Expr a1 = (unfoldITE(a));
        a1 = simplifyBool(a1);
        getConj(a1, constraints[*av.begin()]);
      }
    }

    for (auto & a : constraints){
      nondets[a.first] = orifyCmpConstraintsSet(a.second);
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
    else if (isIntConst(term)) {
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
                   mkMPZ (0, efac)));
      tmp = ineqReverter(tmp);

      if (isOpX<TRUE>(tmp)) continue;
      if (isOpX<FALSE>(tmp)) return tmp;

      newCnjs.insert(tmp);
      lin_coms.insert(tmp->arg(0));
    }

    if (lin_coms.size() == 0)
    {
      if (!keep_redundand) ineqMerger(cnjs, true);
      return conjoin(cnjs, efac);
    }

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
                newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_min_le, efac)));
              it = all_diseqs.erase(it);
            } else if (*it > cur_min_le) { // remove redundand, e.g., (x != 7 /\ x <= 5)
              if (keep_redundand)
                newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (*it, efac)));
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
                newCnjs.insert(mk<LT>(lin_com, mkMPZ (cur_min_lt, efac)));
              it = all_diseqs.erase(it);
            } else if (*it >= cur_min_lt) {  // remove redundand, e.g., (x != 5 /\ x < 5)
              if (keep_redundand)
                newCnjs.insert(mk<LT>(lin_com, mkMPZ (*it, efac)));
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
                newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_max_ge, efac)));
              it = all_diseqs.erase(it);
            } else if (*it < cur_max_ge) { // remove redundand, e.g., (x != 4 /\ x >= 5)
              if (keep_redundand)
                newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (*it, efac)));
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
                newCnjs.insert(mk<GT>(lin_com, mkMPZ (cur_max_gt, efac)));
              it = all_diseqs.erase(it);
            } else if (*it <= cur_max_gt) { // remove redundand, e.g., (x != 5 /\ x > 5)
              if (keep_redundand)
                newCnjs.insert(mk<GT>(lin_com, mkMPZ (*it, efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_gt) break;
        }

      for (auto c : all_diseqs) {
        newCnjs.insert (mk<NEQ>(lin_com, mkMPZ (c, efac)));
      }

      if ((cur_max_gt_bl && cur_min_lt_bl && cur_max_gt >= cur_min_lt - 1) || // e.g., (x > 3 /\ x < 4)
          (cur_max_ge_bl && cur_min_lt_bl && cur_max_ge >= cur_min_lt) ||
          (cur_max_gt_bl && cur_min_le_bl && cur_max_gt >= cur_min_le) ||
          (cur_max_ge_bl && cur_min_le_bl && cur_max_ge >= cur_min_le + 1))
        return mk<FALSE>(efac);

      if (cur_max_ge_bl && cur_min_le_bl && cur_max_ge == cur_min_le && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_min_le, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_gt_bl && cur_min_le_bl && cur_max_gt + 1 == cur_min_le && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_min_le, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_ge_bl && cur_min_lt_bl && cur_max_ge + 1 == cur_min_lt && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_max_ge, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_gt_bl && cur_min_lt_bl && cur_max_gt + 2 == cur_min_lt && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_max_gt + 1, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_min_le_bl && cur_min_lt_bl) {
        if (cur_min_le >= cur_min_lt) {
          newCnjs.insert(mk<LT>(lin_com, mkMPZ (cur_min_lt, efac)));
        }
        else {
          newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_min_le, efac)));
        }
      }
      else {
        if (cur_min_le_bl) {
          newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_min_le, efac)));
        }
        if (cur_min_lt_bl) {
          newCnjs.insert(mk<LT>(lin_com, mkMPZ (cur_min_lt, efac)));
        }
      }

      if (cur_max_ge_bl && cur_max_gt_bl) {
        if (cur_max_ge <= cur_max_gt) {    // e.g., x > 5 /\ x >= 5
          newCnjs.insert(mk<GT>(lin_com, mkMPZ (cur_max_gt, efac)));
        }
        else {
          newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_max_ge, efac)));
        }
      }
      else {
        if (cur_max_ge_bl) {
          newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_max_ge, efac)));
        }
        if (cur_max_gt_bl) {
          newCnjs.insert(mk<GT>(lin_com, mkMPZ (cur_max_gt, efac)));
        }
      }
    }

    if (!keep_redundand) ineqMerger(newCnjs, true);
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
          reBuildCmp(d, mk<PLUS>(d->arg(0), additiveInverse(d->arg(1))), mkMPZ (0, efac)));

      if (isOpX<TRUE>(tmp)) return tmp;
      if (isOpX<FALSE>(tmp)) continue;

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
                newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_max_le, efac)));
              it = all_eqs.erase(it);
            } else if (*it <= cur_max_le) { // remove redundand, e.g., (x = 3 \/ x <= 5)
              if (keep_redundand)
                newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (*it, efac)));
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
                newDsjs.insert(mk<LT>(lin_com, mkMPZ (cur_max_lt, efac)));
              it = all_eqs.erase(it);
            } else if (*it < cur_max_lt) {  // remove redundand, e.g., (x = 4 \/ x < 5)
              if (keep_redundand)
                newDsjs.insert(mk<LT>(lin_com, mkMPZ (*it, efac)));
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
                newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_min_ge, efac)));
              it = all_eqs.erase(it);
            } else if (*it >= cur_min_ge) { // remove redundand, e.g., (x = 9 \/ x >= 5)
              if (keep_redundand)
                newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (*it, efac)));
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
                newDsjs.insert(mk<GT>(lin_com, mkMPZ (cur_min_gt, efac)));
              it = all_eqs.erase(it);
            } else if (*it > cur_min_gt) { // remove redundand, e.g., (x = 6 \/ x > 5)
              if (keep_redundand)
                newDsjs.insert(mk<GT>(lin_com, mkMPZ (*it, efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_gt) break;
        }

      for (auto c : all_eqs) {
        newDsjs.insert (mk<EQ>(lin_com, mkMPZ (c, efac)));
      }

      if ((cur_min_gt_bl && cur_max_lt_bl && cur_min_gt <= cur_max_lt - 1) ||
          (cur_min_ge_bl && cur_max_lt_bl && cur_min_ge <= cur_max_lt) ||
          (cur_min_gt_bl && cur_max_le_bl && cur_min_gt <= cur_max_le) ||
          (cur_min_ge_bl && cur_max_le_bl && cur_min_ge <= cur_max_le + 1))
        return mk<TRUE>(efac);

      if (cur_min_gt_bl && cur_max_lt_bl && cur_min_gt == cur_max_lt && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_max_lt, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_ge_bl && cur_max_lt_bl && cur_min_ge - 1 == cur_max_lt && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_max_lt, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_gt_bl && cur_max_le_bl && cur_min_gt - 1 == cur_max_le && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_min_gt, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_ge_bl && cur_max_le_bl && cur_min_ge - 2 == cur_max_le && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_min_ge - 1, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_max_le_bl && cur_max_lt_bl) {
        if (cur_max_le >= cur_max_lt) {
          newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_max_le, efac)));
        }
        else {
          newDsjs.insert(mk<LT>(lin_com, mkMPZ (cur_max_lt, efac)));
        }
      }
      else {
        if (cur_max_le_bl) {
          newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_max_le, efac)));
        }
        if (cur_max_lt_bl) {
          newDsjs.insert(mk<LT>(lin_com, mkMPZ (cur_max_lt, efac)));
        }
      }

      if (cur_min_ge_bl && cur_min_gt_bl) {
        if (cur_min_ge <= cur_min_gt) {
          newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_min_ge, efac)));
        }
        else {
          newDsjs.insert(mk<GT>(lin_com, mkMPZ (cur_min_gt, efac)));
        }
      }
      else {
        if (cur_min_ge_bl) {
          newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_min_ge, efac)));
        }
        if (cur_min_gt_bl) {
          newDsjs.insert(mk<GT>(lin_com, mkMPZ (cur_min_gt, efac)));
        }
      }
    }

    return disjoin(newDsjs, efac);
  }

  inline static Expr normalizeAtom(Expr fla, ExprVector& intVars)
  {
    if (isOp<ComparissonOp>(fla) && isNumeric(fla->left()))
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
          if (!contains(*it, v)) { ++it; continue; }
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
        if (coef != 0) newlhs.insert(mk<MULT>(mkMPZ(coef, fla->getFactory()), v));
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
        Expr c = mkMPZ (-intconst, fla->getFactory());
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

  inline static Expr normalize(Expr fla)
  {
    ExprVector vars;
    filter (fla, IsConst (), inserter(vars, vars.begin()));
    if (isOpX<AND>(fla) || isOpX<OR>(fla))
    {
      ExprSet args;
      for (int i = 0; i < fla->arity(); i++){
        args.insert(normalizeAtom(fla->arg(i), vars));
      }

      return simplifyBool(isOpX<AND>(fla) ? conjoin (args, fla->getFactory()) :
        disjoin (args, fla->getFactory()));
    }
    return normalizeAtom(fla, vars);
  }

  inline static bool getLinCombCoefs(Expr ex, set<cpp_int>& intCoefs)
  {
    bool res = true;
    if (isOpX<TRUE>(ex)) return false;
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        res = res && getLinCombCoefs(*it, intCoefs);
    }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      if (!isOpX<MPZ>(ex->right())) return false;
      ExprVector addt;
      getAddTerm (ex->left(), addt);
      for (auto & t : addt)
      {
        if (isOpX<MULT>(t) && t->arity() == 2 &&
            isOpX<MPZ>(t->left()) && !isOpX<MPZ>(t->right()))
          intCoefs.insert(lexical_cast<cpp_int> (t->left()));
        else return false;
      }
    }
    return res;
  }

  inline static bool getLinCombConsts(Expr ex, set<cpp_int>& intConsts)
  {
    if (isOpX<OR>(ex))
    {
      bool res = true;
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        res &= getLinCombConsts(*it, intConsts);
      return res;
    }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      if (isOpX<MPZ>(ex->right()))
        intConsts.insert(lexical_cast<cpp_int> (ex->right()));
      else
        return false;
    }
    return true;
  }

  inline static void normalizeSelects(Expr& body)
  {
    ExprVector se;
    filter (body, IsSelect (), inserter(se, se.begin()));
    for (auto & s : se)
    {
      if (!isIntConst(s->right()))
      {
        Expr var_it = intConst(mkTerm<string> ("it_" + lexical_cast<string>(&s), body->getFactory()));
        body = mk<AND>(replaceInSubexpr(body, s, s->right(), var_it), mk<EQ>(s->right(), var_it));
      }
    }
  }

  inline static void uniqueizeSelects(Expr& body)
  {
    ExprVector se;
    filter (body, IsSelect (), inserter(se, se.begin()));
    if (se.size() < 2) return;

    ExprSet seenIterators;
    for (auto & s : se)
    {
      if (find(seenIterators.begin(), seenIterators.end(), s->right()) == seenIterators.end())
      {
        seenIterators.insert(s->right());
      }
      else
      {
        Expr var_it = intConst(mkTerm<string> ("it_" + lexical_cast<string>(&s), body->getFactory()));
        body = mk<AND>(replaceInSubexpr(body, s, s->right(), var_it), mk<EQ>(s->right(), var_it));
      }
    }
  }

  inline static bool isSymmetric (Expr exp)
  {
    return isOpX<EQ>(exp);
  }

  Expr processNestedStores (Expr exp, ExprSet& cnjs)
  {
    // TODO: double check if cells are overwritten
    Expr arrVar = exp->left();
    if (isOpX<STORE>(arrVar)) arrVar = processNestedStores(arrVar, cnjs);
    Expr indVar = exp->right();
    Expr valVar = exp->last();
    cnjs.insert(mk<EQ>(mk<SELECT>(arrVar, indVar), valVar));
    return arrVar;
  }

  struct TransitionOverapprox
  {
    ExprVector& srcVars;
    ExprVector& dstVars;

    TransitionOverapprox (ExprVector& _srcVars, ExprVector& _dstVars):
      srcVars(_srcVars), dstVars(_dstVars) {};

    Expr operator() (Expr exp)
    {
      if (isOp<ComparissonOp>(exp) && !containsOp<ITE>(exp))
      {
        ExprSet tmp;
        if (isOpX<STORE>(exp->left()))
        {
          processNestedStores(exp->left(), tmp);
          return conjoin(tmp, exp->getFactory());
        }
        else if (isOpX<STORE>(exp->right()))
        {
          processNestedStores(exp->right(), tmp);
          return conjoin(tmp, exp->getFactory());
        }

        ExprVector av;
        filter (exp, IsConst (), inserter(av, av.begin()));
        if (!emptyIntersect(av, srcVars) && !emptyIntersect(av, dstVars))
          return mk<TRUE>(exp->getFactory());
      }
      else if (isOpX<OR>(exp))
      {
        ExprSet newDsjs;
        for (unsigned i = 0; i < exp->arity (); i++)
        {
          ExprSet cnjs;
          getConj(exp->arg(i), cnjs);
          map<Expr, bool> sels;
          bool allselects = true;
          bool noselects = true;
          for (auto & a : cnjs)
          {
            sels[a] = containsOp<SELECT>(a);
            if (sels[a]) noselects = false;
            else allselects = false;
          }
          if (!noselects && ! allselects)
          {
            ExprSet newCnjs;
            for (auto & a : cnjs)
              if (sels[a]) newCnjs.insert(a);
            newDsjs.insert(conjoin(newCnjs,exp->getFactory()));
          }
        }
        return disjoin(newDsjs,exp->getFactory());
      }
      return exp;
    }
  };

  // opposite to TransitionOverapprox
  struct TransitionMiner : public std::unary_function<Expr, VisitAction>
  {
    ExprVector& srcVars;
    ExprVector& dstVars;
    ExprSet& transitions;

    TransitionMiner (ExprVector& _srcVars, ExprVector& _dstVars, ExprSet& _transitions):
      srcVars(_srcVars), dstVars(_dstVars), transitions(_transitions) {};

    VisitAction operator() (Expr exp)
    {
      if (isOp<ComparissonOp>(exp) && !containsOp<ITE>(exp))
      {
        ExprVector av;
        filter (exp, IsConst (), inserter(av, av.begin()));
        if (!emptyIntersect(av, srcVars) && !emptyIntersect(av, dstVars))
        {
          transitions.insert(exp);
        }
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  struct BoolEqRewriter
  {
    BoolEqRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<EQ>(exp))
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();
        if (isBoolConst(lhs) || isBoolConst(rhs) ||
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

  struct CondRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& conds;

    CondRetriever (ExprSet& _conds) :  conds(_conds) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<ITE>(exp) && !containsOp<ITE>(exp->arg(0)))
      {
        conds.insert(exp->arg(0));
      }
      return VisitAction::doKids ();
    }
  };

  struct AccessRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& accs;

    AccessRetriever (ExprSet& _accs) :  accs(_accs) {};

    VisitAction operator() (Expr exp)
    {
      if ((isOpX<SELECT>(exp) || isOpX<STORE>(exp)) && !containsOp<ARRAY_TY>(exp->right()))
      {
        accs.insert(exp->right());
      }
      return VisitAction::doKids ();
    }
  };

  struct DeltaRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprVector& srcVars;
    ExprVector& dstVars;
    ExprSet& deltas;

    DeltaRetriever (ExprVector& _srcVars, ExprVector& _dstVars, ExprSet& _deltas):
    srcVars(_srcVars), dstVars(_dstVars), deltas(_deltas) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<EQ>(exp))
      {
        ExprVector av;
        filter (exp, IsConst (), inserter(av, av.begin()));
        if (av.size() != 2) return VisitAction::skipKids ();;
        for (int i = 0; i < srcVars.size(); i++)
        {
          if ((av[0] == srcVars[i] && av[1] == dstVars[i]) ||
              (av[1] == srcVars[i] && av[0] == dstVars[i]))
          {
            set<cpp_int> coefs;
            exp = normalizeAtom(exp, av);
            if (!getLinCombCoefs(exp, coefs)) continue;

            bool success = true;
            for (auto i : coefs) success = success && (i == -1 || i == 1);
            if (success)
            {
              Expr cExpr = exp->right();
              cpp_int c = abs(lexical_cast<cpp_int>(cExpr));
              if (c > 1)
                for (int j = 0; j < 2 /*c*/; j++) // GF: for large c it gives many cands
                  deltas.insert(mk<EQ>(mk<MOD>(
                    srcVars[i],
                      mkMPZ(c, exp->getFactory())),
                      mkMPZ ((j), exp->getFactory())));
            }
          }
        }
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline Expr rewriteBoolEq (Expr exp)
  {
    RW<BoolEqRewriter> tr(new BoolEqRewriter());
    return dagVisit (tr, exp);
  }

  inline void retrieveDeltas (Expr exp, ExprVector& srcVars, ExprVector& dstVars, ExprSet& deltas)
  {
    DeltaRetriever dr (srcVars, dstVars, deltas);
    dagVisit (dr, exp);
  }

  inline void retrieveConds (Expr exp, ExprSet& conds)
  {
    CondRetriever dr (conds);
    dagVisit (dr, exp);
  }

  inline void retrieveAccFuns (Expr exp, ExprSet& accs)
  {
    AccessRetriever dr (accs);
    dagVisit (dr, exp);
  }

  inline void retrieveTransitions (Expr exp, ExprVector& srcVars, ExprVector& dstVars, ExprSet& transitions)
  {
    TransitionMiner trm (srcVars, dstVars, transitions);
    dagVisit (trm, exp);
  }

  inline static Expr overapproxTransitions (Expr exp, ExprVector& srcVars, ExprVector& dstVars)
  {
    RW<TransitionOverapprox> rw(new TransitionOverapprox(srcVars, dstVars));
    return dagVisit (rw, exp);
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

  bool isNonlinear(Expr e) {
    int arity = e->arity();
    if (isOpX<MOD>(e) || isOpX<DIV>(e) || isOpX<IDIV>(e)) {
      ExprVector av;
      filter (e->right(), IsConst (), inserter(av, av.begin()));
      if (av.size() > 0) return true;
      else return isNonlinear(e->left());
    }
    else if (isOpX<MULT>(e))
    {
      int numVars = 0;
      for (int i = 0; i < arity; i++)
      {
        if (isNonlinear(e->arg(i))) return true;
        ExprVector av;
        filter (e->arg(i), IsConst (), inserter(av, av.begin()));
        if (av.size() > 0) numVars++;
      }
      return (numVars > 1);
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
          vars[exp].push_back(fapp(exp->arg(i)));

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
      if (isBVar(exp)) return vars[bvarId(exp)];
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
            ineqs.insert(mk<LEQ>(c->right(), mkMPZ (lexical_cast<cpp_int>(c->left())-1, exp->getFactory())));
          else if(isOpX<MPZ>(c->right()))
            ineqs.insert(mk<LEQ>(mkMPZ (lexical_cast<cpp_int>(c->right())+1, exp->getFactory()), c->left()));
          else
            ineqs.insert(mk<LEQ>(c->right(), mk<MINUS>(c->left(), mkMPZ (1, exp->getFactory()))));
        }
        else if (isOpX<LT>(c))
        {
          if (isOpX<MPZ>(c->left()))
            ineqs.insert(mk<LEQ>(mkMPZ (lexical_cast<cpp_int>(c->left())+1, exp->getFactory()), c->right()));
          else if(isOpX<MPZ>(c->right()))
            ineqs.insert(mk<LEQ>(c->left(), mkMPZ (lexical_cast<cpp_int>(c->right())-1, exp->getFactory())));
          else
            ineqs.insert(mk<LEQ>(c->left(), mk<MINUS>(c->right(), mkMPZ (1, exp->getFactory()))));
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

  inline static void simplifyPropagate (ExprSet& cnj)
  {
    bool toRepeat = false;
    map<Expr, ExprSet> vars;
    for (auto & a : cnj)
    {
      filter (a, IsConst (), inserter(vars[a], vars[a].begin()));
    }

    vector<ExprSet::iterator> tmp;
    ExprSet newCnjs;

    for (auto it0 = cnj.begin(); it0 != cnj.end(); ++it0)
    {
      if (find(tmp.begin(), tmp.end(), it0) != tmp.end()) continue;
      Expr a = *it0;
      for (auto it = cnj.begin(); it != cnj.end(); ++it)
      {
        Expr b = *it;
        if (a == b) continue;

        if (contains(b, a))
        {
          if (find(tmp.begin(), tmp.end(), it) != tmp.end())
          {
            toRepeat = true;
            continue;
          }
          newCnjs.insert(simplifyBool(replaceAll(b, a, mk<TRUE>(a->getFactory()))));
          tmp.push_back(it);
          continue;
        }

        ExprSet& av = vars[a];
        ExprSet& bv = vars[b];
        if (av.size() != 2 ||
            !isOpX<EQ>(a) ||
            !isSubset(av, bv)) continue;

        for (auto v : av)
        {
          Expr t = ineqMover(a, v);
          if (t->left() == v)
          {
            if (find(tmp.begin(), tmp.end(), it) != tmp.end())
            {
              toRepeat = true;
              continue;
            }
            newCnjs.insert(simplifyBool(simplifyArithm(replaceAll(b, t->left(), t->right()))));
            tmp.push_back(it);
            break;
          }
        }
      }
    }

    for (auto & it : tmp) cnj.erase(it);
    cnj.insert(newCnjs.begin(), newCnjs.end());
    if (toRepeat) simplifyPropagate(cnj);
  }

  void getLiterals (Expr exp, ExprSet& lits)
  {
    ExprFactory& efac = exp->getFactory();
    if (isOpX<EQ>(exp) && isNumeric(exp->left()) && !containsOp<MOD>(exp))
    {
      getLiterals(mk<GEQ>(exp->left(), exp->right()), lits);
      getLiterals(mk<LEQ>(exp->left(), exp->right()), lits);
    }
    else if (isOpX<NEQ>(exp) && isNumeric(exp->left()) && !containsOp<MOD>(exp))
    {
      getLiterals(mk<GT>(exp->left(), exp->right()), lits);
      getLiterals(mk<LT>(exp->left(), exp->right()), lits);
    }
    else if ((isOpX<EQ>(exp) || isOpX<NEQ>(exp) || isOpX<XOR>(exp)) && isBoolean(exp->left()))
    {
      getLiterals(exp->left(), lits);
      getLiterals(exp->right(), lits);
      getLiterals(mkNeg(exp->left()), lits);
      getLiterals(mkNeg(exp->right()), lits);
    }
    else if (isOpX<NEG>(exp))
    {
      if (bind::isBoolConst(exp->left()))
        lits.insert(exp);
      else
        getLiterals(mkNeg(exp->left()), lits);
    }
    else if (isOpX<IMPL>(exp))
    {
      getLiterals(mkNeg(exp->left()), lits);
      getLiterals(exp->right(), lits);
    }
    else if (isOpX<IFF>(exp))
    {
      getLiterals(mkNeg(exp->left()), lits);
      getLiterals(exp->right(), lits);
      getLiterals(mkNeg(exp->right()), lits);
      getLiterals(exp->left(), lits);
    }
    else if (bind::typeOf(exp) == mk<BOOL_TY>(efac) &&
        !containsOp<AND>(exp) && !containsOp<OR>(exp))
    {
      if (isOp<ComparissonOp>(exp))
      {
        exp = rewriteDivConstraints(exp);
        exp = rewriteModConstraints(exp);
        if (isOpX<AND>(exp) || isOpX<OR>(exp))
          getLiterals(exp, lits);
        else lits.insert(exp);
      }
      else lits.insert(exp);
    }
    else if (isOpX<AND>(exp) || isOpX<OR>(exp))
    {
      for (int i = 0; i < exp->arity(); i++)
        getLiterals(exp->arg(i), lits);
    }
    else if (!isOpX<TRUE>(exp) && !isOpX<FALSE>(exp))
    {
      errs () << "unable lit: " << *exp << "\n";
      assert(0);
    }
  }

  void pprint(Expr exp, int inden = 0, bool upper = true)
  {
    ExprSet flas;
    if (isOpX<FORALL>(exp) || isOpX<EXISTS>(exp))
    {
      outs() << string(inden, ' ') << (isOpX<FORALL>(exp) ? "[forall (" : "[exists (");
      int i = 0;
      for (; i < exp->arity() - 1; i++) outs () << fapp(exp->arg(i)) << " ";
      outs () << ")\n";
      pprint(exp->arg(i), inden + 2, false);
      outs () << "]\n";
      return;
    }
    else if (isOpX<AND>(exp))
    {
      outs () << string(inden, ' ') << "[&&\n";
      getConj(exp, flas);
    }
    else if (isOpX<OR>(exp))
    {
      outs () << string(inden, ' ') << "[||\n";
      getDisj(exp, flas);
    }
    else if (isOpX<NEG>(exp))
    {
      outs () << string(inden, ' ') << "[!\n";
      flas.insert(exp->left());
    }
    if (flas.empty()) outs () << string(inden, ' ') << exp;
    else
    {
      for (auto & a : flas)
      {
        pprint(a, inden + 2, false);
        outs() << "\n";
      }
      outs () << string(inden, ' ') << "]";
    }
    if (upper) outs() << "\n";
  }
}

#endif
