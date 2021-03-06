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

  template<typename Range> static int intersectSize(Expr a, Range& bv){
    ExprVector av;
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    ExprSet intersect;
    for (auto &var1: av){
      for (auto &var2: bv)
        if (var1 == var2) intersect.insert(var1);
    }
    return intersect.size();
  }

  inline static Expr multVar(Expr var, int coef){
    if (coef == 0)
      return mkTerm (mpz_class (0), var->getFactory());
    if (isOpX<MPZ>(var)) return
      mkTerm (mpz_class (lexical_cast<int>(var) * coef), var->getFactory());
    if (isOpX<MPQ>(var)) return
      mkTerm (mpq_class (lexical_cast<int>(var) * coef), var->getFactory());

    return mk<MULT>(mkTerm (mpz_class (coef), var->getFactory()), var);
  }

  inline static int isMultVar(Expr e, Expr var){
    if (e == var) return 1;
    if (!isOpX<MULT>(e)) return 0;
    if (isOpX<MPZ>(e->right()) && var == e->left()) return lexical_cast<int>(e->right());
    if (isOpX<MPZ>(e->left()) && var == e->right()) return lexical_cast<int>(e->left());
    if (isOpX<MPQ>(e->right()) && var == e->left()) return lexical_cast<int>(e->right());
    if (isOpX<MPQ>(e->left()) && var == e->right()) return lexical_cast<int>(e->left());
    return 0;
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
    return mk<UN_MINUS>(e);
  }

  inline static void getPlusTerms (Expr a, ExprVector &terms)
  {
    if (isOpX<PLUS>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getPlusTerms(a->arg(i), terms);
      }
    }
    else if (isOpX<MINUS>(a)){
      // assume only two args
      terms.push_back(a->left());
      terms.push_back(additiveInverse(a->right()));
    } else {
      terms.push_back(a);
    }
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

  bool isBoolVarOrNegation(Expr exp)
  {
    if (bind::isBoolConst(exp)) return true;
    if (isOpX<NEG>(exp)) return isBoolVarOrNegation(exp->left());
    return false;
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
    else if (isOpX<FALSE>(term))
    {
      return mk<TRUE>(term->getFactory());
    }
    else if (isOpX<TRUE>(term))
    {
      return mk<FALSE>(term->getFactory());
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

  bool isNumeric(Expr a)
  {
    // don't consider ITE-s
    return (isOp<NumericOp>(a) || isOpX<MPZ>(a) || isOpX<MPQ>(a) ||
            bind::isIntConst(a) || bind::isRealConst(a));
  }

  bool isBoolean(Expr a)
  {
    if (isOpX<ITE>(a)) return isBoolean(a->last());
    return (isOpX<AND>(a) || isOpX<OR>(a) || isOpX<IMPL>(a) || isOpX<NEG>(a) || isOpX<IFF>(a) ||
            isOp<ComparissonOp>(a) || bind::isBoolConst(a));
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

    ExprVector terms;
    getPlusTerms(l, terms);
    for (auto & a : terms)
    {
      if (contains(a, var))
      {
        lhs = a;
        continue;
      }
      rhs.insert(additiveInverse(a));
    }

    terms.clear();
    getPlusTerms(r, terms);
    for (auto & a : terms)
    {
      if (contains(a, var))
      {
        assert(lhs == NULL);
        lhs = additiveInverse(a);
        continue;
      }
      rhs.insert(a);
    }

    if (lhs != 0) return mk<T>(lhs, mkplus(rhs, e->getFactory()));
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
          return additiveInverse(res);
        } else
          
          if (isOpX<MINUS>(a)){
            if (a->left() == b) ret = additiveInverse(a->right());
          } else
            
            if (isOpX<MINUS>(b)){
              if (a == b->right()) ret = additiveInverse(b->left());
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
                        ret = additiveInverse(b);
                      }
                    }

    return ret;
  }

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

  inline static bool evaluateCmpConsts(Expr term)
  {
    if (!isOpX<MPZ>(term->left()) || !isOpX<MPZ>(term->right()))
      return false;
    int a = lexical_cast<int>(term->left());
    int b = lexical_cast<int>(term->right());
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

  inline static int separateConst(ExprVector& plsOps)
  {
    int c = 0;
    for (auto it = plsOps.begin(); it != plsOps.end(); )
    {
      if (isOpX<MPZ>(*it))
      {
        c += lexical_cast<int>(*it);
        it = plsOps.erase(it);
        continue;
      }
      else ++it;
    }
    return c;
  }

  inline static Expr simplifyPlus (Expr exp){
    ExprVector plsOps;
    getPlusTerms (exp, plsOps);
    // GF: to extend
    int c = separateConst(plsOps);
    if (c != 0) plsOps.push_back(mkTerm (mpz_class (c), exp->getFactory()));
    return mkplus(plsOps, exp->getFactory());
  }

  inline static Expr simplifyIte (Expr exp)  // simple version, on the syntactic level
  {
    ExprFactory &efac = exp->getFactory();
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getPlusTerms(exp->right(), plusOpsLeft);
    getPlusTerms(exp->last(), plusOpsRight);

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

    Expr b1 = mkplus(plusOpsLeft, efac);
    Expr b2 = mkplus(plusOpsRight, efac);
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
    if (evaluateCmpConsts(exp)) return mk<TRUE>(efac);

    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getPlusTerms(exp->left(), plusOpsLeft);
    getPlusTerms(exp->right(), plusOpsRight);

    int c1 = separateConst(plusOpsLeft);
    int c2 = separateConst(plusOpsRight);

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

    if (c1 > c2)
      plusOpsLeft.push_back(mkTerm (mpz_class (c1 - c2), efac));
    else if (c1 < c2)
      plusOpsRight.push_back(mkTerm (mpz_class (c2 - c1), efac));

    return reBuildCmp(exp, mkplus(plusOpsLeft, efac), mkplus(plusOpsRight, efac));
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
      minus_one = mkTerm (mpz_class (-1), efac);
    };

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
        if (exp->left() == zero) return zero;
        if (exp->right() == zero) return zero;
        if (exp->left() == one) return exp->right();
        if (exp->right() == one) return exp->left();
        if (exp->left() == minus_one) return additiveInverse(exp->right());
        if (exp->right() == minus_one) return additiveInverse(exp->left());
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

      if (isOp<ComparissonOp>(exp) && isNumeric(exp->right()))
      {
        return simplifyCmp(exp);
      }

      if (isOpX<ITE>(exp) && isNumeric(exp->right()))
      {
        return simplifyIte(exp);
      }
      return exp;
    }
  };

  inline static Expr simplifyBool (Expr exp);

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

      if (isOpX<EQ>(exp)){
        if (isOpX<TRUE>(exp->right())) return exp->left();
        if (isOpX<TRUE>(exp->left())) return exp->right();
        if (isOpX<FALSE>(exp->right())) return mkNeg(exp->left());
        if (isOpX<FALSE>(exp->right())) return mkNeg(exp->right());
      }

      if (isOpX<OR>(exp))
      {
        ExprSet dsjs;
        ExprSet newDsjs;
        getDisj(exp, dsjs);
        for (auto & a : dsjs){
          if (isOpX<TRUE>(a))
          {
            return mk<TRUE>(efac);
          }
          if (isOpX<FALSE>(a))
          {
            continue;
          }
          newDsjs.insert(simplifyBool(a));
        }
        return disjoin (newDsjs, efac);
      }

      if (isOpX<AND>(exp))
      {
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(exp, cnjs);
        for (auto & a : cnjs){
          if (isOpX<FALSE>(a))
          {
            return mk<FALSE>(efac);
          }
          if (isOpX<TRUE>(a))
          {
            continue;
          }
          newCnjs.insert(simplifyBool(a));
        }
        return conjoin (newCnjs, efac);
      }

      if (isOpX<ITE>(exp)){
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

      if (isOpX<NEG>(*it))
      {
        Expr negged = mkNeg((*it)->left());
        it = cnjs.erase(it);
        cnjs.insert(negged);
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
          a = simplifyBool(mk<NEG>(a->right()));
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
            facts.push_back(mk<NEG>(c));
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
        else if (isOpX<EQ>(c))
        {
          if (bind::isIntConst(c->left())  &&
              find(hardVars.begin(), hardVars.end(), c->left()) == hardVars.end())
          {
            toRestart = true;
            facts.push_back(c->left());
            repls.push_back(c->right());
          }
          else if (bind::isIntConst(c->right())  &&
                   find(hardVars.begin(), hardVars.end(), c->right()) == hardVars.end())
          {
            toRestart = true;
            facts.push_back(c->right());
            repls.push_back(c->left());
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

    for (int i = 0; i < facts.size() ; i++)
      if (!isOpX<NEG>(facts[i]))
        cnjs.insert(mk<EQ>(facts[i], repls[i]));
  }

  template <typename T> static Expr convertIntsToReals (Expr exp);

  template <typename T> struct IntToReal
  {
    IntToReal<T> () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<T>(exp))
      {
        ExprVector args;
        for (int i = 0; i < exp->arity(); i++)
        {
          Expr e = exp->arg(i);
          if (isOpX<MPZ>(e))
            e = mkTerm (mpq_class (lexical_cast<int>(e)), exp->getFactory());
          else {
            e = convertIntsToReals<PLUS>(e);
            e = convertIntsToReals<MINUS>(e);
            e = convertIntsToReals<MULT>(e);
            e = convertIntsToReals<UN_MINUS>(e);
          }
          args.push_back(e);
        }
        return mknary<T>(args);
      }
      return exp;
    }
  };

  template <typename T> static Expr convertIntsToReals (Expr exp)
  {
    RW<IntToReal<T>> rw(new IntToReal<T>());
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

  struct EqNumMiner : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& eqs;
    Expr& var;

    EqNumMiner (Expr& _var, ExprSet& _eqs): var(_var), eqs(_eqs) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<EQ>(exp) && (contains(exp, var)) && exp->right() != exp->left() &&
          isNumeric(exp->left()) && isNumeric(exp->right()))
      {
        eqs.insert(ineqMover(exp, var));
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  struct EqBoolMiner : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& eqs;
    Expr& var;

    EqBoolMiner (Expr& _var, ExprSet& _eqs): var(_var), eqs(_eqs) {};

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
    if (bind::isIntConst(var) || bind::isRealConst(var))
    {
      EqNumMiner trm (var, eqs);
      dagVisit (trm, exp);
    }
    else
    {
      EqBoolMiner trm (var, eqs);
      dagVisit (trm, exp);
    }
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
}

#endif
