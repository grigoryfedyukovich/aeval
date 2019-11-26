#ifndef SIMSYNT__HPP__
#define SIMSYNT__HPP__

#include "adt/ADTSolver.hpp"

using namespace std;
using namespace boost;
namespace ufo
{

  // non-recursive version (don't be confused with ExprSimpl.hpp::getConj(Expr a, ExprSet &conjs))
  static inline void getConj(Expr s, ExprVector& ops)
  {
    if (isOpX<AND>(s))
    {
      for (unsigned i = 0; i < s->arity(); i++)
      {
        ops.push_back(s->arg(i));
      }
    }
    else ops.push_back(s);
  }

  class SimSynt
  {
    private:

    ExprFactory &efac;
    SMTUtils u;
    ExprVector &opsAdt;
    ExprVector &opsArr;
    ExprVector &assms;

    public:

    SimSynt(ExprFactory& _efac, ExprVector& _ops1, ExprVector& _ops2, ExprVector& _c, ExprVector& _l) :
      efac(_efac), u(_efac), opsAdt(_ops1), opsArr(_ops2), constructors(_c), assms(_l) {}

    ExprVector& constructors;
    Expr adtType;
    Expr baseCon;
    Expr indCon;
    int indConIndex = -1;
    ExprMap varVersions;
    ExprMap varVersionsInverse;
    Expr baseFormula;
    int stateProducingOp = -1;
    int stateConsumingOp = -1;
    int arrVarInd = -1;
    int indexVarInd = -1;
    int adtVarInd = -1;
    ExprVector nonstateVars;

    void getVarVersions(Expr op)
    {
      ExprSet vars;
      filter(op, bind::IsConst (), inserter(vars, vars.begin()));
      for (auto & v : vars)
      {
        string str = lexical_cast<string>(v);
        if (str.back() == '1')
        {
          str.pop_back();
          for (auto & v1 : vars)
          {
            if (str == lexical_cast<string>(v1))
            {
              varVersionsInverse[v] = v1;
              varVersions[v1] = v;
              break;
            }
          }
        }
      }
    }

    bool isBaseConstructor(Expr c, Expr type)
    {
      return (c->last() == type && c->arity() == 2);
    }

    bool isIndConstructor(Expr c, Expr type)
    {
      if (c->last() != type) return false;
      for (int j = 0; j < c->arity() - 1; j++)
        if (c->last() == c->arg(j)) return true;

      return false;
    }

    void checkConstructor(int i)
    {
      ExprSet cnjs;
      getConj(opsAdt[i], cnjs);
      for (auto & op : cnjs)
      {
        for (auto & c : constructors)
        {
          Expr capp;
          if (isOpX<EQ>(op))
          {
            Expr lhs = op->left();
            Expr rhs = op->right();
            if (isOpX<FAPP>(rhs) && rhs->left() == c) capp = rhs;
            else if (isOpX<FAPP>(lhs) && lhs->left() == c) capp = lhs;
          }
          if (capp != NULL)
          {
            if (isBaseConstructor(c, bind::typeOf(capp)))
            {
              // first comes firts serve here (to be generalized)
              if (baseCon == NULL) baseCon = capp;
              if (baseFormula == NULL) baseFormula = opsArr[i];
              return;
            }
            else if (isIndConstructor(c, bind::typeOf(capp)))
            {
              // first comes first serve here (to be generalized)
              if (indCon == NULL)
              {
                indCon = capp;
                indConIndex = i;
              }
              bool found = false;
              for (auto & v : varVersionsInverse)
                found |= contains(capp, v.first);

              if (!found)
              {
                stateProducingOp = i; // TODO: check if several
              }
              else
              {
                stateConsumingOp = i;
              }
              return;
            }
          }
        }
      }
    }

    int findStateConsumingOpInAssms()
    {
      for (int i = 0; i < opsAdt.size(); i++)
      {
        if (i == stateProducingOp) continue;

        ExprSet allConstrs;
        filter(opsAdt[i], bind::IsFApp (), inserter(allConstrs, allConstrs.begin()));

        for (auto & a : allConstrs)
          if (a->arity() > 1 && adtType == bind::typeOf(a))
            for (auto & l : assms)
              // very specific test: search for a lemma of the following shape
              // \forall x a(f(x)) = baseConstructor
              if (isOpX<FORALL>(l) && isOpX<EQ>(l->last()) &&
                  isOpX<FAPP>(l->last()->left()) && l->last()->left()->left() == a->left() &&
                  isOpX<FAPP>(l->last()->right()) &&
                  isBaseConstructor(l->last()->right()->left(), adtType))
                return i;

      }
      return -1;
    }

    int findStateProducingOpInAssms()
    {
      for (int i = 0; i < opsAdt.size(); i++)
      {
        if (i == stateConsumingOp) continue;

        ExprSet allConstrs;
        filter(opsAdt[i], bind::IsFApp (), inserter(allConstrs, allConstrs.begin()));

        for (auto & a : allConstrs)
          if (a->arity() > 1 && adtType == bind::typeOf(a))
            for (auto & l : assms)
              // very specific test: search for a lemma of the following shape
              // \forall x a(..) = indConstructor(...)
              if (isOpX<FORALL>(l) && isOpX<EQ>(l->last()) &&
                  isOpX<FAPP>(l->last()->left()) && l->last()->left()->left() == a->left() &&
                  isOpX<FAPP>(l->last()->right()) &&
                  isIndConstructor(l->last()->right()->left(), adtType))
                return i;

      }
      return -1;
    }

    Expr createQuantifiedFormula(Expr def)
    {
      ExprSet vars;
      ExprVector args;
      filter(def, bind::IsConst (), inserter(vars, vars.begin()));
      for (auto & a : vars) if (a != baseCon) args.push_back(a->last());
      args.push_back(def);
      return mknary<FORALL>(args);
    }

    void proc()
    {
      assert(opsAdt.size() == opsArr.size());

      // preprocessing
      for (int i = 0; i < opsAdt.size(); i++)
      {
        getVarVersions(opsAdt[i]);
        getVarVersions(opsArr[i]);
        checkConstructor(i);
      }

      adtType = bind::typeOf(indCon);
      assert(adtType == bind::typeOf(indCon));

      if (stateProducingOp == -1) stateProducingOp = findStateProducingOpInAssms();
      if (stateConsumingOp == -1) stateConsumingOp = findStateConsumingOpInAssms();
      assert(stateProducingOp >= 0);
      assert(stateConsumingOp >= 0);
      assert(baseFormula != NULL);
      assert(isOpX<EQ>(baseFormula));

      // get vars, types and arguments for rules of R
      ExprVector types;
      ExprVector vars;
      ExprVector varsPrime;
      ExprVector argsBase;
      ExprVector argsInd;

      for (auto & p : varVersions)
      {
        Expr v = p.first;
        vars.push_back(v);
        varsPrime.push_back(p.second);
        indCon = replaceAll(indCon, p.second, v);
        types.push_back(bind::typeOf(v));

        if (bind::typeOf(v) == adtType)
        {
          argsBase.push_back(baseCon);
        }
        else
        {
          if (varVersions[v] == NULL)
          {
            outs () << "NO UNPRIMED VAR FOR " << *v <<"\n";
            return;
          }
          argsBase.push_back(v);
        }
        if (bind::typeOf(v) == adtType)
          argsInd.push_back(indCon);   // use the app of the constructor(s) as argument
        else
          argsInd.push_back(v);        // use unprimed versions of other variables
      }

      types.push_back (mk<BOOL_TY> (efac));
      Expr rel = bind::fdecl (mkTerm<string> ("R", efac), types);
      Expr baseApp = bind::fapp (rel, argsBase);
      Expr baseDef = mk<EQ>(baseApp, baseFormula);

      // create a quantified formula representing the base rule of R
      Expr baseRule = createQuantifiedFormula(baseDef);

      // prepare for the inductive rule construction
      ExprSet indexVars;
      getCounters (opsArr[indConIndex], indexVars);
      Expr indexVar = *indexVars.begin(); // proceed with the least one
      Expr accessTerm;

      // if indConIndex == stateConsumingOp,
      // we require SELECTS to be expressed over primed vars (TODO: relax)
      indexVar = replaceAll(indexVar, varVersionsInverse);

      // identify how elements in the arrays are accessed (i.e., the indexVar)
      // and what content is stored to the array
      ExprSet transitions;
      map<Expr, ExprSet> arrayContent;
      getConj(opsArr[indConIndex], transitions);
      for (auto tr : transitions)
      {
        if (contains (tr, indexVar) && !containsOp<ARRAY_TY>(tr) && isOpX<EQ>(tr))
        {
          tr = normalizeArithm(tr);
          tr = ineqSimplifier(indexVar, tr);
          assert(tr->left() == indexVar);
          accessTerm = replaceAll(tr->right(), varVersionsInverse);
          if (indConIndex == stateConsumingOp)    // maybe will need to be treated more carefully
            accessTerm = swapPlusMinusConst(accessTerm);
        }
        else
        {
          ExprSet cnj;
          getConj(rewriteSelectStore(tr), cnj);
          for (auto & a : cnj)
          {
            if (isOpX<EQ>(a) && isOpX<SELECT>(a->right()))
              arrayContent[a->left()].insert(replaceAll(a->right()->last(), varVersionsInverse));
          }
        }
      }

      assert(accessTerm != NULL);
      bool traverseDirection = isConstPos(accessTerm);

      // calculate the least fixedpoint over the indexVar variable
      // currently, a simple heuristic is used, but it can be extended
      ExprSet guesses;
      mutateHeuristic (baseFormula, guesses);
      Expr invariant;
      for (auto & g : guesses)
      {
        if (u.implies(baseFormula, g) &&
            u.implies (mk<AND>(g, opsArr[indConIndex]), replaceAll(g, varVersions)))
        {
          invariant = g;
          break;
        }
      }

      // TODO: further, this invariant can be used to generate an auxiliary lemma
      //       e.g., \forall xs, n, A . R (xs, n, A) => invariant (n)

      // get the "precondition" for the inductive rule of R:
      // it should follow the fixedpoint but inconsistent with
      // the precondition for the base rule of R (captured in baseFormula)
      assert (invariant != NULL);
      Expr remainingCnj = mk<AND>(invariant, mkNeg(baseFormula));

      // prepare for the nested call of R in the inductive rule of R
      while (true)
      {
        int nestedInd = -1;
        for (int j = 1; j < indCon->arity(); j++)
        {
          if (adtType == bind::typeOf(indCon->arg(j)))
          {
            if (isOpX<FAPP>(indCon->arg(j)) && isIndConstructor(indCon->arg(j)->left(), adtType))
              nestedInd = j;
          }
          else
            nonstateVars.push_back(indCon->arg(j));
        }
        if (nestedInd == -1) break;
        else indCon = indCon->arg(nestedInd);
      }

      // aux vars for indexes
      for (int j = 0; j < types.size(); j++)
        if (isOpX<ARRAY_TY>(types[j])) arrVarInd = j;
        else if (types[j] == adtType) adtVarInd = j;
        else if (vars[j] == indexVar) indexVarInd = j;

      // get arguments of the nested call of R
      ExprVector argsIndNested = argsInd;
      for (int j = 0; j < types.size(); j++)
      {
        if (adtType == types[j]) argsIndNested[j] = vars[j];
        if (argsInd[j] == indexVar
              /*types[j] == bind::typeOf(indexVar)*/) argsIndNested[j] = accessTerm;
      }

      // prepare the inductive definition of R (i.e., the RHS of the inductive rule)
      ExprSet cnjs;
      for (auto & a : nonstateVars)   // need to match all non-state vars
      {                               // (obtained from the array and the ADT)
        auto it = arrayContent[a].begin();
        if (it == arrayContent[a].end()) continue;
        Expr accessTermTmp = normalizeArithm(replaceAll(accessTerm, indexVar, *it));
        if (traverseDirection)
          cnjs.insert(mk<EQ>(a, mk<SELECT>(vars[arrVarInd], indexVar)));
        else
          cnjs.insert(mk<EQ>(a, mk<SELECT>(vars[arrVarInd], accessTermTmp)));
        arrayContent[a].erase(it);
      }
      cnjs.insert(remainingCnj);

      // create a quantified formula representing the inductive rule
      Expr indRule = createQuantifiedFormula(generalizeInductiveDef(rel, argsInd, argsIndNested, cnjs));

      // generate and prove extra lemmas
      ExprVector extraLemmas;
      extraLemmas.push_back(createQuantifiedFormula(mk<IMPL>(bind::fapp (rel, vars), invariant)));
      Expr newInd = bind::intConst(mkTerm<string> (lexical_cast<string>(indexVar) + "1", efac));
      ExprVector newVars = vars;
      newVars[arrVarInd] = mk<STORE>(vars[arrVarInd], newInd, *nonstateVars.begin());
      extraLemmas.push_back(createQuantifiedFormula(mk<IMPL>(mk<AND>(
           (traverseDirection ? mk<LT>(newInd, indexVar) : mk<GEQ>(newInd, indexVar)),
                   bind::fapp (rel, vars)), bind::fapp (rel, newVars))));

      assms.push_back(baseRule);
      assms.push_back(indRule);

      for (auto it = extraLemmas.begin(); it != extraLemmas.end(); )
      {
        if (prove(assms, *it))
        {
          outs () << "added lemma: ";
          u.serialize_formula (*it);
          ++it;
        }
        else
        {
          it = extraLemmas.erase(it);
        }
      }

      // extraLemmas are added to assms at the very end (to accelerate solving)
      // however, for some cases it could be needed to use extraLemmas to prove some other extraLemmas
      assms.insert(assms.end(), extraLemmas.begin(), extraLemmas.end());

      for (int i = 0; i < opsAdt.size(); i ++)
      {
        if (i != stateConsumingOp && i != stateProducingOp) continue;

        Expr goal = bind::fapp (rel, varsPrime);
        ExprVector assmsTmp;
        getConj(opsArr[i], assmsTmp);
        getConj(opsAdt[i], assmsTmp);

        // simplification
        for (auto it = assmsTmp.begin(); it != assmsTmp.end();)
        {
          auto a = *it;
          if (isOpX<EQ>(a) && contains(goal, a->left()))
          {
            goal = replaceAll(goal, a->left(), a->right());
            it = assmsTmp.erase(it);
          }
          else ++it;
        }

        assmsTmp.insert(assmsTmp.end(), assms.begin(), assms.end());
        assmsTmp.push_back(bind::fapp (rel, vars));

        // estimate the number of rewriting rounds for the prover
        // based on the number of constructors (to be optimized further)
        ExprSet allConstrs;
        filter(opsAdt[i], bind::IsFApp (), inserter(allConstrs, allConstrs.begin()));
        int rounds = 1;
        for (auto & a : allConstrs)
          if (find(constructors.begin(), constructors.end(), a->left()) != constructors.end() &&
              a->arity() > 1) rounds++;

        bool res = prove(assmsTmp, goal, rounds);
        outs () << "proving for operations " << (i == stateConsumingOp ? "consuming" : "producing") <<
          " state: " << (res ? "true" : "false") << "\n";
        if (!res)
        {
          outs () << "unknown\n";
          exit(0);
        }
      }
      outs () << "simulation proved\n";
      u.serialize_formula(baseRule);
      u.serialize_formula(indRule);
    }

    bool prove (ExprVector lemmas, Expr fla, int rounds = 2)
    {
      ADTSolver sol (fla, lemmas, constructors /*, 5, 1, true*/); // uncomment for the verbose mode
      vector<int> basenums, indnums; // dummies
      bool res;
      if (isOpX<FORALL>(fla)) res = sol.solve(basenums, indnums);
      else res = sol.solveNoind(rounds);
      return res;
    }

    Expr generalizeInductiveDef(Expr rel, ExprVector& argsInd, ExprVector& argsIndNested, ExprSet& cnjs)
    {
      Expr all = mkTerm (mpz_class (nonstateVars.size()), efac);
      ExprSet pre;

      // nonstateVars computed by the recursive traversal of indCon
      // so it is safe to look at them here instead of looking at indCon again
      for (int i = 0; i < nonstateVars.size(); i++)
      {
        Expr cur = mkTerm (mpz_class (i + 1), efac);
        Expr a = mk<EQ>(nonstateVars[i], mk<SELECT>(argsInd[arrVarInd],
                        mk<MINUS>(argsInd[indexVarInd], cur)));
        bool res = false;
        for (auto it = cnjs.begin(); it != cnjs.end(); )
        {
          if (u.implies(*it, a))
          {
            res = true;
            cnjs.erase(it);
            break;
          }
          else ++it;
        }
        if (!res)
          pre.insert(mk<EQ>(mk<MOD>(argsInd[indexVarInd], all), mkTerm (mpz_class (i), efac)));
      }

      if (u.isTrue(mk<EQ>(argsIndNested[indexVarInd], mk<MINUS>(argsInd[indexVarInd], all))))
      {
        Expr newDecrement = mk<MINUS>(argsInd[indexVarInd], mkTerm (mpz_class (1), efac));
        pre.insert(mk<EQ>(mk<SELECT>(argsInd[arrVarInd], newDecrement), nonstateVars.back()));
        cnjs.insert(disjoin(pre, efac));
        argsInd[adtVarInd] = indCon;
        argsIndNested[indexVarInd] = newDecrement;
      }
      cnjs.insert(bind::fapp (rel, argsIndNested));
      return mk<EQ>(bind::fapp (rel, argsInd), conjoin(cnjs, efac));
    }
  };

  static inline void simSynt(ExprFactory& efac, EZ3& z3, Expr s1, Expr s2)
  {
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(a);
    ExprVector opsAdt;
    ExprVector opsArr;
    if (containsOp<ARRAY_TY>(s2))
    {
      assert(containsOp<AD_TY>(s1));
      getConj(s1, opsAdt);
      getConj(s2, opsArr);
    }
    else
    {
      assert(containsOp<ARRAY_TY>(s1));
      assert(containsOp<AD_TY>(s2));
      getConj(s2, opsAdt);
      getConj(s1, opsArr);
    }

    ExprVector assms;
    for (auto it = opsAdt.begin(); it != opsAdt.end(); )
    {
      if (isOpX<FORALL>(*it))
      {
        assms.push_back(regularizeQF(*it));
        it = opsAdt.erase(it);
      }
      else
      {
        ++it;
      }
    }

    SimSynt sim (efac, opsAdt, opsArr, constructors, assms);
    sim.proc();
  }
}

#endif
