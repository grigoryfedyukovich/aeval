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
    ExprVector &assumptions;

    public:

    SimSynt(ExprFactory& _efac, ExprVector& _ops1, ExprVector& _ops2, ExprVector& _c, ExprVector& _l) :
      efac(_efac), u(_efac), opsAdt(_ops1), opsArr(_ops2), constructors(_c), assumptions(_l) {}

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
    int stateInitOp = -1;
    int stateNoOp = -1;
    int arrVarInd = -1;
    int indexVarInd = -1;
    int adtVarInd = -1;
    ExprVector nonstateVars;
    ExprSet extras; // aux
    Expr nestedRel;
    ExprVector extraLemmas;
    Expr baseRule;
    Expr indRule;
    ExprVector types;
    ExprVector vars;
    ExprVector varsPrime;
    ExprVector argsBase;
    ExprVector argsInd;
    Expr indexVar;
    Expr rel;
    map<Expr, ExprSet> arrayContent;
    Expr accessTerm;

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
      ExprSet allConstrs;
      filter(opsAdt[i], bind::IsFApp (), inserter(allConstrs, allConstrs.begin()));
      for (auto rit = allConstrs.rbegin(); rit != allConstrs.rend(); ++rit)
      {
        Expr capp = *rit;
        for (auto & c : constructors)
        {
          if (capp->left() == c)
          {
            if (isBaseConstructor(c, bind::typeOf(capp)))
            {
              // first comes firts serve here (to be generalized)
              if (baseCon == NULL)
              {
                baseCon = capp;
                assert (baseFormula == NULL);
                baseFormula = opsArr[i];
                stateInitOp = i;
                return;
              }
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
            for (auto & l : assumptions)
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
            for (auto & l : assumptions)
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

    void guessScanBasedRelations(Expr accessTerm)
    {
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
      indRule = createQuantifiedFormula(generalizeInductiveDef(rel, argsInd, argsIndNested, cnjs));

      // generate extra lemmas
      extraLemmas.push_back(createQuantifiedFormula(mk<IMPL>(bind::fapp (rel, vars), invariant)));
      Expr newInd = bind::intConst(mkTerm<string> (lexical_cast<string>(indexVar) + "1", efac));
      ExprVector newVars = vars;
      newVars[arrVarInd] = mk<STORE>(vars[arrVarInd], newInd, *nonstateVars.begin());
      extraLemmas.push_back(createQuantifiedFormula(mk<IMPL>(mk<AND>(
           (traverseDirection ? mk<LT>(newInd, indexVar) : mk<GEQ>(newInd, indexVar)),
                   bind::fapp (rel, vars)), bind::fapp (rel, newVars))));
    }

    void guessRelations(bool alt = true)
    {
      // prepare for the nested call of R in the inductive rule of R
      ExprVector argsIndNested = argsInd;
      for (int j = 0; j < types.size(); j++)
      {
        if (j == adtVarInd)
        {
          argsIndNested[j] = vars[j];
        }
        else if (j == arrVarInd)
        {
          // TODO: make sure variables are unified
          if (alt)
            // currently, hardcode:
            argsIndNested[j] = opsArr[stateConsumingOp]->right();
        }
      }

      // prepare the inductive definition of R (i.e., the RHS of the inductive rule)
      ExprSet cnjs;
      ExprSet transitions1;
      ExprSet transitions2;
      getConj(opsArr[stateNoOp], transitions1);
      getConj(opsAdt[stateNoOp], transitions2);
      for (auto tr1 : transitions1)
      {
        for (auto tr2 : transitions2)
        {
          if (isOpX<EQ>(tr1) && isOpX<EQ>(tr2))
          {
            Expr eq;
            if (tr1->left() == tr2->left())
            {
              eq = (mk<EQ>(tr1->right(), tr2->right()));
            }
            else if (tr1->right() == tr2->right())
            {
              eq = (mk<EQ>(tr1->left(), tr2->left()));
            }
            else if (tr1->left() == tr2->right())
            {
              eq = (mk<EQ>(tr1->right(), tr2->left()));
            }
            else if (tr1->right() == tr2->left())
            {
              eq = (mk<EQ>(tr1->left(), tr2->right()));
            }
            if (eq != NULL)
              cnjs.insert(
                simplifyFormulaWithLemmas(replaceAll(eq, vars[adtVarInd], argsInd[adtVarInd]),
                  assumptions, constructors));
          }
        }
      }

      nestedRel = bind::fapp (rel, argsIndNested);
      cnjs.insert(nestedRel);
      Expr inductiveDef = mk<EQ>(bind::fapp (rel, argsInd), conjoin(cnjs, efac));
      indRule = createQuantifiedFormula(inductiveDef);

      if (stateNoOp >= 0 && stateNoOp < opsAdt.size())
      {
        Expr adtPred;
        Expr arrPred;
        if (opsAdt[stateNoOp]->left() == opsArr[stateNoOp]->left())
        {
          adtPred = opsAdt[stateNoOp]->right();
          arrPred = opsArr[stateNoOp]->right();
        }
        else if (opsAdt[stateNoOp]->right() == opsArr[stateNoOp]->right())
        {
          adtPred = opsAdt[stateNoOp]->left();
          arrPred = opsArr[stateNoOp]->left();
        }
        else if (opsAdt[stateNoOp]->left() == opsArr[stateNoOp]->right())
        {
          adtPred = opsAdt[stateNoOp]->right();
          arrPred = opsArr[stateNoOp]->left();
        }
        else if (opsAdt[stateNoOp]->right() == opsArr[stateNoOp]->left())
        {
          adtPred = opsAdt[stateNoOp]->left();
          arrPred = opsArr[stateNoOp]->right();
        }
        if (adtPred != NULL && arrPred != NULL &&
            bind::typeOf(adtPred) == mk<BOOL_TY>(efac))
        {
          // currently, hardcode:
          if (alt)
          {
            extras.insert(mkNeg(adtPred));
            extras.insert(mkNeg(arrPred));
          }
          else
          {
            extras.insert(adtPred);
            extras.insert(arrPred);
          }
          extraLemmas.push_back(createQuantifiedFormula(
                mk<IMPL>(mk<AND>(bind::fapp (rel, vars), adtPred), arrPred)));
          extraLemmas.push_back(createQuantifiedFormula(
                mk<IMPL>(mk<AND>(bind::fapp (rel, vars), mkNeg(adtPred)), mkNeg(arrPred))));
        }
      }
    }

    Expr simplifyFormulaWithLemmas(Expr fla, ExprVector lemmas, ExprVector& constructors)
    {
      ADTSolver sol (fla, lemmas, constructors, 7, 3, 3, 0, false);
      ExprSet newAssms;
      sol.simplifyAssm(fla, newAssms);
      if (newAssms.empty()) return fla;
      ExprSet newAssmsSimpl;
      for (auto & a : newAssms) newAssmsSimpl.insert(simplifyBool(a));
      return *newAssmsSimpl.begin(); // TODO: check if it is meaningful somehow
    }

    void preprocessing()
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
      for (stateNoOp = 0; stateNoOp < opsAdt.size(); stateNoOp++)
      {
        if (stateNoOp != stateProducingOp &&
            stateNoOp != stateConsumingOp &&
            stateNoOp != stateInitOp &&
            isOpX<EQ>(opsAdt[stateNoOp]) && isOpX<EQ>(opsArr[stateNoOp]))
          break;
      }
      assert(baseFormula != NULL);

      // get vars, types and arguments for rules of R

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
      rel = bind::fdecl (mkTerm<string> ("R", efac), types);
      Expr baseApp = bind::fapp (rel, argsBase);
      Expr baseDef = mk<EQ>(baseApp, baseFormula);

      // create a quantified formula representing the base rule of R
      baseRule = createQuantifiedFormula(baseDef);

      // prepare for the inductive rule construction
      ExprSet indexVars;
      getCounters (opsArr[indConIndex], indexVars);
      indexVar = *indexVars.begin(); // proceed with the least one

      // if indConIndex == stateConsumingOp,
      // we require SELECTS to be expressed over primed vars (TODO: relax)
      indexVar = replaceAll(indexVar, varVersionsInverse);

      // identify how elements in the arrays are accessed (i.e., the indexVar)
      // and what content is stored to the array
      ExprSet transitions;
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
            if (isOpX<EQ>(a) && isOpX<SELECT>(a->right()))
              arrayContent[a->left()].insert(replaceAll(a->right()->last(), varVersionsInverse));
        }
      }

      // aux vars for indexes
      for (int j = 0; j < types.size(); j++)
        if (isOpX<ARRAY_TY>(types[j])) arrVarInd = j;
        else if (types[j] == adtType) adtVarInd = j;
        else if (vars[j] == indexVar) indexVarInd = j;
    }

    void proc()
    {
      preprocessing();

      // benchmarks with stack/queue are expected to fall into this category
      if (accessTerm != NULL) guessScanBasedRelations(accessTerm);
      // otherwise, "standard" relations (e.g., characteristic sets)
      else guessRelations();

      if (checkAll(assumptions, ExprSet()))
      {
        outs () << "simulation proved\n";
        u.serialize_formula(baseRule);
        u.serialize_formula(indRule);
        return;
      }

      // TODO: make a CEGAR-loop

      if (checkAll(assumptions, extras))
      {
        Expr rel1 = nestedRel;
        Expr pre1;
        for (auto & a : extras) if (!containsOp<ARRAY_TY>(a)) pre1 = a;
        extras.clear();
        guessRelations(false);
        if (checkAll(assumptions, extras))
        {
          indRule = replaceAll(indRule, nestedRel, mk<ITE>(mkNeg(pre1), nestedRel, rel1));
          if (checkAll(assumptions, ExprSet()))
          {
            u.serialize_formula(baseRule);
            u.serialize_formula(indRule);
          }
        }
      }
    }

    bool checkAll(ExprVector assms, ExprSet extras)
    {
      // check lemmas first
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

        if (extras.size() > 0)
          assmsTmp.insert(assmsTmp.end(), extras.begin(), extras.end());

        bool res = prove(assmsTmp, goal, rounds);
        outs () << "proving for operations " << (i == stateConsumingOp ? "consuming" : "producing") <<
          " state: " << (res ? "true" : "false") << "\n";
        if (!res)
        {
          return false;
        }
      }
      return true;
    }

    bool prove (ExprVector lemmas, Expr fla, int rounds = 2)
    {
      ADTSolver sol (fla, lemmas, constructors, 7, 3, 3, 0, false); // last false is for verbosity
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
        pre.insert(mk<EQ>(nonstateVars.back(), mk<SELECT>(argsInd[arrVarInd], newDecrement)));
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

    for (auto & a : opsArr)
    {
      if (isOpX<FORALL>(a))
      {
        a = regularizeQF(a);
      }
    }

    SimSynt sim (efac, opsAdt, opsArr, constructors, assms);
    sim.proc();
  }
}

#endif
