#ifndef SIMSYNT__HPP__
#define SIMSYNT__HPP__

#include "adt/ADTSolver.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class SimSynt
  {
    private:

    ExprFactory &efac;
    SMTUtils u;
    ExprVector &opsAdt;
    ExprVector &opsArr;
    ExprVector& constructors;
    ExprVector &assumptions;
    Expr adtType;
    Expr baseCon;
    Expr indCon;
    int indConIndex = -1;
    ExprMap& varVersions;
    Expr baseFormula;
    int stateProducingOp = -1;
    int stateConsumingOp = -1;
    int stateNoOp = -1;
    int arrVarInd = -1;
    int indexVarInd = -1;
    int adtVarInd = -1;
    ExprVector nonstateVars;
    ExprSet extras; // aux
    Expr nestedRel;
    ExprVector extraLemmas;
    ExprVector types;
    ExprVector vars;
    ExprVector varsPrime;
    ExprVector argsBase;
    ExprVector argsInd;
    Expr indexVar;
    Expr rel;
    map<Expr, ExprSet> arrayContent;
    Expr accessTerm;
    Expr baseRule;
    Expr indRule;

    public:

    SimSynt(ExprFactory& _efac, ExprVector& _ops1, ExprVector& _ops2, ExprMap& _v,
            ExprVector& _c, Expr _r, ExprVector& _l, Expr _b) :
      efac(_efac), u(_efac), opsAdt(_ops1), opsArr(_ops2), varVersions(_v),
            constructors(_c), rel(_r), assumptions(_l), baseFormula(_b){}

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
            if (isIndConstructor(c, bind::typeOf(capp)))
            {
              // first comes first serve here (to be generalized)
              if (indCon == NULL)
              {
                indCon = capp;
                indConIndex = i;
              }
              bool found = false;
              for (auto & v : varVersions)
                found |= contains(capp, v.second);

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
            {
              // very specific test: search for a lemma of the following shape
              // \forall x a(f(x)) = baseConstructor
              if (isOpX<FORALL>(l) && isOpX<EQ>(l->last()) &&
                  isOpX<FAPP>(l->last()->left()) && contains(l->last()->left(), a->left()) &&
                  isOpX<FAPP>(l->last()->right()) &&
                  isBaseConstructor(l->last()->right()->left(), adtType))
                return i;
            }

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
                  isOpX<FAPP>(l->last()->left()) && contains(l->last()->left(), a->left()) &&
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

    // relations based on linear scan (e.g., stack, queue)
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

      // generate and prove extra lemmas
      extraLemmas.push_back(createQuantifiedFormula(mk<IMPL>(bind::fapp (rel, vars), invariant)));
      Expr newInd = bind::intConst(mkTerm<string> (lexical_cast<string>(indexVar) + "1", efac));
      ExprVector newVars = vars;
      newVars[arrVarInd] = mk<STORE>(vars[arrVarInd], newInd, *nonstateVars.begin());
      extraLemmas.push_back(createQuantifiedFormula(mk<IMPL>(mk<AND>(
           (traverseDirection ? mk<LT>(newInd, indexVar) : mk<GEQ>(newInd, indexVar)),
                   bind::fapp (rel, vars)), bind::fapp (rel, newVars))));
    }

    // relations based on nonlinear scan and noops (e.g., sets, multisets)
    void guessRelations(bool alt = true)
    {
      // prepare the inductive definition of R (i.e., the RHS of the inductive rule)
      ExprSet cnjs;
      ExprSet transitionsArr;
      ExprSet transitionsAdt;
      if (stateNoOp >= 0 && stateNoOp < opsAdt.size())
      {
        Expr adtPred;
        Expr arrPred;

        getConj(opsArr[stateNoOp], transitionsArr);
        getConj(opsAdt[stateNoOp], transitionsAdt);

        if (transitionsArr.empty())
        {
          for (auto trAdt : transitionsAdt)
          {
            if (isOpX<NEG>(trAdt) && isOpX<EQ>(trAdt->last())) // coming from the query
            {
              trAdt = trAdt->last();
              if (containsOp<ARRAY_TY>(trAdt->left()) && contains(trAdt->right(), adtType))
              {
                adtPred = trAdt->right();
                arrPred = trAdt->left();
              }
              else if (containsOp<ARRAY_TY>(trAdt->right()) && contains(trAdt->left(), adtType))
              {
                adtPred = trAdt->left();
                arrPred = trAdt->right();
              }
            }
          }
        }
        else
        {
          for (auto trArr : transitionsArr)
          {
            for (auto trAdt : transitionsAdt)
            {
              if (isOpX<EQ>(trArr) && isOpX<EQ>(trAdt))
              {
                if (trArr->left() == trAdt->left())
                {
                  adtPred = trAdt->right();
                  arrPred = trArr->right();
                }
                else if (trArr->right() == trAdt->right())
                {
                  adtPred = trAdt->left();
                  arrPred = trArr->left();
                }
                else if (trArr->left() == trAdt->right())
                {
                  adtPred = trAdt->left();
                  arrPred = trArr->right();
                }
                else if (trArr->right() == trAdt->left())
                {
                  adtPred = trAdt->right();
                  arrPred = trArr->left();
                }
              }
            }
          }
        }

        if (adtPred != NULL && arrPred != NULL)
        {
          // prepare app for the definition of R
          // unify vars
          // step 1: find common occurrences in adtPred and arrPred:

          ExprSet c;
          intersect(adtPred, arrPred, c);
          assert (!c.empty());

          // step 2: make sure body uses vars from c
          // assume c.size() == 1;
          Expr cVar = *c.begin();
          if (!contains(argsInd[adtVarInd], cVar))
          {
            ExprVector av;
            filter (argsInd[adtVarInd], bind::IsConst (), inserter(av, av.begin()));
            for (auto & v : av)
            {
              if (bind::typeOf(v) == bind::typeOf(cVar))
              {
                argsInd[adtVarInd] = replaceAll(argsInd[adtVarInd], v, cVar);
                break;
              }
            }
          }

          Expr app = bind::fapp (rel, argsInd);

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
              {
                argsIndNested[j] = opsArr[indConIndex]->right();
                if (indConIndex == stateProducingOp)
                {
                  Expr tmp = argsIndNested[j];
                  tmp = swapPlusMinusConst(tmp);
                  if (tmp != argsIndNested[j])
                  {
                    argsIndNested[j] = tmp;
                  }
                  else
                  {
                    // GF: hack, need a proper replacer
                    tmp = replaceAll(tmp, mk<TRUE>(efac), mk<FALSE>(efac));
                    if (tmp != argsIndNested[j])
                    {
                      argsIndNested[j] = tmp;
                    }
                    else
                    {
                      // complicated replacement based on noops

                      ExprVector av;  // sanity check
                      filter (adtPred, bind::IsConst (), inserter(av, av.begin()));
                      for (auto & a : av) assert (contains (app, a)); // TODO: proper renaming

                      ExprSet c;
                      intersect(app, tmp, c);
                      for (auto & a : c)
                      {
                        if (bind::typeOf(adtPred) == bind::typeOf(a))
                        {
                          tmp = replaceAll(tmp, a, adtPred);
                          if (tmp != argsIndNested[j])
                          {
                            argsIndNested[j] = tmp;
                            break;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          nestedRel = bind::fapp (rel, argsIndNested);

          Expr body =
            simplifyFormulaWithLemmas(
              replaceAll(mk<EQ>(arrPred, adtPred),
                vars[adtVarInd], argsInd[adtVarInd]),
                  assumptions, constructors);

          cnjs.insert(body);
          cnjs.insert(nestedRel);
          Expr inductiveDef = mk<EQ>(app, conjoin(cnjs, efac));
          indRule = createQuantifiedFormula(inductiveDef);
          extraLemmas.push_back(createQuantifiedFormula(
               mk<IMPL>(bind::fapp (rel, vars), mk<EQ>(arrPred, adtPred))));
        }
      }
    }

    Expr simplifyFormulaWithLemmas(Expr fla, ExprVector lemmas, ExprVector& constructors)
    {
      ADTSolver sol (fla, lemmas, constructors, 0, 0, 3, 0, false);
      ExprSet newAssms;
      sol.simplifyAssm(fla, newAssms);
      if (newAssms.empty()) return fla;
      ExprSet newAssmsSimpl;
      for (auto & a : newAssms) newAssmsSimpl.insert(/*simplifyArithm*/(simplifyBool(a)));
      return *newAssmsSimpl.begin(); // TODO: check if it is meaningful somehow
    }

    void preprocessing()
    {
      assert(opsAdt.size() == opsArr.size());

      for (int i = 0; i < opsAdt.size(); i++) checkConstructor(i);

      if (indCon == NULL)
      {
        for (auto & c : constructors)
        {
          for (int j = 0; j < c->arity() - 1; j++)
          {
            if (c->last() == c->arg(j))
            {
              // found inductive constructor
              Expr indConstructor = c;
              ExprVector args;
              for (int i = 1; i < indConstructor->arity() - 1; i++)
              {
                Expr s;
                if (j == i)
                {
                  // link to the already defined ADT (try guessing for now)
                  for (auto & p : varVersions)
                  {
                    if (containsOp<AD_TY>(p.first))
                    {
                      s = p.first;
                      break;
                    }
                  }
                  assert(s != NULL);
                }
                else
                {
                  // should be a fresh (nonstate) var

                  Expr singleCons = NULL;
                  for (auto & a : constructors)
                  {
                    if (a->last() == indConstructor->arg(i))
                    {
                      if (singleCons != NULL)
                      {
                        singleCons = NULL;
                        break;
                      }
                      singleCons = a;
                    }
                  }
                  if (singleCons != NULL && !isIndConstructor(singleCons, indConstructor->arg(i)))
                  {
                    // unfold non-recursive definitions
                    ExprVector argsCons;
                    for (int j = 1; j < singleCons->arity() - 1; j++)
                    {
                      argsCons.push_back(bind::mkConst(mkTerm<string> ("_x_" + to_string(j), efac), singleCons->arg(j)));
                    }
                    s = bind::fapp (singleCons, argsCons);

                  }
                  else
                  {
                    s = bind::mkConst(mkTerm<string> ("_x_" + to_string(i), efac), indConstructor->arg(i));
                  }
                }
                args.push_back(s);
              }
              indCon = bind::fapp(indConstructor, args);
              break;
            }
          }
        }
      }

      adtType = bind::typeOf(indCon);
      ExprVector empt;
      for (auto & a : constructors) if (a->arity() == 2) baseCon = bind::fapp (a, empt);

      assert(adtType == bind::typeOf(indCon));

      if (stateProducingOp == -1) stateProducingOp = findStateProducingOpInAssms();
      if (stateConsumingOp == -1) stateConsumingOp = findStateConsumingOpInAssms();
      assert(stateProducingOp >= 0);
      assert(stateConsumingOp >= 0);
      if (indConIndex == -1) indConIndex = stateConsumingOp;  // for the case of crafted ind constructors

      for (stateNoOp = 0; stateNoOp < opsAdt.size(); stateNoOp++)
      {
        if (stateNoOp != stateProducingOp &&
            stateNoOp != stateConsumingOp)
        {
          break;
        }
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
      Expr baseApp = bind::fapp (rel, argsBase);
      Expr baseDef = mk<EQ>(baseApp, baseFormula);
      // create a quantified formula representing the base rule of R
      baseRule = createQuantifiedFormula(baseDef);

      // prepare for the inductive rule construction
      ExprSet indexVars;
      getCounters (opsArr[indConIndex], indexVars);
      indexVar = *indexVars.begin(); // proceed with the least one
      indexVar = replaceAllRev(indexVar, varVersions);

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
          accessTerm = replaceAllRev(tr->right(), varVersions);
          if (indConIndex == stateConsumingOp)    // maybe will need to be treated more carefully
            accessTerm = swapPlusMinusConst(accessTerm);
        }
        else
        {
          ExprSet cnj;
          getConj(rewriteSelectStore(tr), cnj);
          for (auto & a : cnj)
            if (isOpX<EQ>(a) && isOpX<SELECT>(a->right()))
              arrayContent[a->left()].insert(replaceAllRev(a->right()->last(), varVersions));
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

      // check lemmas first
      assumptions.push_back(baseRule);
      assumptions.push_back(indRule);
      
      for (auto it = extraLemmas.begin(); it != extraLemmas.end(); )
      {
        if (prove(assumptions, *it))
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
      
      // extraLemmas are added to assumptions at the very end (to accelerate solving)
      // however, for some cases it could be needed to use extraLemmas to prove some other extraLemmas
      assumptions.insert(assumptions.end(), extraLemmas.begin(), extraLemmas.end());
    }

    bool prove (ExprVector lemmas, Expr fla, int rounds = 2, bool print = false)
    {
      ADTSolver sol (fla, lemmas, constructors, 7, 2, 3, 1, print); // last false is for verbosity
      return isOpX<FORALL>(fla) ? sol.solve() : sol.solveNoind(rounds);
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
        {
          if (nonstateVars.size() > 1)
          {
            pre.insert(mk<EQ>(mk<MOD>(argsInd[indexVarInd], all), mkTerm (mpz_class (i), efac)));
          }
        }
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

    void printSol()
    {
      u.serialize_formula (baseRule);
      u.serialize_formula (indRule);
    }
  };
}

#endif
