#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearnerV2.hpp"

#ifdef HAVE_ARMADILLO
#include "DataLearner.hpp"
#endif

using namespace std;
using namespace boost;
namespace ufo
{
  struct ArrAccessIter
  {
    bool grows;
    Expr iter;
    Expr qv;
    Expr precond;
    Expr postcond;
    Expr range;
    bool closed;
    vector<int> mbp;
  };

  static bool (*weakeningPriorities[])(Expr, tribool) =
  {
    [](Expr cand, tribool val) { return bool(!val); },
    [](Expr cand, tribool val) { return indeterminate(val) && containsOp<FORALL>(cand); },
    [](Expr cand, tribool val) { return indeterminate(val); }
  };

  class RndLearnerV3 : public RndLearnerV2
  {
    protected:

    ExprSet checked;
    set<HornRuleExt*> propped;
    map<int, ExprVector> candidates;
    map<int, ExprSet> tmpFailed;
    bool boot = true;
    int mut, dat, to;
    map<int, Expr> ssas, prefs;
    map<int, vector<ArrAccessIter* >> qvits; // per cycle
    map<int, ExprSet> qvars;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, unsigned _to,
                  bool freqs, bool aggp, int _mu, int _da, int debug) :
      RndLearnerV2 (efac, z3, r, _to, freqs, aggp, debug),
                  mut(_mu), dat(_da), to(_to) {}

    bool checkInit(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isFact && hr.dstRelation == rel)
        {
          adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    bool checkInductiveness(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        bool checkedSrc = find(checked.begin(), checked.end(), hr.srcRelation) != checked.end();
        bool checkedDst = find(checked.begin(), checked.end(), hr.dstRelation) != checked.end();
        if ((hr.srcRelation == rel && hr.dstRelation == rel) ||
            (hr.srcRelation == rel && checkedDst) ||
            (hr.dstRelation == rel && checkedSrc) ||
            (checkedSrc && checkedDst) ||
            (hr.isFact && checkedDst))
        {
          if (!hr.isQuery) adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    ArrAccessIter* getQvit (int invNum, Expr it)
    {
      for (auto a : qvits[invNum]) if (a->qv == it) return a;
      return NULL;
    }

    Expr actualizeQV (int invNum, Expr cand)
    {
      assert(isOpX<FORALL>(cand));
      Expr ranges = cand->last()->left();
      ExprMap repls;
      for (int i = 0; i < cand->arity()-1; i++)
      {
        auto qv = bind::fapp(cand->arg(i));
        for (auto a : qvits[invNum])
        {
          if (u.implies(ranges, replaceAll(a->range, a->qv, qv)))
          {
            repls[qv->left()] = a->qv->left();
            continue;
          }
        }
      }
      return replaceAll(cand, repls);
    }

    Expr renameCand(Expr newCand, ExprVector& varsRenameFrom, int invNum)
    {
      newCand = replaceAll(newCand, varsRenameFrom, invarVarsShort[invNum]);
      return newCand;
    }

    Expr eliminateQuantifiers(Expr e, ExprVector& varsRenameFrom, int invNum, bool bwd)
    {
      Expr eTmp = keepQuantifiersRepl(e, varsRenameFrom);
      eTmp = weakenForHardVars(eTmp, varsRenameFrom);
      if (bwd) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(/*simplifyArithm*/(eTmp /*, false, true*/));
      eTmp = unfoldITE(eTmp);
      eTmp = renameCand(eTmp, varsRenameFrom, invNum);
      if (printLog >= 4)
      {
        outs () << "       QE [keep vars  "; pprint(varsRenameFrom); outs () << "]\n"; pprint(e, 9);
        outs () << "       QE res:\n"; pprint(eTmp, 9);
      }
      return eTmp;
    }

    void addPropagatedArrayCands(Expr rel, int invNum, Expr candToProp)
    {
      vector<int>& tmp = ruleManager.getCycleForRel(rel);
      if (tmp.size() != 1) return; // todo: support

      Expr fls = candToProp->last()->right();
      for (auto & q : qvits[invNum])
        fls = replaceAll(fls, q->qv, q->iter);
      Expr bdy = rewriteSelectStore(ruleManager.chcs[tmp[0]].body);

      ExprVector ev;
      for (int h = 0; h < ruleManager.chcs[tmp[0]].dstVars.size(); h++)
      {
        Expr var = ruleManager.chcs[tmp[0]].srcVars[h];
        bool pushed = false;
        for (auto & q : qvits[invNum])
        {
          if (q->iter == var)
          {
            ev.push_back(var);
            pushed = true;
          }
        }
        if (!pushed) ev.push_back(ruleManager.chcs[tmp[0]].dstVars[h]);
      }

      ExprSet cnjs;
      Expr newCand2;
      cnjs.clear();
      getConj(eliminateQuantifiers(mk<AND>(fls, bdy), ev, invNum, false), cnjs);
      for (auto & c : cnjs)
      {
        if (u.isTrue(c) || u.isFalse(c)) continue;
        Expr e = ineqNegReverter(c);
        if (isOp<ComparissonOp>(e))
        {
          for (auto & q : qvits[invNum])
          {
            if (containsOp<ARRAY_TY>(e) && !emptyIntersect(q->iter, e))
            {
              e = replaceAll(e, q->iter, q->qv);
              e = renameCand(e, ruleManager.chcs[tmp[0]].dstVars, invNum);

              // workaround: it works only during bootstrapping now
              arrCands[invNum].insert(e);
            }
          }
        }
      }
    }

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, Expr relFrom,
                      ExprVector& varsRenameFrom, Expr rel, bool seed, bool fwd)
    {
      if (!containsOp<FORALL>(candToProp) && !u.isSat(candToProp, constraint))
        return false; // sometimes, maybe we should return true.

      int invNum = getVarIndex(rel, decls);
      int invNumFrom = getVarIndex(relFrom, decls);

      if (containsOp<FORALL>(candToProp))
      {
        // GF: not tested for backward propagation
        if (fwd == false) return true;
        bool fin = finalizeArrCand(candToProp, constraint, invNumFrom);   // enlarge range, if possible
        auto candsTmp = candidates;
        Expr newCand = getForallCnj(eliminateQuantifiers(
                          mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
        newCand = actualizeQV(invNum, newCand);
        if (newCand == NULL) return true;
        candidates[invNum].push_back(newCand);

        bool res = checkCand(invNum, false) &&
                   propagateRec(rel, conjoin(candidates[invNum], m_efac), false);

        if (fin && isOpX<FORALL>(candToProp))
        {
          assert (isOpX<FORALL>(candToProp));
          Expr qvar = getQvit(invNumFrom, bind::fapp(candToProp->arg(0)))->qv; // TODO: support nested loops with several qvars

          addPropagatedArrayCands(rel, invNum, candToProp);  // unclear, why?
          if (!candidates[invNum].empty()) return res;

          for (auto & q : qvits[invNum])            // generate regress candidates
          {
            Expr newCand1 = replaceAll(newCand, qvar->last(), q->qv->last());
            ExprVector newCands;
            replaceArrRangeForIndCheck(invNum, newCand1, newCands, /* regress == */ true);
            if (newCands.empty()) continue;
            newCand1 = newCands[0]; // TODO: extend
            candidates = candsTmp;
            candidates[invNum].push_back(newCand1);
            if (checkCand(invNum, false) &&
                propagateRec(rel, conjoin(candidates[invNum], m_efac), false))
              res = true;
          }
        }
        return res;
      }

      Expr newCand = eliminateQuantifiers(
                     (fwd ? mk<AND>(candToProp, constraint) :
                            mk<AND>(constraint, mkNeg(candToProp))),
                                    varsRenameFrom, invNum, !fwd);
      ExprSet cnjs;
      getConj(newCand, cnjs);
      addCandidates(rel, cnjs);

      if (seed)
      {
        if (u.isTrue(newCand)) return true;
        else return propagateRec(rel, newCand, true);
      }
      else
      {
        checkCand(invNum, false);
        return propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
      }
    }

    bool addCandidate(int invNum, Expr cnd)
    {
      if (printLog >= 3) outs () << "Adding candidate [" << invNum << "]: " << cnd << "\n";
      SamplFactory& sf = sfs[invNum].back();
      Expr allLemmas = sf.getAllLemmas();
      if (containsOp<FORALL>(cnd) || containsOp<FORALL>(allLemmas))
      {
        if (containsOp<FORALL>(cnd))
          replaceArrRangeForIndCheck (invNum, cnd, candidates[invNum]);
        else
          candidates[invNum].push_back(cnd);
        return true;
      }
      if (!isOpX<TRUE>(allLemmas) && u.implies(allLemmas, cnd)) return false;

      for (auto & a : candidates[invNum])
        if (a == cnd) return false;
      candidates[invNum].push_back(cnd);
      return true;
    }

    void addCandidates(Expr rel, ExprSet& cands)
    {
      int invNum = getVarIndex(rel, decls);
      for (auto & a : cands) addCandidate(invNum, a);
    }

    bool finalizeArrCand(Expr& cand, Expr constraint, int invNum)
    {
      // only forward currently
      if (!isOpX<FORALL>(cand)) return false;
      if (!containsOp<ARRAY_TY>(cand)) return false;

      Expr invs = conjoin(sfs[invNum].back().learnedExprs, m_efac);
      ExprSet cnj;
      for (int i = 0; i < cand->arity()-1; i++)
      {
        Expr qv = bind::fapp(cand->arg(i));
        auto q = getQvit(invNum, qv);
        if (u.isSat(invs, replaceAll(q->range, q->qv, q->iter), constraint))
          return false;
        else
          getConj(q->range, cnj);
      }

      cand = replaceAll(cand, cand->last()->left(), conjoin(cnj, m_efac));
      return true;
    }

    Expr getForallCnj (Expr cands)
    {
      ExprSet cnj;
      getConj(cands, cnj);
      for (auto & cand : cnj)
        if (isOpX<FORALL>(cand)) return cand;
      return NULL;
    }

    void replaceArrRangeForIndCheck(int invNum, Expr cand, ExprVector& cands,
      bool regress = false)
    {
      assert(isOpX<FORALL>(cand));
      ExprSet cnjs;
      getConj(cand->last()->left(), cnjs);
      for (int i = 0; i < cand->arity()-1; i++)
      {
        auto qv = bind::fapp(cand->arg(i));
        auto str = getQvit(invNum, qv);
        Expr itRepl = str->iter;

        if (contains(cand->last()->right(), qv))
        {
          if      (str->grows && regress)   cnjs.insert(mk<GEQ>(qv, itRepl));
          else if (str->grows && !regress)  cnjs.insert(mk<LT>(qv, itRepl));
          else if (!str->grows && regress)  cnjs.insert(mk<LEQ>(qv, itRepl));
          else if (!str->grows && !regress) cnjs.insert(mk<GT>(qv, itRepl));
        }
        else
        {
          for (auto it = cnjs.begin(); it != cnjs.end(); )
          {
            if (contains (*it, qv)) it = cnjs.erase(it);
            else ++it;
          }
        }
        cands.push_back(simplifyQuants(
          replaceAll(cand, cand->last()->left(), conjoin(cnjs, m_efac))));
      }
    }

    bool propagate(int invNum, Expr cand, bool seed) {
      return propagate(decls[invNum], cand, seed);
    }

    bool propagate(Expr rel, Expr cand, bool seed)
    {
      propped.clear();
      checked.clear();
      return propagateRec(rel, cand, seed);
    }

    bool propagateRec(Expr rel, Expr cand, bool seed)
    {
      if (printLog >= 3) outs () << "     Propagate:   " << cand << "\n";
      bool res = true;
      checked.insert(rel);
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery || hr.isFact) continue;

        // forward:
        if (hr.srcRelation == rel && find(propped.begin(), propped.end(), &hr) == propped.end())
        {
          if (hr.isInductive && ruleManager.hasArrays[rel]) continue;     // temporary workarond
          propped.insert(&hr);
          SamplFactory* sf1 = &sfs[getVarIndex(hr.srcRelation, decls)].back();
          Expr replCand = replaceAllRev(cand, sf1->lf.nonlinVars);
          replCand = replaceAll(replCand, ruleManager.invVars[rel], hr.srcVars);
          res = res && getCandForAdjacentRel (replCand, hr.body, rel, hr.dstVars, hr.dstRelation, seed, true);
        }
        // backward (very similarly):
        if (hr.dstRelation == rel && find(propped.begin(), propped.end(), &hr) == propped.end())
        {
          propped.insert(&hr);
          SamplFactory* sf2 = &sfs[getVarIndex(hr.dstRelation, decls)].back();
          Expr replCand = replaceAllRev(cand, sf2->lf.nonlinVars);
          replCand = replaceAll(replCand, ruleManager.invVars[rel], hr.dstVars);
          res = res && getCandForAdjacentRel (replCand, hr.body, rel, hr.srcVars, hr.srcRelation, seed, false);
        }
      }
      return res;
    }

    bool checkCand(int invNum, bool propa = true)
    {
      Expr rel = decls[invNum];
      if (!checkInit(rel)) return false;
      if (!checkInductiveness(rel)) return false;

      return !propa || propagate(invNum, conjoin(candidates[invNum], m_efac), false);
    }

    void addLemma (int invNum, SamplFactory& sf, Expr l)
    {
      if (printLog)
        outs () << "Added lemma for " << decls[invNum] << ": " << l
                << (printLog >= 2 ? " 👍\n" : "\n");
      sf.learnedExprs.insert(l);
    }

    // a simple method to generate properties of a larger Array range,
    // given already proven ranges
    void generalizeArrInvars (int invNum, SamplFactory& sf)
    {
      if (sf.learnedExprs.size() > 1)
      {
        ExprVector posts;
        ExprVector pres;
        map<Expr, ExprVector> tmp;
        ExprVector tmpVars;
        ExprVector arrVars;
        Expr tmpIt = bind::intConst(mkTerm<string> ("_tmp_it", m_efac));

        for (auto & a : sf.learnedExprs)
        {
          if (!isOpX<FORALL>(a)) continue;
          Expr learnedQF = a->last();
          if (!isOpX<IMPL>(learnedQF)) continue;
          ExprVector se;
          filter (learnedQF->last(), bind::IsSelect (), inserter(se, se.begin()));

          // filter out accesses via non-quantified indeces
          for (auto it = se.begin(); it != se.end();)
          {
            bool found = false;
            for (int i = 0; i < a->arity(); i++)
            {
              if (contains(se[0]->right(), a->arg(0)))
              {
                found = true;
                break;
              }
            }
            if (!found) it = se.erase(it);
            else ++it;
          }

          bool multipleIndex = false;
          for (auto & s : se) {
            if (se[0]->right() != s->right()) {
              multipleIndex = true;
              break;
            }
          }

          if (se.size() == 0 || multipleIndex) continue;

          if (arrVars.size() == 0) {
            for (int index = 0; index < se.size(); index++) {
              arrVars.push_back(se[index]->left());
              tmpVars.push_back(cloneVar(se[index],
                mkTerm<string> ("_tmp_var_" + lexical_cast<string>(index), m_efac)));
            }
          } else {
            bool toContinue = false;
            for (auto & s : se) {
              if (find(arrVars.begin(), arrVars.end(), s->left()) == arrVars.end()) {
                toContinue = true;
                break;
              }
            }
            if (toContinue) continue;
          }

          Expr postReplaced = learnedQF->right();
          for (int index = 0; index < se.size() && index < tmpVars.size(); index++)
          postReplaced = replaceAll(postReplaced, se[index], tmpVars[index]);

          ExprSet postVars;
          filter(postReplaced, bind::IsConst(), inserter(postVars, postVars.begin()));
          for (auto & fhVar : sf.lf.getVars()) postVars.erase(fhVar);
          for (auto & tmpVar : tmpVars) postVars.erase(tmpVar);
          if (postVars.size() > 0)
          {
            AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(postReplaced, mk<EQ>(tmpIt, se[0]->right())), postVars);
            if (ae.solve())
            {
              Expr pr = ae.getValidSubset();
              ExprSet conjs;
              getConj(pr, conjs);
              if (conjs.size() > 1)
              {
                for (auto conjItr = conjs.begin(); conjItr != conjs.end();)
                {
                  ExprVector conjVars;
                  filter (*conjItr, bind::IsConst(), inserter(conjVars, conjVars.begin()));
                  bool found = false;
                  for (auto & conjVar : conjVars)
                  {
                    if (find (tmpVars.begin(), tmpVars.end(), conjVar) != tmpVars.end())
                    {
                      found = true;
                      break;
                    }
                  }
                  if (!found) conjItr = conjs.erase(conjItr);
                  else ++conjItr;
                }
              }
              postReplaced = conjoin(conjs, m_efac);
            }
          }

          pres.push_back(learnedQF->left());
          posts.push_back(postReplaced);
          tmp[mk<AND>(learnedQF->left(), postReplaced)].push_back(se[0]->right());
        }

        if (tmp.size() > 0)
        {
          for (auto & a : tmp)
          {
            if (a.second.size() > 1)
            {
              Expr disjIts = mk<FALSE>(m_efac);
              for (auto & b : a.second) disjIts = mk<OR>(disjIts, mk<EQ>(tmpIt, b));
              ExprSet elementaryIts;
              filter (disjIts, bind::IsConst (), inserter(elementaryIts, elementaryIts.begin()));
              for (auto & a : sf.lf.getVars()) elementaryIts.erase(a);
              elementaryIts.erase(tmpIt);
              if (elementaryIts.size() == 1)
              {
                AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(disjIts, a.first->left()), elementaryIts);
                if (ae.solve())
                {
                  ExprVector args;
                  Expr it = *elementaryIts.begin();
                  args.push_back(it->left());
                  Expr newPre = replaceAll(ae.getValidSubset(), tmpIt, it);
                  Expr newPost = replaceAll(a.first->right(), tmpIt, it);
                  for (int index = 0; index < tmpVars.size() && index < arrVars.size(); index++)
                  newPost = replaceAll(newPost, tmpVars[index], mk<SELECT>(arrVars[index], it));
                  args.push_back(mk<IMPL>(newPre, newPost));
                  Expr newCand = mknary<FORALL>(args);
                  addLemma(invNum, sf, newCand);
                }
              }
            }
          }
        }
      }
    }

    void assignPrioritiesForLearned()
    {
      for (auto & cand : candidates)
      {
        if (cand.second.size() > 0)
        {
          SamplFactory& sf = sfs[cand.first].back();
          for (auto b : cand.second)
          {
            b = simplifyArithm(b);
            if (!statsInitialized || containsOp<ARRAY_TY>(b)
                    || containsOp<BOOL_TY>(b) || findNonlin(b))
              addLemma(cand.first, sf, b);
            else
            {
              Expr learnedCand = normalizeDisj(b, invarVarsShort[cand.first]);
              Sampl& s = sf.exprToSampl(learnedCand);
              sf.assignPrioritiesForLearned();
              if (!u.implies(sf.getAllLemmas(), learnedCand))
                addLemma(cand.first, sf, learnedCand);
            }
          }
        }
      }
    }

    void deferredPriorities()
    {
      for (auto & dcl: ruleManager.wtoDecls)
      {
        int invNum = getVarIndex(dcl, decls);
        SamplFactory& sf = sfs[invNum].back();
        for (auto & l : sf.learnedExprs)
        {
          if (containsOp<ARRAY_TY>(l) || findNonlin(l) || containsOp<BOOL_TY>(l))
            continue;
          Expr learnedCand = normalizeDisj(l, invarVarsShort[invNum]);
          Sampl& s = sf.exprToSampl(learnedCand);
          sf.assignPrioritiesForLearned();
        }
        for (auto & failedCand : tmpFailed[invNum])
        {
          Sampl& s = sf.exprToSampl(failedCand);
          sf.assignPrioritiesForFailed();
        }
      }
    }

    virtual bool synthesize(unsigned maxAttempts)
    {
      if (printLog) outs () << "\nSAMPLING\n========\n";

      ExprSet cands;
      bool rndStarted = false;
      int lsz = ruleManager.loopheads.size();
      for (int i = 0; i < maxAttempts; i++)
      {
        // next cand (to be sampled)
        // TODO: find a smarter way to calculate; make parametrizable
        Expr rel = ruleManager.loopheads[i % lsz];
        int invNum = getVarIndex(rel, decls);
        candidates.clear();
        SamplFactory& sf = sfs[invNum].back();
        Expr cand = sf.getFreshCandidate();
        if (cand == NULL) {
          outs() << "cand is NULL\n";
          exit(1);
        }
        if (cand != NULL && isOpX<FORALL>(cand) && isOpX<IMPL>(cand->last()))
        {
          if (!u.isSat(cand->last()->left())) cand = NULL;
        }
        if (cand == NULL) continue;
        if (printLog) outs () << " - - - Sampled cand (#" << i << ") for "
                  << decls[invNum] << ": "
                              << cand << (printLog >= 3 ? " 😎\n" : "\n");
        if (!addCandidate(invNum, cand)) continue;

        bool lemma_found = checkCand(invNum);
        if (lemma_found)
        {
          assignPrioritiesForLearned();
          generalizeArrInvars(invNum, sf);
          if (checkAllLemmas())
          {
            outs () << "Success after " << (i+1) << " iterations\n";
            printSolution();
            return true;
          }
        }
      }
      outs() << "unknown\n";
      return false;
    }

    virtual bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          for (auto & hr : ruleManager.chcs)
          {
            if (hr.dstRelation == decls[i]) worklist.push_back(&hr);
          }
        }
      }

      // basically, just checks initiation and immediately removes bad candidates
      multiHoudini(worklist, false);

      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          ExprVector cur;
          deque<Expr> def;
          u.splitUnsatSets(candidates[i], cur, def);
          candidates[i] = cur;
        }
      }

      return true;
    }

    virtual bool weaken (int invNum, ExprVector& ev,
                 map<Expr, tribool>& vals, HornRuleExt* hr, SamplFactory& sf,
                 function<bool(Expr, tribool)> cond, bool singleCand)
    {
      bool weakened = false;
      for (auto it = ev.begin(); it != ev.end(); )
      {
        if (cond(*it, vals[*it]))
        {
          weakened = true;
          if (printLog >= 3) outs () << "    Failed cand for " << hr->dstRelation << ": " << *it << " 🔥\n";
          if (hr->isFact && !containsOp<ARRAY_TY>(*it) && !containsOp<BOOL_TY>(*it) && !findNonlin(*it))
          {
            Expr failedCand = normalizeDisj(*it, invarVarsShort[invNum]);
            if (statsInitialized)
            {
              Sampl& s = sf.exprToSampl(failedCand);
              sf.assignPrioritiesForFailed();
            }
            else tmpFailed[invNum].insert(failedCand);
          }
          it = ev.erase(it);
          if (singleCand) break;
        }
        else
        {
          ++it;
        }
      }
      return weakened;
    }

    bool multiHoudini (vector<HornRuleExt*> worklist, bool recur = true)
    {
      if (printLog >= 3) outs () << "MultiHoudini\n";
      if (printLog >= 4) printCands();

      bool res1 = true;
      for (auto &hr: worklist)
      {
        if (printLog >= 3) outs () << "  Doing CHC check (" << hr->srcRelation << " -> "
                                   << hr->dstRelation << ")\n";
        if (hr->isQuery) continue;
        tribool b = checkCHC(*hr, candidates);
        if (b || indeterminate(b))
        {
          if (printLog >= 3) outs () << "    CHC check failed\n";
          int invNum = getVarIndex(hr->dstRelation, decls);
          SamplFactory& sf = sfs[invNum].back();

          map<Expr, tribool> vals;
          for (auto & cand : candidates[invNum])
          {
            Expr repl = cand;
            repl = replaceAll(repl, invarVarsShort[invNum], hr->dstVars);
            vals[cand] = u.eval(repl);
          }

          // first try to remove candidates immediately by their models (i.e., vals)
          // then, invalidate (one-by-one) all candidates for which Z3 failed to find a model

          for (int i = 0; i < 3 /*weakeningPriorities.size() */; i++)
            if (weaken (invNum, candidates[invNum], vals, hr, sf, (*weakeningPriorities[i]), i > 0))
              break;

          if (recur)
          {
            res1 = false;
            break;
          }
        }
        else if (printLog >= 3) outs () << "    CHC check succeeded\n";
      }
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool findInvVar(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));

      for (auto & v : vars)
      {
        bool found = false;
        for (auto & w : invarVars[invNum])
        {
          if (w.second == v)
          {
            found = true;
            break;
          }
        }
        if (!found)
        {
          if (find (ve.begin(), ve.end(), v) == ve.end())
            return false;
        }
      }
      return true;
    }

    // based on the version from early Aug 2021
    void doSeedMining(Expr invRel, ExprSet& cands, set<cpp_int>& progConsts,
                        set<cpp_int>& intCoefs)
    {
      int invNum = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[invNum].back();
      ExprSet candsFromCode;
      bool analyzedExtras = false;
      bool isFalse = false;
      bool hasArrays = false;

      // for Arrays
      ExprSet tmpArrAccess;
      ExprSet tmpArrSelects;
      ExprSet tmpArrCands;
      ExprSet tmpArrFuns;
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;
        SeedMiner sm (hr, invRel, invarVars[invNum], sf.lf.nonlinVars);

        sm.analyzeCode();
        if (!analyzedExtras && hr.srcRelation == invRel)
        {
          sm.analyzeExtras (cands);
          analyzedExtras = true;
        }
        for (auto &cand : sm.candidates) candsFromCode.insert(cand);

        // for arrays
        if (ruleManager.hasArrays[invRel])
        {
          tmpArrCands.insert(sm.arrCands.begin(), sm.arrCands.end());
          tmpArrSelects.insert(sm.arrSelects.begin(), sm.arrSelects.end());
          tmpArrFuns.insert(sm.arrFs.begin(), sm.arrFs.end());
          hasArrays = true;
        }
      }

      if (hasArrays)
      {

        for (int qNum = 0; qNum < qvits[invNum].size(); qNum++)
        {
          auto & q = qvits[invNum][qNum];

          // repair behavioral arrCands
          if (!arrCands[invNum].empty())
          {
            ExprSet repCands;
            for (auto & a : arrCands[invNum])
              repCands.insert(replaceAll(a, q->iter, q->qv));
            arrCands[invNum] = repCands;
          }
        }

        // TODO: revisit handling of nested loops
        /*
        auto nested = ruleManager.getNestedRel(invRel);
        if (nested != NULL)
        {
          int invNumTo = getVarIndex(nested->dstRelation, decls);
          // only one variable for now. TBD: find if we need more
          Expr qVar2 = bind::intConst(mkTerm<string> ("_FH_nst_it", m_efac));
          arrAccessVars[invNum].push_back(qVar2);
          Expr range = conjoin (arrIterRanges[invNumTo], m_efac);
          ExprSet quantified;
          for (int i = 0; i < nested->dstVars.size(); i++)
          {
            range = replaceAll(range, invarVars[invNumTo][i], nested->dstVars[i]);
            quantified.insert(nested->dstVars[i]);
          }
          // naive propagation of ranges
          ExprSet cnjs;
          getConj(nested->body, cnjs);
          for (auto & a : cnjs)
          {
            for (auto & b : quantified)
            {
              if (isOpX<EQ>(a) && a->right() == b)
              {
                range = replaceAll(range, b, a->left());
              }
              else if (isOpX<EQ>(a) && a->left() == b)
              {
                range = replaceAll(range, b, a->right());
              }
            }
          }
          arrIterRanges[invNum].insert(
                replaceAll(replaceAll(range, *arrAccessVars[invNumTo].begin(), qVar2),
                      q->iter, *arrAccessVars[invNum].begin()));
        }
         */

        // process all quantified seeds
        for (auto & a : tmpArrCands)
        {
          if (u.isTrue(a) || u.isFalse(a)) continue;
          Expr replCand = replaceAllRev(a, sf.lf.nonlinVars);
          ExprSet allVars;
          getExtraVars(replCand, ruleManager.invVars[invRel], allVars);
          if (allVars.size() < 2 &&
              !u.isTrue(replCand) && !u.isFalse(replCand))
          {
            if (allVars.empty())
            {
              candsFromCode.insert(replCand);
              for (auto & q : qvits[invNum])
                replCand = replaceAll(replCand, q->iter, q->qv);
              arrCands[invNum].insert(replCand);
            }
            else
              for (auto & q : qvits[invNum])
                if (typeOf(*allVars.begin()) == typeOf(q->qv))
                  arrCands[invNum].insert(replaceAll(replCand, *allVars.begin(), q->qv));
          }
        }
      }

      // process all quantifier-free seeds
      cands = candsFromCode;
      for (auto & cand : candsFromCode)
      {
        Expr replCand = replaceAllRev(cand, sf.lf.nonlinVars);
        addCandidate(invNum, replCand);
      }
    }

    void getQVcands(int invNum, Expr replCand, ExprSet& cands)
    {
      ExprVector se;
      filter (replCand, bind::IsSelect (), inserter(se, se.begin()));
      bool found = false;
      for (auto & q : qvits[invNum])
      {
        if (!contains(conjoin(se, m_efac), q->iter)) continue;
        found = true;
        Expr replTmp = replaceAll(replCand, q->iter, q->qv);
        cands.insert(replCand);
        getQVcands(invNum, replTmp, cands);
      }
      if (!found)
      {
        cands.insert(replCand);
      }
    }

    bool anyProgress(vector<HornRuleExt*> worklist)
    {
      for (int i = 0; i < invNumber; i++)
        // subsumption check
        for (auto & hr : worklist)
          if (hr->srcRelation == decls[i] || hr->dstRelation == decls[i])
            if (candidates[i].size() > 0)
              if (!u.implies (conjoin(sfs[i].back().learnedExprs, m_efac),
                conjoin(candidates[i], m_efac)))
                  return true;
      return false;
    }

    void getArrRanges(map<Expr, ExprVector>& m)
    {
      for (auto & dcl : decls)
        for (auto q : qvits[getVarIndex(dcl, decls)])
          if (q->closed)
            m[dcl].push_back (q->grows ?
              mk<MINUS>(q->postcond, q->precond) :
              mk<MINUS>(q->precond, q->postcond));
    }

    void filterTrivCands(ExprSet& tmp) // heuristics for incremental DL
    {
      for (auto it = tmp.begin(); it != tmp.end();)
        if (u.hasOneModel(*it))
          it = tmp.erase(it);
        else
          ++it;
    }

    virtual void addDataCand(int invNum, Expr cand, ExprSet& cands)
    {
      cands.insert(cand);
    }

    void getDataCandidates(map<Expr, ExprSet>& cands, Expr srcRel = NULL,
                           Expr phaseGuard = NULL, Expr invs = NULL, bool fwd = true){
#ifdef HAVE_ARMADILLO
      if (printLog && phaseGuard == NULL) outs () << "\nDATA LEARNING\n=============\n";
      if (phaseGuard == NULL) assert(invs == NULL && srcRel == NULL);
      DataLearner dl(ruleManager, m_z3, to, printLog);
      vector<map<Expr, ExprSet>> poly;
      if (phaseGuard == NULL)
      {
        // run at the beginning, compute data once
        map<Expr, ExprVector> m;
        getArrRanges(m);
        map<Expr, ExprSet> constr;
        for (int i = 0; i < dat; i++)
        {
          if (!dl.computeData(m, constr)) break;
          poly.push_back(map<Expr, ExprSet>());
          for (auto & dcl : decls)
          {
            ExprSet tmp;
            dl.computePolynomials(dcl, tmp);
            simplify(tmp);
            poly.back()[dcl] = tmp;
            filterTrivCands(tmp);
            constr[dcl].insert(conjoin(tmp, m_efac));
          }
        }
      }
      else
      {
        // run at `generatePhaseLemmas`
        for (auto & dcl : decls)
        {
          if (srcRel == dcl)
          {
            ExprSet constr;
            for (int i = 0; i < dat; i++)
            {
              poly.push_back(map<Expr, ExprSet>());
              dl.computeDataSplit(srcRel, phaseGuard, invs, fwd, constr);
              ExprSet tmp;
              dl.computePolynomials(dcl, tmp);
              simplify(tmp);
              poly.back()[dcl] = tmp;
              filterTrivCands(tmp);
              constr.insert(conjoin(tmp, m_efac));
            }
            break;
          }
        }
      }

      if (mut == 0)
      {
        for (auto & c : poly)
          for (auto & p : c)
            for (Expr a : p.second)
            {
              int invNum = getVarIndex(p.first, decls);
              if (containsOp<ARRAY_TY>(a))
                arrCands[invNum].insert(a);
              else
                addDataCand(invNum, a, cands[p.first]);
            }
        return;
      }

      // mutations (if specified)
      for (auto & c : poly)
        for (auto & p : c)
        {
          int invNum = getVarIndex(p.first, decls);
          ExprSet tmp, its;
          if (mut == 1 && ruleManager.hasArrays[p.first])   // heuristic to remove cands irrelevant to counters and arrays
          {
            for (auto q : qvits[invNum]) its.insert(q->iter);
            for (auto it = p.second.begin(); it != p.second.end();)
              if (emptyIntersect(*it, its))
                it = p.second.erase(it);
              else
                ++it;
          }
          mutateHeuristicEq(p.second, tmp, p.first, (phaseGuard == NULL));
          for (auto & c : tmp)
            addDataCand(invNum, c, cands[p.first]);
        }
#else
      if (printLog) outs() << "Skipping learning from data as required library (armadillo) not found\n";
#endif
    }

    void mutateHeuristicEq(ExprSet& src, ExprSet& dst, Expr dcl, bool toProp)
    {
      int invNum = getVarIndex(dcl, decls);
      ExprSet src2;
      map<Expr, ExprVector> substs;
      Expr (*ops[])(Expr, Expr) = {mk<PLUS>, mk<MINUS>};        // operators used in the mutations

      for (auto a1 = src.begin(); a1 != src.end(); ++a1)
        if (isNumericEq(*a1))
        {
          for (auto a2 = std::next(a1); a2 != src.end(); ++a2)    // create various combinations
            if (isNumericEq(*a2))
            {
              const ExprVector m1[] = {{(*a1)->left(), (*a2)->left()}, {(*a1)->left(), (*a2)->right()}};
              const ExprVector m2[] = {{(*a1)->right(), (*a2)->right()}, {(*a1)->right(), (*a2)->left()}};
              for (int i : {0, 1})
                for (Expr (*op) (Expr, Expr) : ops)
                  src2.insert(simplifyArithm(normalize(
                    mk<EQ>((*op)(m1[i][0], m1[i][1]), (*op)(m2[i][0], m2[i][1])))));
            }

          // before pushing them to the cand set, we do some small mutations to get rid of specific consts
          Expr a = simplifyArithm(normalize(*a1));
          if (isOpX<EQ>(a) && isIntConst(a->left()) &&
              isNumericConst(a->right()) && lexical_cast<string>(a->right()) != "0")
            substs[a->right()].push_back(a->left());
          src2.insert(a);
        }

      bool printedAny = false;
      if (printLog >= 2) outs () << "Mutated candidates:\n";
      for (auto a : src2)
        if (!u.isFalse(a) && !u.isTrue(a))
        {
          if (printLog >= 2) { outs () << "  " << a << "\n"; printedAny = true; }

          if (containsOp<ARRAY_TY>(a))
            arrCands[invNum].insert(a);
          else
            dst.insert(a);

          if (isNumericConst(a->right()))
          {
            cpp_int i1 = lexical_cast<cpp_int>(a->right());
            for (auto b : substs)
            {
              cpp_int i2 = lexical_cast<cpp_int>(b.first);

              if (i1 % i2 == 0 && i1/i2 != 0)
                for (auto c : b.second)
                {
                  Expr e = simplifyArithm(normalize(mk<EQ>(a->left(), mk<MULT>(mkMPZ(i1/i2, m_efac), c))));
                  if (!u.isSat(mk<NEG>(e))) continue;
                  if (containsOp<ARRAY_TY>(e))
                    arrCands[invNum].insert(e);
                  else
                    dst.insert(e);

                  if (printLog >= 2) { outs () << "  " << e << "\n"; printedAny = true; }
                }
            }
          }
        }
      if (printLog >= 2 && !printedAny) outs () << "  none\n";
    }

    virtual bool simplLemmas() { return true; }

    virtual void postBootCands(int invNum, Expr c, Expr cand) {}

    bool bootstrap()
    {
      if (printLog) outs () << "\nBOOTSTRAPPING\n=============\n";
      filterUnsat();

      if (multiHoudini(ruleManager.dwtoCHCs))
      {
        assignPrioritiesForLearned();
        if (checkAllLemmas())
        {
          outs () << "Success after bootstrapping\n";
          printSolution();
          return true;
        }
      }

      if (simplLemmas()) simplifyLemmas();
      boot = false;

      // try array candidates one-by-one (adapted from `synthesize`)
      for (auto & dcl: ruleManager.wtoDecls)
      {
        if (ruleManager.hasArrays[dcl])
        {
          int invNum = getVarIndex(dcl, decls);
          SamplFactory& sf = sfs[invNum].back();
          for (auto it = arrCands[invNum].begin(); it != arrCands[invNum].end();
               it = arrCands[invNum].erase(it))
          {
            Expr c = *it;
            if (u.isTrue(c) || u.isFalse(c)) continue;

            Expr cand = sf.af.getQCand(c);
            if (cand->arity() <= 1) continue;

            if (printLog)
              outs () << "- - - Bootstrapped cand for " << dcl << ": "
                      << cand << (printLog >= 3 ? " 😎\n" : "\n");

            auto candidatesTmp = candidates[invNum]; // save for later
            if (!addCandidate(invNum, cand)) continue;
            if (checkCand(invNum))
            {
              assignPrioritiesForLearned();
              generalizeArrInvars(invNum, sf);
              if (checkAllLemmas())
              {
                outs () << "Success after bootstrapping\n";
                printSolution();
                return true;
              }
            }
            else
            {
              postBootCands(invNum, c, cand);
              if (candidates[invNum].empty())
                candidates[invNum] = candidatesTmp;
            }
          }
        }

        // second round of bootstrapping (to be removed after Houdini supports arrays)

        candidates.clear();
        ExprVector empt;
        for (auto &hr: ruleManager.chcs)
        {
          if (hr.isQuery)
          {
            int invNum = getVarIndex(hr.srcRelation, decls);
            ExprSet cnjs;
            getConj(hr.body, cnjs);
            for (auto & a : cnjs)
            {
              if (isOpX<NEG>(a) && findInvVar(invNum, a, empt))
              {
                candidates[invNum].push_back(a->left());
                break;
              }
            }
            break;
          }
        }
        if (multiHoudini(ruleManager.dwtoCHCs))
        {
          assignPrioritiesForLearned();
          if (checkAllLemmas())
          {
            outs () << "Success after bootstrapping\n";
            printSolution();
            return true;
          }
        }
      }

      return false;
    }

    bool checkAllLemmas()
    {
      candidates.clear();
      for (int i = ruleManager.wtoCHCs.size() - 1; i >= 0; i--)
      {
        auto & hr = *ruleManager.wtoCHCs[i];
        tribool b = checkCHC(hr, candidates, true);
        if (b) {
          if (!hr.isQuery)
          {
            if (printLog) outs() << "WARNING: Something went wrong" <<
              (ruleManager.hasArrays[hr.srcRelation] || ruleManager.hasArrays[hr.dstRelation] ?
              " (possibly, due to quantifiers)" : "") <<
              ". Restarting...\n";

            for (int i = 0; i < decls.size(); i++)
            {
              SamplFactory& sf = sfs[i].back();
              for (auto & l : sf.learnedExprs) candidates[i].push_back(l);
              sf.learnedExprs.clear();
            }
            multiHoudini(ruleManager.wtoCHCs);
            assignPrioritiesForLearned();

            return false;
          }
          else
            return false; // TODO: use this fact somehow
        }
        else if (indeterminate(b)) return false;
      }
      return true;
    }

    tribool checkCHC (HornRuleExt& hr, map<int, ExprVector>& annotations,
      bool checkAll = false)
    {
      int srcNum = getVarIndex(hr.srcRelation, decls);
      int dstNum = getVarIndex(hr.dstRelation, decls);

      if (!hr.isQuery)       // shortcuts
      {
        if (dstNum < 0)
        {
          if (printLog >= 3) outs () << "      Trivially true since " << hr.dstRelation << " is not initialized\n";
          return false;
        }
        if (checkAll && annotations[dstNum].empty())
          return false;
      }

      ExprSet exprs = {hr.body};

      if (!hr.isFact)
      {
        ExprSet lms = sfs[srcNum].back().learnedExprs;
        for (auto & a : annotations[srcNum]) lms.insert(a);
        for (auto a : lms)
        {
          a = replaceAll(a, invarVarsShort[srcNum], hr.srcVars);
          exprs.insert(a);
        }
      }

      if (!hr.isQuery)
      {
        ExprSet lms = sfs[dstNum].back().learnedExprs;
        ExprSet negged;
        for (auto & a : annotations[dstNum]) lms.insert(a);
        for (auto a : lms)
        {
          a = replaceAll(a, invarVarsShort[dstNum], hr.dstVars);
          negged.insert(mkNeg(a));
        }
        exprs.insert(disjoin(negged, m_efac));
      }
      return u.isSat(exprs);
    }

    virtual bool updateRanges(int invNum, ArrAccessIter* newer)
    {
      qvits[invNum].push_back(newer);
      return true;
    }

    int qvitNum = 0;
    bool createArrAcc(Expr rel, int invNum, Expr a, bool grows, vector<int>& extMbp, Expr extPref, Expr pre)
    {
      ArrAccessIter* ar = new ArrAccessIter();
      ar->iter = a;
      ar->grows = grows;
      ar->mbp = extMbp;

      ExprSet itersCur = {a};
      AeValSolver ae(mk<TRUE>(m_efac), extPref, itersCur);
      ae.solve();
      Expr skol = u.simplifyITE(ae.getSimpleSkolemFunction(), ae.getValidSubset());
      if (isOpX<TRUE>(skol))
      {
        if (printLog >= 3) outs() << "Preprocessing of counter " << a << " of relation " << rel << " fails  🔥\n";
        return false;
      }
      ar->precond = projectITE (skol, a);
      if (ar->precond == NULL)
      {
        if (printLog >= 3) outs() << "Preprocessing of counter " << a << " of relation " << rel << " fails  🔥\n";
        return false;
      }

      ar->qv = bind::intConst(mkTerm<string>("_FH_arr_it_" + lexical_cast<string>(qvitNum++), m_efac));
      Expr fla = (ar->grows) ? mk<GEQ>(ar->qv, ar->precond) :
                               mk<LEQ>(ar->qv, ar->precond);
      ExprSet tmp;
      getConj(pre, tmp);
      for (auto it = tmp.begin(); it != tmp.end(); )
      {
        if (contains(*it, ar->iter))
        {
          Expr t = ineqSimplifier(ar->iter, *it);     // we need the tightest "opposite" bound; to extend
          if ((ar->grows && (isOpX<LT>(t) || isOpX<LEQ>(t))) ||
             (!ar->grows && (isOpX<GT>(t) || isOpX<GEQ>(t))))
          {
            if (t->left() == ar->iter)
            {
              ar->postcond = t->right();
              ++it;
              continue;
            }
          }
        }
        it = tmp.erase(it);
      }

      ar->closed = tmp.size() > 0;              // flag that the range has lower and upper bounds

      ExprVector invAndIterVarsAll = invarVarsShort[invNum];
      invAndIterVarsAll.push_back(ar->qv);
      ar->range = simplifyArithm(normalizeDisj(mk<AND>(fla,
                 replaceAll(conjoin(tmp, m_efac), ar->iter, ar->qv)), invAndIterVarsAll));

      // keep it, if it is more general than an existing one
      if (updateRanges(invNum, ar))
      {
        arrIterRanges[invNum].insert(ar->range);
        arrAccessVars[invNum].push_back(ar->qv);
        if (printLog >= 2)
          outs () << "Introducing " << ar->qv << " for "
                  << (ar->grows ? "growing" : "shrinking")
                  << " variable " << ar->iter
                  << " with " << (ar->closed ? "closed" : "open")
                  << " range " << ar->range << "\n";
      }
      return true;
    }

    virtual void initializeAux(ExprSet& cands, BndExpl& bnd, Expr dcl, int cycleNum, Expr pref)
    {
      vector<int>& cycle = ruleManager.cycles[dcl][cycleNum];
      HornRuleExt* hr = &ruleManager.chcs[cycle[0]];
      Expr rel = hr->srcRelation;
      ExprVector& srcVars = hr->srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;
      assert(srcVars.size() == dstVars.size());

      int invNum = getVarIndex(rel, decls);
      prefs[invNum] = pref;
      Expr ssac = bnd.toExpr(cycle);
      ssac = replaceAll(ssac, bnd.bindVars.back(), dstVars);
      ssas[invNum] = ssac;
      ssac = rewriteSelectStore(ssac);
      retrieveDeltas(ssac, srcVars, dstVars, cands);

      if (qvits[invNum].size() > 0) return;

      ExprSet ssa;
      if (!containsOp<ARRAY_TY>(ssas[invNum])) return; // todo: support

      getConj(ssas[invNum], ssa);

      filter (ssas[invNum], bind::IsConst (), inserter(qvars[invNum],
        qvars[invNum].begin()));

      ExprSet itersCur;
      vector<int> extMbp; // placeholder here
      for (int i = 0; i < dstVars.size(); i++)
      {
        Expr a = srcVars[i];
        Expr b = dstVars[i];
        if (!bind::isIntConst(a) /*|| !contains(postconds[invNum], a)*/) continue;

        bool implDecr = (bool)u.implies(ssas[invNum], mk<GT>(a, b));
        bool implGrow = !implDecr && (bool)u.implies(ssas[invNum], mk<LT>(a, b));
        if (implDecr || implGrow)
          createArrAcc(rel, invNum, a, implGrow, extMbp, pref,
                                            ruleManager.getPrecondition(hr));
      }
      if (!qvits[invNum].empty()) ruleManager.hasArrays[rel] = true;
    }

    void printCands()
    {
      for (auto & c : candidates)
        if (c.second.size() > 0)
        {
          outs() << "  Candidates for " << *decls[c.first] << ":\n";
          pprint(c.second, 4);
        }
    }
  };

  inline void learnInvariants3(string smt, unsigned maxAttempts, unsigned to,
       bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
       int doProp, bool dSee, bool ser, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    SMTUtils u(m_efac);

    CHCs ruleManager(m_efac, z3, debug - 2);
    auto res = ruleManager.parse(smt, doElim, doArithm);
    if (ser)
    {
      ruleManager.serialize();
      return;
    }
    if (!res) return;

    if (ruleManager.hasBV)
    {
      outs() << "Bitvectors currently not supported. Try `bnd/expl`.\n";
      return;
    }

    BndExpl bnd(ruleManager, to, debug);
    if (!ruleManager.hasCycles())
      return (void)bnd.exploreTraces(1, ruleManager.chcs.size(), true);

    RndLearnerV3 ds(m_efac, z3, ruleManager, to, freqs, aggp, mut, dat, debug);

    map<Expr, ExprSet> cands;

    for (auto& cyc : ruleManager.cycles) {
      Expr rel = cyc.first;
      for (int i = 0; i < cyc.second.size(); i++)
      {
        Expr dcl = ruleManager.chcs[cyc.second[i][0]].srcRelation;
        if (ds.initializedDecl(dcl)) continue;
        ds.initializeDecl(dcl);
        if (!dSee) continue;

        Expr pref = bnd.compactPrefix(rel, i);
        ExprSet tmp;
        getConj(pref, tmp);
        for (auto & t : tmp)
        if (hasOnlyVars(t, ruleManager.invVars[dcl]))
        cands[dcl].insert(t);

        if (mut > 0) ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
        ds.initializeAux(cands[dcl], bnd, rel, i, pref);
      }
    }
    if (dat > 0) ds.getDataCandidates(cands);

    for (auto & dcl: ruleManager.wtoDecls)
    {
      for (int i = 0; i < doProp; i++)
        for (auto & a : cands[dcl]) ds.propagate(dcl, a, true);
      ds.addCandidates(dcl, cands[dcl]);
      ds.prepareSeeds(dcl, cands[dcl]);
    }

    if (ds.bootstrap()) return;

    ds.calculateStatistics();
    ds.deferredPriorities();
    std::srand(std::time(0));
    ds.synthesize(maxAttempts);
  }
}

#endif
