#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearner.hpp"
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
    Expr range;
  };

  static bool (*weakeningPriorities[])(Expr, tribool) =
  {
    [](Expr cand, tribool val) { return bool(!val); },
    [](Expr cand, tribool val) { return indeterminate(val) && containsOp<FORALL>(cand); },
    [](Expr cand, tribool val) { return indeterminate(val); }
  };

  class RndLearnerV3 : public RndLearnerV2
  {
    private:

    ExprSet checked;
    set<HornRuleExt*> propped;
    map<int, ExprVector> candidates;
    map<int, deque<Expr>> deferredCandidates;
    map<int, ExprSet> tmpFailed;
    bool boot = true;

    // extra options for disjunctive invariants
    unsigned dCandNum = 0;
    unsigned dAttNum = 100;
    unsigned dDepNum = 3;
    bool dAllMbp;
    bool dAddProp;
    bool dAddDat;
    bool dStrenMbp;

    map<int, Expr> postconds;
    map<int, Expr> ssas;
    map<int, Expr> prefs;
    map<int, ExprSet> mbps;

    map<int, vector<ArrAccessIter* >> qvits; // per cycle
    map<int, ExprSet> qvars;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, unsigned to, bool freqs, bool aggp,
                  bool _dAllMbp, bool _dAddProp, bool _dAddDat, bool _dStrenMbp, int debug) :
      RndLearnerV2 (efac, z3, r, to, freqs, aggp, debug),
                  dAllMbp(_dAllMbp), dAddProp(_dAddProp), dAddDat(_dAddDat), dStrenMbp(_dStrenMbp) {}

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

    Expr renameCand(Expr newCand, ExprVector& varsRenameFrom, int invNum)
    {
      for (auto & v : invarVars[invNum])
        newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
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
        outs () << "  QE: " << e << "\n  vars   (((";
        for (auto & v : varsRenameFrom ) outs () << "   " << v << " ";
        outs () << ")))\n";
        outs () << "  QE res: " << eTmp << "\n";
      }
      return eTmp;
    }

    void addPropagatedArrayCands(Expr rel, int invNum, Expr candToProp)
    {
      vector<int> tmp;
      ruleManager.getCycleForRel(rel, tmp);
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

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, Expr relFrom, ExprVector& varsRenameFrom, Expr rel, bool seed, bool fwd)
    {
      if (!containsOp<FORALL>(candToProp) && !u.isSat(candToProp, constraint))
        return false; // sometimes, maybe we should return true.

      int invNum = getVarIndex(rel, decls);
      int invNumFrom = getVarIndex(relFrom, decls);

      if (containsOp<FORALL>(candToProp))
      {
        // GF: not tested for backward propagation
        if (fwd == false) return true;
        if (finalizeArrCand(candToProp, constraint, relFrom))
        {
          assert (isOpX<FORALL>(candToProp));
          Expr qvar = getQvit(invNumFrom, bind::fapp(candToProp->arg(0)))->qv; // TODO: support nested loops with several qvars

          addPropagatedArrayCands(rel, invNum, candToProp);
          Expr newCand = getForallCnj(eliminateQuantifiers(
                        mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;

          auto candsTmp = candidates;
          candidates[invNum].push_back(newCand);

          bool res = checkCand(invNum, false) &&
                     propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
          if (!candidates[invNum].empty()) return res;

          for (auto & q : qvits[invNum])
          {
            Expr newCand1 = replaceAll(newCand, qvar->last(), q->qv->last());
            newCand1 = replaceArrRangeForIndCheck(invNum, newCand1, true);
            if (newCand1 == NULL) continue;
            candidates = candsTmp;
            candidates[invNum].push_back(newCand1);
            if (checkCand(invNum, false) &&
                propagateRec(rel, conjoin(candidates[invNum], m_efac), false))
              res = true;
          }
          return res;
        }
        else
        {
          // very ugly at the moment, to be revisited
          Expr newCand = getForallCnj(eliminateQuantifiers(
                          mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;
          candidates[invNum].push_back(newCand);
          return checkCand(invNum, false) &&
               propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
        }
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
      if (printLog >= 3) outs () << "   Adding candidate [" << invNum << "]: " << cnd << "\n";
      SamplFactory& sf = sfs[invNum].back();
      Expr allLemmas = sf.getAllLemmas();
      if (containsOp<FORALL>(cnd) || containsOp<FORALL>(allLemmas))
      {
        if (containsOp<FORALL>(cnd))
          cnd = replaceArrRangeForIndCheck (invNum, cnd);
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

    bool finalizeArrCand(Expr& cand, Expr constraint, Expr relFrom)
    {
      // only forward currently
      if (!isOpX<FORALL>(cand)) return false;
      if (!containsOp<ARRAY_TY>(cand)) return false;

      // need to make sure the candidate is finalized (i.e., not a nested loop)
      int invNum = getVarIndex(relFrom, decls);
      if (u.isSat(postconds[invNum], constraint)) return false;

      ExprSet cnj;
      for (int i = 0; i < cand->arity()-1; i++)
      {
        Expr qv = bind::fapp(cand->arg(i));
        auto q = getQvit(invNum, qv);
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

    Expr replaceArrRangeForIndCheck(int invNum, Expr cand, bool fwd = false)
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
          if      (str->grows && fwd)   cnjs.insert(mk<GEQ>(qv, itRepl));
          else if (str->grows && !fwd)  cnjs.insert(mk<LT>(qv, itRepl));
          else if (!str->grows && fwd)  cnjs.insert(mk<LEQ>(qv, itRepl));
          else if (!str->grows && !fwd) cnjs.insert(mk<GT>(qv, itRepl));
        }
        else
        {
          for (auto it = cnjs.begin(); it != cnjs.end(); )
          {
            if (contains (*it, qv)) it = cnjs.erase(it);
            else ++it;
          }
        }
        cand = replaceAll(cand, cand->last()->left(), conjoin(cnjs, m_efac));
      }
      return simplifyQuants(cand);
    }

    bool propagate(int invNum, Expr cand, bool seed) { return propagate(decls[invNum], cand, seed); }

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

        Expr constraint = hr.body;

        // forward:
        if (hr.srcRelation == rel && find(propped.begin(), propped.end(), &hr) == propped.end())
        {
          if (hr.isInductive && ruleManager.hasArrays[rel]) continue;     // temporary workarond
          propped.insert(&hr);
          SamplFactory* sf1 = &sfs[getVarIndex(hr.srcRelation, decls)].back();
          Expr replCand = replaceAllRev(cand, sf1->lf.nonlinVars);
          replCand = replaceAll(replCand, ruleManager.invVars[rel], hr.srcVars);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.dstVars, hr.dstRelation, seed, true);
        }
        // backward (very similarly):
        if (hr.dstRelation == rel && find(propped.begin(), propped.end(), &hr) == propped.end())
        {
          propped.insert(&hr);
          SamplFactory* sf2 = &sfs[getVarIndex(hr.dstRelation, decls)].back();
          Expr replCand = replaceAllRev(cand, sf2->lf.nonlinVars);
          replCand = replaceAll(replCand, ruleManager.invVars[rel], hr.dstVars);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.srcVars, hr.srcRelation, seed, false);
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

    void addLemma (SamplFactory& sf, Expr l)
    {
      if (printLog) outs () << "Added lemma " << l << "\n";
      sf.learnedExprs.insert(l);
    }

    // a simple method to generate properties of a larger Array range, given already proven ranges
    void generalizeArrInvars (SamplFactory& sf)
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
              tmpVars.push_back(bind::intConst(mkTerm<string> ("_tmp_var_" + lexical_cast<string>(index), m_efac)));
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
                  addLemma(sf, newCand);
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
              addLemma(sf, b);
            else
            {
              Expr learnedCand = normalizeDisj(b, invarVarsShort[cand.first]);
              Sampl& s = sf.exprToSampl(learnedCand);
              sf.assignPrioritiesForLearned();
              if (!u.implies(sf.getAllLemmas(), learnedCand))
                addLemma(sf, learnedCand);
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
          if (containsOp<ARRAY_TY>(l) || findNonlin(l) || containsOp<BOOL_TY>(l)) continue;
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

    Expr mkImplCnd(Expr pre, Expr cand, bool out = true)
    {
      Expr im;
      if (isOpX<FORALL>(cand))
      {
        Expr tmp = cand->last()->right();
        im = replaceAll(cand, tmp, mkImplCnd(pre, tmp, false));
      }
      else im = mk<IMPL>(pre, cand);
      if (printLog >= 2 && out)
        outs () << "  - - - Implication candidate: " << im << "\n";
      return im;
    }

    bool synthesizeDisjLemmas(int invNum, int cycleNum, Expr rel,
                              Expr cnd, Expr splitter, Expr ind, unsigned depth, Expr lastModel = NULL)
    {
      if (printLog >= 2) outs () << "  Try finding splitter for " << cnd << "\n";
      if (dCandNum++ == dAttNum || depth == dDepNum) return true;
      Expr invs = conjoin(sfs[invNum].back().learnedExprs, m_efac);

      if (isOpX<FORALL>(cnd)) cnd = replaceArrRangeForIndCheck (invNum, cnd);

      vector<int>& cycle = ruleManager.cycles[cycleNum];
      ExprVector& srcVars = ruleManager.chcs[cycle[0]].srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;
      Expr cndPrime = replaceAll(cnd, srcVars, dstVars);
      Expr cndSsa = mk<AND>(cnd, ssas[invNum]);
      Expr cndSsaPr = mk<AND>(cndSsa, cndPrime);

      ExprVector cur_mbps;

      while (true)
      {
        Expr avail = mkNeg(disjoin(cur_mbps, m_efac));
        Expr fla = mk<AND>(splitter, cndSsa);     // to weaken MBP further

        if (lastModel == NULL) {
          if (isOpX<TRUE>(splitter) && u.isSat(avail, prefs[invNum], cndSsaPr)) {
            fla = mk<AND>(prefs[invNum], cndSsaPr);
          } else if (u.isSat(avail, splitter, cndSsaPr)) {
            fla = mk<AND>(splitter, cndSsaPr);
          } else if (u.isSat(avail, splitter, cndSsa)) {
            fla = mk<AND>(splitter, cndSsa);
          } else break;

          lastModel = u.getModel();
        }

        if (lastModel == NULL) break;
        Expr mbp = getMbp(invNum, lastModel);
        if (isOpX<FALSE>(mbp)) break;
        mbp = ufo::eliminateQuantifiers(mbp, dstVars); // for the case of arrays
        mbp = weakenForVars(mbp, dstVars);
        mbp = u.getImplDecomp(mbp, invs);
        mbp = u.getWeakerMBP(mbp, fla, srcVars);
        if (printLog >= 2) outs() << "    Found MBP: " << mbp << "\n";

        bool toadd = true;
        for (int j = 0; j < cur_mbps.size(); j++)
          if (u.isSat(cur_mbps[j], mbp))
          {
            cur_mbps[j] = mk<OR>(cur_mbps[j], mbp);
            toadd = false;
            break;
          }
        if (toadd) cur_mbps.push_back(mbp);
        if (isOpX<FORALL>(cnd)) break;    // temporary workaround for arrays (z3 might fail in giving models)
        if (dAllMbp)
          lastModel = NULL;
        else
          break;
      }

      for (auto mbp : cur_mbps)
      {
        if (!u.isSat(invs, mbp, splitter)) return true;

        if (dStrenMbp)
        {
          ExprSet tmp, tmp2;
          getConj(mbp, tmp);

          if (u.implies (prefs[invNum], cnd)) mutateHeuristic(prefs[invNum], tmp2);
          tmp2.insert(sfs[invNum].back().learnedExprs.begin(), sfs[invNum].back().learnedExprs.end());

          for (auto m : tmp)
          {
            if (!isOp<ComparissonOp>(m)) continue;
            for (auto t : tmp2)
            {
              if (!isOp<ComparissonOp>(t)) continue;
              Expr t1 = mergeIneqs(t, m);
              if (t1 == NULL) continue;
              t1 = simplifyArithm(t1);
              if (u.implies(mk<AND>(t1, ssas[invNum]), replaceAll(t1, srcVars, dstVars))) // && u.isSat(ind, t1))
                ind = mk<AND>(ind, t1);
            }
          }
        }

        if (u.isEquiv(mbp, splitter)) {
          candidates[invNum].push_back(mkImplCnd(mk<AND>(mbp, ind), cnd));
          candidates[invNum].push_back(mkImplCnd(mbp, cnd));
          return true;
        }

        Expr candImpl;
        if (isOpX<FORALL>(cnd))
        {
          Expr splitterArr = mk<AND>(splitter, mbp);
          for (auto & q : qvits[invNum])
            splitterArr = replaceAll(splitterArr, q->iter, q->qv);
          candImpl = mkImplCnd(splitterArr, cnd);
        }
        else
        {
          candImpl = mkImplCnd(mk<AND>(splitter, mbp), cnd); //mkImplCnd(mk<AND>(mk<AND>(splitter, ind), mbp), cnd);
          candidates[invNum].push_back(mkImplCnd(mk<AND>(splitter, ind), cnd)); // heuristic to add a candidate with weaker precond
          candidates[invNum].push_back(mkImplCnd(mk<AND>(mk<AND>(splitter, ind), mbp), cnd));
        }

        if (find(candidates[invNum].begin(), candidates[invNum].end(), candImpl) != candidates[invNum].end())
          return true;
        candidates[invNum].push_back(candImpl);

        // use multiHoudini here to give more chances to array candidates
        auto candidatesTmp = candidates;
        if (multiHoudini(ruleManager.wtoCHCs)) assignPrioritiesForLearned();
        else candidates = candidatesTmp;

        map<Expr, ExprSet> cands;

        if (dAddProp)
        {
          ExprSet s = {mbp, splitter, ind, ssas[invNum],
                       mkNeg(replaceAll(mk<AND>(mk<AND>(splitter, ind), mbp), srcVars, dstVars))};
          ExprVector vars = dstVars;
          if (isOpX<FORALL>(cnd))
          {
            s.insert(cnd->last());
            for (int i = 0; i < cnd->arity()-1; i++)
              vars.push_back(bind::fapp(cnd->arg(i)));
          }
          else
            s.insert(cnd);
          Expr newCand = keepQuantifiers (conjoin(s, m_efac), vars);
          newCand = u.removeITE(replaceAll(newCand, dstVars, srcVars));
          if (isOpX<FORALL>(cnd))
            cands[rel].insert(replaceAll(cnd, cnd->last(), newCand));
          else
            getConj(newCand, cands[rel]);
        }

        Expr nextModel;
        ExprSet qfInvs, candsToDat; //, se;
        if (dAddDat)
        {
//          getArrInds(ssas[invNum], se);
          if (isOpX<FORALL>(cnd))
            qfInvs.insert(cnd->right()->right());              // only the actual inv without the splitter/mbp
          else
            candsToDat.insert(candImpl);
          for (auto & inv : sfs[invNum].back().learnedExprs)   // basically, invs
            if (isOpX<FORALL>(inv))
              qfInvs.insert(inv->right()->right());
            else
              candsToDat.insert(inv);
//          for (auto & s : se)
          {
            Expr candToDat = conjoin(qfInvs, m_efac);
            for (auto & q : qvits[invNum])
              candToDat = replaceAll(candToDat, q->qv, q->iter); // s);
            ExprVector vars2keep;
            for (int i = 0; i < srcVars.size(); i++)
              if (containsOp<ARRAY_TY>(srcVars[i]))
                candToDat = replaceAll(candToDat, srcVars[i], dstVars[i]);
            candsToDat.insert(candToDat);
          }
          nextModel = getDataCandidates(cands, rel, mkNeg(mbp), conjoin(candsToDat, m_efac));
        }

        // postprocess behavioral arrCands
        if (ruleManager.hasArrays[rel])
        {
          for (auto &a : arrCands[invNum])
          {
            Expr arrCand = a;
            for (auto &q : qvits[invNum])
              arrCand = replaceAll(arrCand, q->iter, q->qv);
            cands[rel].insert(sfs[invNum].back().af.getSimplCand(arrCand));
          }
          arrCands[invNum].clear();
        }

        for (auto & c : cands[rel])
        {
          if (isOpX<FORALL>(cnd) && !isOpX<FORALL>(c)) continue;
          synthesizeDisjLemmas(invNum, cycleNum, rel, c, mk<AND>(splitter, mkNeg(mbp)), ind, depth + 1, nextModel);
        }
      }
      return true;
    }

    bool synthesize(unsigned maxAttempts, bool doDisj)
    {
      if (printLog >= 3)
        for (auto & a : deferredCandidates)
          for (auto & b : a.second)
            outs () << "  Deferred cand for " << a.first << ": " << b << "\n";
      if (printLog) outs () << "\nSAMPLINGV3\n========\n";

      ExprSet cands;
      for (int i = 0; i < maxAttempts; i++)
      {
        // next cand (to be sampled)
        // TODO: find a smarter way to calculate; make parametrizable
        int cycleNum = i % ruleManager.cycles.size();
        int tmp = ruleManager.cycles[cycleNum][0];
        Expr rel = ruleManager.chcs[tmp].srcRelation;
        int invNum = getVarIndex(rel, decls);
        candidates.clear();
        SamplFactory& sf = sfs[invNum].back();
        Expr cand;
        if (deferredCandidates[invNum].empty()) {
          cand = sf.getFreshCandidate(i < 25);  // try simple array candidates first
          //outs() << "CAND>" << cand << "\n";
        }
        else {
          cand = deferredCandidates[invNum].back();
          deferredCandidates[invNum].pop_back();
        }
        if (cand != NULL && isOpX<FORALL>(cand) && isOpX<IMPL>(cand->last()))
        {
          if (!u.isSat(cand->last()->left())) cand = NULL;
        }
        if (cand == NULL) continue;
        if (printLog) outs () << " - - - Sampled cand (#" << i << ") for " << decls[invNum] << ": " << cand << "\n";
        if (!addCandidate(invNum, cand)) continue;

        bool lemma_found = checkCand(invNum);
        if (doDisj && (isOp<ComparissonOp>(cand) || isOpX<FORALL>(cand)))
        {
          dCandNum = 0;
          lemma_found = true;
          synthesizeDisjLemmas(invNum, cycleNum, rel, cand, mk<TRUE>(m_efac), mk<TRUE>(m_efac), 0);
          multiHoudini(ruleManager.wtoCHCs);
          if (printLog) outs () << "\n";
        }
        if (lemma_found)
        {
          assignPrioritiesForLearned();
          generalizeArrInvars(sf);
          if (checkAllLemmas())
          {
            outs () << "Success after " << (i+1) << " iterations "
                    << (deferredCandidates[invNum].empty() ? "(+ rnd)" : "") << "\n";
            printSolution();
            return true;
          }
        }
      }
      outs() << "unknown\n";
      return false;
    }

    bool filterUnsat()
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
          deferredCandidates[i] = def;
          candidates[i] = cur;
        }
      }

      return true;
    }

    bool weaken (int invNum, ExprVector& ev,
                 map<Expr, tribool>& vals, HornRuleExt* hr, SamplFactory& sf,
                 function<bool(Expr, tribool)> cond, bool singleCand)
    {
      bool weakened = false;
      for (auto it = ev.begin(); it != ev.end(); )
      {
        if (cond(*it, vals[*it]))
        {
          weakened = true;
          if (printLog >= 3) outs () << "    Failed cand for " << hr->dstRelation << ": " << *it << "\n";
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
          if (boot)
          {
            if (isOpX<EQ>(*it)) deferredCandidates[invNum].push_back(*it);  //  prioritize equalities
            else deferredCandidates[invNum].push_front(*it);
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

      if (!anyProgress(worklist)) {
        if (printLog >= 4) outs() << "    No progress\n";
        return false;
      }
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
            for (auto & v : invarVars[invNum])
              repl = replaceAll(repl, v.second, hr->dstVars[v.first]);
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

    void generateMbps(int invNum, Expr ssa, ExprVector& srcVars, ExprVector& dstVars)
    {
      ExprVector vars2keep;
      for (int i = 0; i < srcVars.size(); i++)
        if (containsOp<ARRAY_TY>(srcVars[i]))
          vars2keep.push_back(dstVars[i]);
        else
          vars2keep.push_back(srcVars[i]);

      ExprSet tmp = {ssa};
      while (true)
      {
        if (!u.isSat(tmp)) break;
        Expr mbp = keepQuantifiersRepl (u.getTrueLiterals(ssa), vars2keep);
        mbps[invNum].insert(mbp);
        tmp.insert(mk<NEG>(mbp));
      }
      if (printLog >= 2 && !mbps[invNum].empty())
      {
        outs() << "Generated MBPs:\n";
        for (auto & mbp : mbps[invNum]) outs() << "  " << mbp << "\n";
      }
    }

    Expr getMbp(int invNum, Expr lastModel)
    {
      ExprSet cur_mbps;
      for (auto & m : mbps[invNum])
        if (u.isSat(m, lastModel)) cur_mbps.insert(m);
      return disjoin(cur_mbps, m_efac);
    }

    // overloaded, called from `prepareSeeds`
    void doSeedMining(Expr invRel, ExprSet& cands, set<cpp_int>& progConsts, set<cpp_int>& intCoefs)
    {
      int invNum = getVarIndex(invRel, decls);

      Expr ssa = rewriteSelectStore(ssas[invNum]);
      ExprVector& srcVars = ruleManager.invVars[invRel];
      ExprVector& dstVars = ruleManager.invVarsPrime[invRel];
      retrieveDeltas(ssa, srcVars, dstVars, cands);
      generateMbps(invNum, ssa, srcVars, dstVars);     // add mbps as candidates:
      for (auto & mbp : mbps[invNum]) getConj(replaceAll(mbp, dstVars, srcVars), cands);
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

        // limit only to queries:
        if (hr.isQuery) sm.analyzeCode();
        if (!analyzedExtras && hr.srcRelation == invRel)
        {
          sm.analyzeExtras (cands);
          analyzedExtras = true;
        }
        for (auto &cand : sm.candidates) candsFromCode.insert(cand);
        for (auto &a : sm.intConsts) progConsts.insert(a);
        for (auto &a : sm.intCoefs) intCoefs.insert(a);

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
          Expr pre = q->precond;
          Expr qVar = bind::intConst(mkTerm<string>("_FH_arr_it_" + lexical_cast<string>(qNum), m_efac));
          q->qv = qVar;
          arrAccessVars[invNum].push_back(qVar);

          assert (isOpX<EQ>(pre)); // TODO: support more

          ExprVector invAndIterVarsAll = invarVarsShort[invNum];
          invAndIterVarsAll.push_back(qVar);

          Expr fla = (q->grows) ? mk<GEQ>(qVar, pre->right()) :
                                  mk<LEQ>(qVar, pre->right());

          ExprSet tmp;
          getConj(postconds[invNum], tmp);
          for (auto it = tmp.begin(); it != tmp.end(); )
            if (contains(*it, q->iter)) ++it; else it = tmp.erase(it);

          q->range = normalizeDisj(mk<AND>(fla,
                     replaceAll(conjoin(tmp, m_efac), q->iter, qVar)), invAndIterVarsAll);
          arrIterRanges[invNum].insert(q->range);

          // repair behavioral arrCands
          if (!arrCands[invNum].empty())
          {
            ExprSet repCands;
            for (auto & a : arrCands[invNum])
              repCands.insert(replaceAll(a, q->iter, qVar));
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
          getExtraVars(replCand, srcVars, allVars);
          if (allVars.size() < 2 &&
              !u.isTrue(replCand) && !u.isFalse(replCand))
          {
            if (allVars.size() == 0)
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

        // trick for tiling benchs
        ExprSet afs;
        for (auto & a : tmpArrFuns)
        {
          ExprVector vars;
          filter (a, bind::IsConst(), std::inserter (vars, vars.begin ()));
          if (vars.size() != 1 || *vars.begin() == a) continue;
          afs.insert(replaceAll(a, *vars.begin(), arrAccessVars[invNum][0]));
        }

//        for (auto & s : afs)
//        {
//          for (auto & qcand : arrCands[invNum])
//          {
//            outs () << "  qcand: " << *qcand << "\n";
//            ExprSet se;
//            filter (qcand, bind::IsSelect (), inserter(se, se.begin()));
//            for (auto & arrsel : se)
//            {
//              Expr qcandTmp = replaceAll(qcand, arrsel->right(), s);
//              arrCands[invNum].insert(qcandTmp);
//              outs () << "   prepro: " << *qcandTmp << "\n";
//            }
//          }
//        }
      }
      // process all quantifier-free seeds

      cands = candsFromCode;

      for (auto & cand : candsFromCode)
      {
        Expr replCand = replaceAllRev(cand, sf.lf.nonlinVars);
        addCandidate(invNum, replCand);
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

    Expr getDataCandidates(map<Expr, ExprSet>& cands, Expr srcRel = NULL,
                           Expr splitter = NULL, Expr invs = NULL){
      Expr model;     // for splitters
#ifdef HAVE_ARMADILLO
      if (printLog && splitter == NULL) outs () << "\nDATA LEARNING\n=============\n";
      if (splitter == NULL) assert(invs == NULL && srcRel == NULL);
      map<Expr, ExprSet> poly;
      DataLearner dl(ruleManager, m_z3, printLog);
      if (splitter == NULL)
      {
        // run at the beginning, compute data once
        dl.computeData();
        for (auto & dcl : decls)
        {
          int invNum = getVarIndex(dcl, decls);
          dl.computePolynomials(dcl, poly[dcl]);
        }
      }
      else
      {
        // run at `synthesizeDisjLemmas`
        for (auto & dcl : decls) {
          int invNum = getVarIndex(dcl, decls);
          if (srcRel == dcl)
          {
            dl.computeData(srcRel, splitter, invs);
            dl.computePolynomials(dcl, poly[dcl]);
            for (auto & a : dl.getConcrInvs(dcl)) cands[dcl].insert(a);
            model = conjoin(dl.getConcrInvs(srcRel), m_efac);
            break;
          }
        }
      }

      // mutations after all
      for (auto & p : poly)
      {
        if (ruleManager.hasArrays[p.first])   // heuristic to remove cands irrelevant to counters and arrays
        {
          ExprSet its;
          int invNum = getVarIndex(p.first, decls);
          for (auto q : qvits[invNum]) its.insert(q->iter);
          for (auto it = p.second.begin(); it != p.second.end();)
            if (emptyIntersect(simplifyArithm(*it), its))
              it = p.second.erase(it);
            else
              ++it;
        }
        mutateHeuristicEq(p.second, cands[p.first], p.first, (splitter == NULL));
      }
#else
      if (printLog) outs() << "Skipping learning from data as required library (armadillo) not found\n";
#endif
      return model;
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

    bool bootstrap(bool doDisj)
    {
      if (printLog) outs () << "\nBOOTSTRAPPING\n===============\n";
      filterUnsat();

      if (multiHoudini(ruleManager.wtoCHCs))
      {
        assignPrioritiesForLearned();
        if (checkAllLemmas())
        {
          outs () << "Success after bootstrapping\n";
          printSolution();
          return true;
        }
      }

      if (!doDisj) simplifyLemmas();
      boot = false;

      // try array candidates one-by-one (adapted from `synthesize`)
      // TODO: batching
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

            Expr cand = sf.af.getSimplCand(c);
            if (printLog) outs () << "- - - Bootstrapped cand for " << dcl << ": " << cand << "\n";

            auto candidatesTmp = candidates[invNum]; // save for later
            if (!addCandidate(invNum, cand)) continue;
            if (checkCand(invNum))
            {
              assignPrioritiesForLearned();
              generalizeArrInvars(sf);
              if (checkAllLemmas())
              {
                outs () << "Success after bootstrapping\n";
                printSolution();
                return true;
              }
            }
            else
            {
              if (isOpX<EQ>(c))         // prioritize equality cands
                deferredCandidates[invNum].push_back(cand);
              else
                deferredCandidates[invNum].push_front(cand);
              if (candidates[invNum].empty()) candidates[invNum] = candidatesTmp;
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
        if (multiHoudini(ruleManager.wtoCHCs))
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
      if(printLog >= 4) outs() << "    leaving bootstrapping\n";
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

    tribool checkCHC (HornRuleExt& hr, map<int, ExprVector>& annotations, bool checkAll = false)
    {
      if (checkAll && !hr.isQuery && annotations[getVarIndex(hr.dstRelation, decls)].empty())
        return false;     // shortcut

      ExprSet exprs = {hr.body};

      if (!hr.isFact)
      {
        int invNum = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[invNum].back();
        ExprSet lms = sf.learnedExprs;
        for (auto & a : annotations[invNum]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[invNum]) a = replaceAll(a, v.second, hr.srcVars[v.first]);
          exprs.insert(a);
        }
      }

      if (!hr.isQuery)
      {
        int invNum = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[invNum].back();
        ExprSet lms = sf.learnedExprs;
        ExprSet negged;
        for (auto & a : annotations[invNum]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[invNum]) a = replaceAll(a, v.second, hr.dstVars[v.first]);
          negged.insert(mkNeg(a));
        }
        exprs.insert(disjoin(negged, m_efac));
      }
      return u.isSat(exprs);
    }

    // it used to be called initArrayStuff, but now it does more stuff than just for arrays
    void initializeAux(BndExpl& bnd, int cycleNum, Expr pref)
    {
      vector<int>& cycle = ruleManager.cycles[cycleNum];
      HornRuleExt* hr = &ruleManager.chcs[cycle[0]];
      Expr rel = hr->srcRelation;
      ExprVector& srcVars = hr->srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;
      assert(srcVars.size() == dstVars.size());

      int invNum = getVarIndex(rel, decls);

      prefs[invNum] = pref;
      Expr e = bnd.toExpr(cycle);
      ssas[invNum] = replaceAll(e, bnd.bindVars.back(), dstVars);

      if (qvits[invNum].size() > 0) return;

      ExprSet ssa;
      if (!containsOp<ARRAY_TY>(ssas[invNum])) return; // todo: support

      getConj(ssas[invNum], ssa);

      filter (ssas[invNum], bind::IsConst (), inserter(qvars[invNum], qvars[invNum].begin()));
      postconds[invNum] = ruleManager.getPrecondition(hr);

      ExprSet itersCur;
      for (int i = 0; i < dstVars.size(); i++)
      {
        Expr a = srcVars[i];
        Expr b = dstVars[i];
        if (!bind::isIntConst(a) /*|| !contains(postconds[invNum], a)*/) continue;

        bool implDecr = (bool)u.implies(ssas[invNum], mk<GT>(a, b));
        bool implGrow = !implDecr && (bool)u.implies(ssas[invNum], mk<LT>(a, b));
        if (implDecr || implGrow)
        {
          ArrAccessIter* ar = new ArrAccessIter();
          ar->iter = a;
          ar->grows = implGrow;
          qvits[invNum].push_back(ar);
          ruleManager.iterators[rel].push_back(i);
          itersCur.insert(a);
        }
      }

      ssa.clear();
      getConj(pref, ssa);
      AeValSolver ae(mk<TRUE>(m_efac), pref, itersCur);
      ae.solve();
      Expr skol = u.simplifyITE(ae.getSimpleSkolemFunction(), ae.getValidSubset());
      if (!isOpX<TRUE>(skol))
        for (auto & q : qvits[invNum])
          q->precond = mk<EQ>(q->iter, projectITE (skol, q->iter));
      if (!qvits[invNum].empty()) ruleManager.hasArrays[rel] = true;

      if (printLog >= 2)
      {
        outs ()   << "In total, found " << qvits[invNum].size() << " iterator"
                  << (qvits[invNum].size() == 1 ? "" : "s")
                  << " for " << *rel << ":\n";
        for (auto & q : qvits[invNum])
          outs () << "      " << *q->iter
                  << "      " << (q->grows ? "increases" : "decreases")
                  << "      init value: " << *q->precond << "\n";
      }
    }

    void printCands()
    {
      for (auto & c : candidates)
        if (c.second.size() > 0)
        {
          outs() << "  Candidates for " << *decls[c.first] << ":\n";
          for (auto & a : c.second)
            outs () << "    "  << *a << "\n";
        }
    }
  };

  inline void learnInvariants3(string smt, unsigned maxAttempts, unsigned to, bool freqs, bool aggp,
                               bool enableDataLearning, bool doElim, bool doArithm, bool doDisj, int doProp,
                               bool dAllMbp, bool dAddProp, bool dAddDat, bool dStrenMbp, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3, (debug >= 2));
    ruleManager.parse(smt, doElim, doArithm);
    BndExpl bnd(ruleManager, debug);
    if (!ruleManager.hasCycles())
    {
      bnd.exploreTraces(1, ruleManager.chcs.size(), true);
      return;
    }

    RndLearnerV3 ds(m_efac, z3, ruleManager, to, freqs, aggp, dAllMbp, dAddProp, dAddDat, dStrenMbp, debug);

    map<Expr, ExprSet> cands;
    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr dcl = ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation;
      if (ds.initializedDecl(dcl)) continue;
      ds.initializeDecl(dcl);
      Expr pref = bnd.compactPrefix(i);
      ExprSet tmp;
      getConj(pref, tmp);
      for (auto & t : tmp)
        if (hasOnlyVars(t, ruleManager.invVars[dcl]))
          cands[dcl].insert(t);

      ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
      ds.initializeAux(bnd, i, pref);
    }

    if (enableDataLearning) ds.getDataCandidates(cands);

    for (auto & dcl: ruleManager.wtoDecls)
    {
      for (int i = 0; i < doProp; i++)
        for (auto & a : cands[dcl]) ds.propagate(dcl, a, true);
      ds.addCandidates(dcl, cands[dcl]);
      ds.prepareSeeds(dcl, cands[dcl]);
    }

    if (ds.bootstrap(doDisj)) return;

    ds.calculateStatistics();
    ds.deferredPriorities();
    std::srand(std::time(0));
    ds.synthesize(maxAttempts, doDisj);
  }
}

#endif
