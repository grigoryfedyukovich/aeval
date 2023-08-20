#ifndef RNDLEARNERV4__HPP__
#define RNDLEARNERV4__HPP__

#include "RndLearnerV3.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearnerV4 : public RndLearnerV3
  {
    private:

    bool dDisj;
    bool dAllMbp;
    bool dAddProp;
    bool dAddDat;
    bool dStrenMbp;
    bool dRecycleCands;
    bool dGenerous;
    int dFwd;
    int mbpEqs;

    map<int, ExprSet> mbps;
    map<int, ExprTree> mbpDt, strenDt;

    map<int, ExprSet> allDataCands;
    map<int, deque<Expr>> deferredCandidates;

    public:

    RndLearnerV4 (ExprFactory &_e, EZ3 &_z3, CHCs& _r, unsigned _to, bool _freqs,
                  bool _aggp, int _mu, int _da, bool _d, int _m, bool _dAllMbp,
                  bool _dAddProp, bool _dAddDat, bool _dStrenMbp, int _dFwd,
                  bool _dR, bool _dG, int _debug) :
      RndLearnerV3 (_e, _z3, _r, _to, _freqs, _aggp, _mu, _da, _debug),
                  dDisj(_d), mbpEqs(_m), dAllMbp(_dAllMbp),
                  dAddProp(_dAddProp), dAddDat(_dAddDat), dStrenMbp(_dStrenMbp),
                  dFwd(_dFwd), dRecycleCands(_dR), dGenerous(_dG) {}

    bool simplLemmas() { return !dDisj; }

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
          if (printLog >= 3)
            outs () << "    Failed cand for " << hr->dstRelation
                    << ": " << *it << " 🔥\n";
          if (hr->isFact && !containsOp<ARRAY_TY>(*it) &&
              !containsOp<BOOL_TY>(*it) && !findNonlin(*it))
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
            if (isOpX<EQ>(*it))
              deferredCandidates[invNum].push_back(*it);  //  prioritize equalities
            else
            {
              ExprSet disjs;
              getDisj(*it, disjs);
              for (auto & a : disjs)  // to try in the `--disj` mode
              {
                deferredCandidates[invNum].push_front(a);
                deferredCandidates[invNum].push_front(mkNeg(a));
              }
            }
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

    void postBootCands(int invNum, Expr c, Expr cand)
    {
      if (dAddProp)   // for QE-based propagation, the heuristic is disabled
        deferredCandidates[invNum].push_back(cand);
                      // otherwise, prioritize equality cands with closed ranges
      else if (isOpX<EQ>(c) && getQvit(invNum, bind::fapp(cand->arg(0)))->closed)
        deferredCandidates[invNum].push_back(cand);
      else
        deferredCandidates[invNum].push_front(cand);
    }

    virtual void addDataCand(int invNum, Expr cand, ExprSet& cands)
    {
      Expr (*ops[])(Expr, Expr) = {mk<GEQ>, mk<LEQ>};
      int sz = allDataCands[invNum].size();
      allDataCands[invNum].insert(cand);
      bool isNew = allDataCands[invNum].size() > sz;
      if (isNew || dGenerous)
      {
        cands.insert(cand);                               // actually, add it
        // also, add weaker versions of cand to deferred set
        if (dRecycleCands && !boot && isOpX<EQ>(cand))
          for (Expr (*op) (Expr, Expr) : ops)
            deferredCandidates[invNum].push_front(
                          (*op)(cand->left(), cand->right()));
      }
      else if (printLog >= 3 && !boot)
        outs () << "    Data candidate " << cand
                << " has already appeared before\n";
    }

    Expr mkImplCnd(Expr pre, Expr cand, bool out = true)
    {
      Expr im;
      if (isOpX<FORALL>(cand))
      {
        Expr tmp = cand->last()->right();
        im = replaceAll(cand, tmp, mkImplCnd(pre, tmp, false));
      }
      else im = simplifyBool(mk<IMPL>(pre, cand));
      if (printLog >= 2 && out)
        outs () << "  - - - Implication candidate: " << im
                << (printLog >= 3 ? " 😎\n" : "\n");
      return im;
    }

    Expr mkImplCndArr(int invNum, Expr mbp, Expr cnd)
    {
      Expr phaseGuardArr = mbp;
      for (auto & q : qvits[invNum])
        if (contains(cnd, q->qv))
          phaseGuardArr = replaceAll(phaseGuardArr, q->iter, q->qv);
      return mkImplCnd(phaseGuardArr, cnd);
    }

    void internalArrProp(int invNum, Expr ind, Expr mbp, Expr cnd,
          ExprSet& s, ExprVector& srcVars, ExprVector& dstVars, ExprSet& cands)
    {
      // mainly, one strategy for `--phase-prop`:
      //   * finalizing a candidate for the next phase,
      //   * reusing the regressing one at the next-next phase
      // TODO: support the reasoning for `--phase-data`
      Expr nextMbp = getMbpPost(invNum, conjoin(s, m_efac), srcVars, dstVars);
      Expr newCand = cnd;
      if (!finalizeArrCand(newCand, nextMbp, invNum)) return;
      newCand = getForallCnj(eliminateQuantifiers(
            mk<AND>(newCand, u.simplifiedAnd(ssas[invNum], nextMbp)),
            dstVars, invNum, false));
      if (newCand == NULL) return;
      getConj(newCand, cands);
      ExprVector newCands;
      replaceArrRangeForIndCheck(invNum, newCand, newCands, /* regress == */ true);
      for (auto & newCand : newCands)
      {
        s = {ind, u.simplifiedAnd(ssas[invNum], nextMbp),
            mkNeg(replaceAll(mk<AND>(ind, mbp), srcVars, dstVars))};
        nextMbp = getMbpPost(invNum, conjoin(s, m_efac), srcVars, dstVars);
        Expr candImplReg = mkImplCndArr(invNum, nextMbp, newCand);
        candidates[invNum].push_back(candImplReg);
      }
    }

    void generatePhaseLemmas(int invNum, int cycleNum, Expr rel, Expr cnd)
    {
      if (printLog >= 2)
        outs () << "  Try finding phase guard for " << cnd << "\n";
      if (isOpX<FORALL>(cnd))
      {
        ExprVector cnds;
        replaceArrRangeForIndCheck (invNum, cnd, cnds);
        if (cnds.empty()) return;
        cnd = cnds[0];              // TODO: extend
      }

      vector<int>& cycle = ruleManager.cycles[rel][cycleNum];
      ExprVector& srcVars = ruleManager.chcs[cycle[0]].srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;

      vector<pair<int, int>> cur_mbps;
      int curDepth = dFwd ? INT_MAX : 0;
      int curPath = -1;
      int curLen = INT_MAX;

      for (int p = 0; p < mbpDt[invNum].paths.size(); p++)
      {
        auto &path = mbpDt[invNum].paths[p];
        for (int m = 0; m < path.size(); m++)
        {
          Expr fla = mk<AND>(mbpDt[invNum].getExpr(p,m),
                             strenDt[invNum].getExpr(p,m));
          if (m == 0)
            if (!u.implies(mk<AND>(prefs[invNum], fla), cnd))
              continue;                            // initialization filtering
          ExprVector filt = {mbpDt[invNum].getExpr(p, m),
                            strenDt[invNum].getExpr(p ,m), ssas[invNum], cnd};
          if (!u.isSat(filt))                      // consecution filtering
            continue;
          if (m + 1 < path.size())                 // lookahead-based filtering
          {
            filt.push_back(replaceAll(mk<AND>(mbpDt[invNum].getExpr(p, m + 1),
                        strenDt[invNum].getExpr(p, m + 1)), srcVars, dstVars));
            if (!u.isSat(filt))
              continue;
          }

          if (dAllMbp) cur_mbps.push_back({p, m});    // TODO: try other heuristics
          else if (((dFwd && m <= curDepth) || (!dFwd && m >= curDepth)) &&
                    curLen > path.size())
          {
            curPath = p;
            curDepth = m;
            curLen = path.size();
            if (printLog >= 3)
              outs () << "      updating MBP path/depth since its has "
                      << "an earlier occurrence: ["
                      << curPath << ", " << curDepth << "] and shorter path\n";
          }
        }
      }

      if (!dAllMbp && curPath >= 0) cur_mbps.push_back({curPath, curDepth});

      if (printLog >= 2)
      {
        outs () << "  Total " << cur_mbps.size() << " MBP paths to try: ";
        for (auto & c : cur_mbps)
          outs () << "[ " << c.first << ", " << c.second  << " ], ";
        outs () << "\n";
      }
      for (auto & c : cur_mbps)
        for (bool dir : {true, false})
          if (dFwd == dir || dFwd == 2)
            annotateDT(invNum, rel, cnd, c.first, c.second, srcVars, dstVars, dir);
    }

    void annotateDT(int invNum, Expr rel, Expr cnd, int path, int depth,
                        ExprVector& srcVars, ExprVector& dstVars, bool fwd)
    {
      if (!mbpDt[invNum].isValid(path, depth))
      {
        if (dRecycleCands)
          deferredCandidates[invNum].push_back(cnd);
        return;
      }
      Expr mbp = mbpDt[invNum].getExpr(path, depth);
      if (mbp == NULL) return;

      if (printLog >= 2)
        outs () << "    Next ordered MBP: " << mbp << " [ "
                << path << ", " << depth << " ] in "
                << (fwd ? "forward" : "backward") << " direction\n";

      Expr ind = strenDt[invNum].getExpr(path, depth);
      if (printLog >= 2)
        outs () << "    Strengthening the guard [ " << path << ", "
                << depth << " ] with " << ind << "\n";

      Expr candImpl;
      if (isOpX<FORALL>(cnd)) candImpl = mkImplCndArr(invNum, mbp, cnd);
      else candImpl = mkImplCnd(mk<AND>(ind, mbp), cnd);

      if (find(candidates[invNum].begin(), candidates[invNum].end(), candImpl)
           != candidates[invNum].end())
             return;
      candidates[invNum].push_back(candImpl);

      // use multiHoudini here to give more chances to array candidates
      auto candidatesTmp = candidates;
      if (multiHoudini(ruleManager.dwtoCHCs)) assignPrioritiesForLearned();
      else if (dAllMbp) candidates = candidatesTmp;
      else return;

      Expr nextMbp;
      if (fwd)
      {
        if (mbpDt[invNum].isLast(path, depth))
        {
          ExprSet tmp;
          mbpDt[invNum].getBackExprs(path, depth, tmp);
          if (tmp.empty())  return;
          nextMbp = disjoin(tmp, m_efac);
        }
        else nextMbp = mbpDt[invNum].getExpr(path, depth + 1);
      }
      else
      {
        if (depth == 0) return;
        nextMbp = mbpDt[invNum].getExpr(path, depth - 1);
      }

      // GF: if `dFwd == 2` then there is a lot of redundancy
      //     since all the code above this point runs twice
      //     TODO: refactor

      map<Expr, ExprSet> cands;
      if (dAddProp)
      {
        ExprSet s;
        if (fwd)
          s = { ind, u.simplifiedAnd(ssas[invNum], mbp),
                       replaceAll(nextMbp, srcVars, dstVars) };
        else
          s = { u.simplifiedAnd(ssas[invNum], nextMbp),
                       replaceAll(mbp, srcVars, dstVars) , ind };

        Expr newCand;

        if (isOpX<FORALL>(cnd))      // Arrays are supported only if `fwd == 1`;
          internalArrProp(invNum, ind, mbp, cnd, s, srcVars, dstVars, cands[rel]);
        else
        {
          if (fwd)
          {
            s.insert(cnd);        // the cand to propagate (using standard QE)
            newCand = keepQuantifiers (conjoin(s, m_efac), dstVars);
            newCand = weakenForHardVars(newCand, dstVars);
            newCand = replaceAll(newCand, dstVars, srcVars);
          }
          else
          {
            s.insert(mkNeg(replaceAll(cnd, srcVars, dstVars)));  // (abduction)
            newCand = keepQuantifiers (conjoin(s, m_efac), srcVars);
            newCand = weakenForHardVars(newCand, srcVars);
            newCand = mkNeg(newCand);
          }

          newCand = u.removeITE(newCand);
          if (isOpX<FALSE>(newCand)) return;
          getConj(newCand, cands[rel]);
          if (printLog >= 3)
            outs () << "  Phase propagation gave "
                    << cands[rel].size() << " candidates to try\n";
        }
      }

      ExprSet qfInvs, candsToDat;
      if (dAddDat)
      {
        candsToDat = { mbp, ind };
        int sz = cands[rel].size();
        if (isOpX<FORALL>(cnd))                   // only the actual inv
          qfInvs.insert(cnd->last()->right());    // without the phaseGuard/mbp
        else
          candsToDat.insert(candImpl);
        for (auto & inv : sfs[invNum].back().learnedExprs)   // basically, invs
          if (isOpX<FORALL>(inv))
            qfInvs.insert(inv->last()->right());
          else
            candsToDat.insert(inv);
        Expr candToDat = conjoin(qfInvs, m_efac);
        for (auto & q : qvits[invNum])
          candToDat = replaceAll(candToDat, q->qv, q->iter); // s);
        ExprVector vars2keep;
        for (int i = 0; i < srcVars.size(); i++)
          if (containsOp<ARRAY_TY>(srcVars[i]))
            candToDat = replaceAll(candToDat, srcVars[i], dstVars[i]);
        candsToDat.insert(candToDat);
        getDataCandidates(cands, rel, nextMbp, conjoin(candsToDat, m_efac), fwd);
        if (printLog >= 3)
          outs () << "  Data Learning gave " << (cands[rel].size() - sz)
                  << (dAddProp? "additional " : "") << " candidates to try\n";
      }

      // postprocess behavioral arrCands
      if (ruleManager.hasArrays[rel])
      {
        for (auto &a : arrCands[invNum])
        {
          ExprSet tmpCands;
          getQVcands(invNum, a, tmpCands);
          for (Expr arrCand : tmpCands)
            cands[rel].insert(sfs[invNum].back().af.getQCand(arrCand));
        }
        arrCands[invNum].clear();
      }

      for (auto c : cands[rel])
      {
        if (isOpX<FORALL>(cnd) && !isOpX<FORALL>(c)) continue;
        if (isOpX<FORALL>(c))
        {
          ExprVector cnds;
          replaceArrRangeForIndCheck (invNum, c, cnds);
          if (cnds.empty()) continue;
          c = cnds[0]; //  to extend
        }

        annotateDT(invNum, rel, c, path, depth + (fwd ? 1 : -1),
                    srcVars, dstVars, fwd);
      }
    }

    void doSeedMining(Expr invRel, ExprSet& cands, set<cpp_int>& progConsts,
                        set<cpp_int>& intCoefs)
    {
      int invNum = getVarIndex(invRel, decls);
      ExprVector& srcVars = ruleManager.invVars[invRel];
      ExprVector& dstVars = ruleManager.invVarsPrime[invRel];

      SamplFactory& sf = sfs[invNum].back();
      ExprSet candsFromCode, tmpArrCands;
      bool analyzedExtras, isFalse, hasArrays = false;

      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;
        SeedMiner sm (hr, invRel, invarVars[invNum], sf.lf.nonlinVars);

        // limit only to queries:
        if (hr.isQuery) sm.analyzeCode();
        if (!analyzedExtras && hr.srcRelation == invRel)
        {
          sm.analyzeExtras (cands);
          sm.analyzeExtras (arrCands[invNum]);
          analyzedExtras = true;
        }
        for (auto &cand : sm.candidates) candsFromCode.insert(cand);
        for (auto &a : sm.intConsts) progConsts.insert(a);
        for (auto &a : sm.intCoefs) intCoefs.insert(a);

        // for arrays
        if (ruleManager.hasArrays[invRel])
        {
          tmpArrCands.insert(sm.arrCands.begin(), sm.arrCands.end());
          hasArrays = true;
        }
      }

      if (hasArrays)
      {
        ExprSet repCands;
        for (auto & a : arrCands[invNum])
        {
          getQVcands(invNum, a, repCands);
        }
        arrCands[invNum] = repCands;


        // TODO: revisit handling of nested loops
        /*
        auto nested = ruleManager.getNestedRel(invRel);
        if (nested != NULL)
        {
          int invNumTo = getVarIndex(nested->dstRelation, decls);
          // only one variable for now. TBD: find if we need more
          Expr q->qv2 = bind::intConst(mkTerm<string> ("_FH_nst_it", m_efac));
          arrAccessVars[invNum].push_back(q->qv2);

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
                replaceAll(replaceAll(range, *arrAccessVars[invNumTo].begin(), q->qv2),
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
            if (allVars.empty())
            {
              candsFromCode.insert(replCand);
              getQVcands(invNum, replCand, arrCands[invNum]);
            }
            else if (allVars.size() > 1)
              continue;      // to extend to larger allVars
            else
              for (auto & q : qvits[invNum])
                if (typeOf(*allVars.begin()) == typeOf(q->qv))
                  arrCands[invNum].insert(
                    replaceAll(replCand, *allVars.begin(), q->qv));
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

    // currently, largely based on V3's version
    bool synthesize(unsigned maxAttempts)
    {
      if (printLog) outs () << "\nSAMPLING\n========\n";
      if (printLog >= 3)
        for (auto & a : deferredCandidates)
          for (auto & b : a.second)
            outs () << "  Deferred cand for " << a.first << ": " << b << "\n";

      map<int, int> defSz;
      for (auto & a : deferredCandidates) defSz[a.first] = a.second.size();
      ExprSet cands;
      bool rndStarted = false;
      int lsz = ruleManager.loopheads.size();
      for (int i = 0; i < maxAttempts; i++)
      {
        // next cand (to be sampled)
        // TODO: find a smarter way to calculate; make parametrizable
        Expr rel = ruleManager.loopheads[i % lsz];
        int cycleNum = i % ruleManager.cycles[rel].size();
        int invNum = getVarIndex(rel, decls);
        candidates.clear();
        SamplFactory& sf = sfs[invNum].back();
        Expr cand;
        if (deferredCandidates[invNum].empty())
        {
          rndStarted = true;
          cand = sf.getFreshCandidate();  // try simple array candidates first
        }
        else
        {
          cand = deferredCandidates[invNum].back();
          deferredCandidates[invNum].pop_back();
        }
        if (cand != NULL && isOpX<FORALL>(cand) && isOpX<IMPL>(cand->last()))
        {
          if (!u.isSat(cand->last()->left())) cand = NULL;
        }
        if (cand == NULL) continue;
        if (printLog >= 3 && dRecycleCands)
          outs () << "Number of deferred candidates: "
                  << deferredCandidates[invNum].size() << "\n";
        if (printLog)
          outs () << " - - - Sampled cand (#" << i << ") for "
                  << decls[invNum] << ": "
                  << cand << (printLog >= 3 ? " 😎\n" : "\n");
        if (!addCandidate(invNum, cand)) continue;

        bool lemma_found = checkCand(invNum);
        if (dDisj && (isOp<ComparissonOp>(cand) || isOpX<FORALL>(cand)))
        {
          lemma_found = true;
          generatePhaseLemmas(invNum, cycleNum, rel, cand); //, mk<TRUE>(m_efac));
          multiHoudini(ruleManager.dwtoCHCs);
          if (printLog) outs () << "\n";
        }
        if (lemma_found)
        {
          assignPrioritiesForLearned();
          generalizeArrInvars(invNum, sf);
          if (checkAllLemmas())
          {
            outs () << "Success after " << (i+1) << " iterations "
                    << (rndStarted ? "(+ rnd)" :
                       (i > defSz[invNum]) ? "(+ rec)" : "" ) << "\n";
            printSolution();
            return true;
          }
        }
      }
      outs() << "unknown\n";
      return false;
    }

    void generateMbps(int invNum, Expr ssa, ExprVector& srcVars,
                      ExprVector& dstVars, ExprSet& cands)
    {
      ExprVector vars2keep, prjcts, prjcts1, prjcts2;
      bool hasArray = false;
      for (int i = 0; i < srcVars.size(); i++)
        if (containsOp<ARRAY_TY>(srcVars[i]))
        {
          hasArray = true;
          vars2keep.push_back(dstVars[i]);
        }
        else
          vars2keep.push_back(srcVars[i]);

      if (mbpEqs != 0)
        u.flatten(ssa, prjcts1, false, vars2keep, keepQuantifiersRepl);
      if (mbpEqs != 1)
        u.flatten(ssa, prjcts2, true, vars2keep, keepQuantifiersRepl);

      prjcts1.insert(prjcts1.end(), prjcts2.begin(), prjcts2.end());
      for (auto p : prjcts1)
      {
        if (hasArray)
        {
          getConj(replaceAll(p, dstVars, srcVars), cands);
          p = ufo::eliminateQuantifiers(p, dstVars);
          p = weakenForVars(p, dstVars);
        }
        else
        {
          p = weakenForVars(p, dstVars);
          p = simplifyArithm(normalize(p));
          getConj(p, cands);
        }
        prjcts.push_back(p);
        if (printLog >= 2) outs() << "Generated MBP: " << p << "\n";
      }

      // heuristics: to optimize the range computation
      u.removeRedundantConjunctsVec(prjcts);

      for (auto p = prjcts.begin(); p != prjcts.end(); )
      {
        if (!u.isSat(prefs[invNum], *p) &&
            !u.isSat(mkNeg(*p), ssa, replaceAll(*p, srcVars, dstVars)))
            {
              if (printLog >= 3)
                outs() << "Erasing MBP: " << *p
                       << " since it is negatively inductive\n";
              p = prjcts.erase(p);
            }
        else ++p;
      }

      if (hasArray)
      {
         // for array benchmarks, since more expensive
         // otherwise, ranges won't be computed
        u.removeRedundantDisjuncts(prjcts);
        if (prjcts.empty()) prjcts.push_back(mk<TRUE>(m_efac));
      }

      for (auto p : prjcts)
        mbps[invNum].insert(simplifyArithm(p));
    }

    Expr getMbpPost(int invNum, Expr ssa, ExprVector& srcVars, ExprVector& dstVars)
    {
      // currently, a workaround
      // it ignores the pointers to mbps at qvits and sortedMbps
      // TODO: support
      ExprSet cur_mbps;
      for (auto & m : mbps[invNum])
        if (u.isSat(replaceAll(m, srcVars, dstVars), ssa))
          cur_mbps.insert(m);
      return simplifyBool(distribDisjoin(cur_mbps, m_efac));
    }

    void generateMbpDecisionTree(int invNum, ExprVector& srcVars,
                                 ExprVector& dstVars, int f = 0)
    {
      int sz = mbpDt[invNum].sz;
      if (f == 0)
      {
        assert(sz == 0);
        mbpDt[invNum].addEmptyEdge();
        sz++;
      }

      for (auto mbp = mbps[invNum].begin(); mbp != mbps[invNum].end(); ++mbp)
      {
        if (mbpDt[invNum].hasEdge(f, *mbp)) continue;
        ExprSet constr;
        if (f == 0) constr = {*mbp, prefs[invNum]};
        else constr = {mbpDt[invNum].tree_cont[f], ssas[invNum],
              replaceAll(mk<AND>
                (mkNeg(mbpDt[invNum].tree_cont[f]), *mbp), srcVars, dstVars)};
        if (u.isSat(constr))
        {
          if (f == 0) mbpDt[invNum].addEdge(f, *mbp);
          else
            if (mbpDt[invNum].getExprInPath(f, *mbp) < 0)    // to avoid cycles
              mbpDt[invNum].addEdge(f, *mbp);
        }
      }
      for (; sz < mbpDt[invNum].sz; sz++)
        generateMbpDecisionTree(invNum, srcVars, dstVars, sz);
    }

    void strengthenMbpDecisionTree(int invNum, ExprVector& srcVars, ExprVector& dstVars)
    {
      strenDt[invNum] = mbpDt[invNum];
      for (int i = 0; i < strenDt[invNum].tree_cont.size(); i++)
        strenDt[invNum].tree_cont[i] = mk<TRUE>(m_efac);
      if (!dStrenMbp) return;     // by default, strenghtening is disabled

      for (auto & s : mbpDt[invNum].tree_edgs)
      {
        if (s.second.size() == 0) continue; // leaves, nothing to strenghten
        Expr rootStr = strenDt[invNum].tree_cont[s.first];

        ExprVector constr;
        if (s.first == 0) constr = {prefs[invNum]};
        else constr = { mbpDt[invNum].tree_cont[s.first], ssas[invNum],
                replaceAll(mkNeg(mbpDt[invNum].tree_cont[s.first]), srcVars, dstVars) };

        for (auto & v : srcVars)
        {
          ExprVector allStrs;
          ExprVector abdVars = {v};
          for (auto & e : s.second)
          {
            Expr mbp = mbpDt[invNum].tree_cont[e];
            Expr abd = simplifyArithm(mkNeg(ufo::keepQuantifiers(
                          mkNeg(mk<IMPL>(conjoin(constr, m_efac), mbp)), abdVars)));
            if (!isOpX<FALSE>(abd) &&
              u.implies(mk<AND>(abd, ssas[invNum]), replaceAll(abd, srcVars, dstVars)))
                allStrs.push_back(abd);
          }
          if (!u.isSat(allStrs))
          {
            for (int i = 0; i < s.second.size(); i++)
            {
              strenDt[invNum].tree_cont[s.second[i]] = allStrs[i];
              if (printLog >= 2)
              {
                auto e = s.second[i];
                outs () << "Found strengthening: "
                        << strenDt[invNum].tree_cont[e] << " for "
                        << mbpDt[invNum].tree_cont[e] << "\n";
              }
            }
            break;
          }
        }
        if (s.first > 0 && !isOpX<TRUE>(rootStr))
        {
          for (auto & e : s.second)
            if (isOpX<TRUE>(strenDt[invNum].tree_cont[e]))
              strenDt[invNum].tree_cont[e] = rootStr;
            else
              strenDt[invNum].tree_cont[e] =
                mk<AND>(rootStr, strenDt[invNum].tree_cont[e]);
        }
      }
    }

    Expr generatePostcondsFromPhases(int invNum, Expr cnt, vector<int>& extMbp,
                      Expr ssa, int p, ExprVector& srcVars, ExprVector& dstVars)
    {
      auto &path = mbpDt[invNum].paths[p];
      Expr pre, phase = NULL;
      for (int i = 0; i < extMbp.size(); i++)
      {
        Expr mbp = mbpDt[invNum].tree_cont[path[extMbp[i]]];
        Expr phaseCur = u.simplifiedAnd(ssa, mbp);
        Expr preCur = keepQuantifiers(phaseCur, srcVars);
        preCur = weakenForHardVars(preCur, srcVars);
        preCur = projectVar(preCur, cnt);
        if (i == 0)
          pre = preCur;
        else if (!u.isSat(pre, phaseCur))
          pre = preCur;
        else
        {
          pre = keepQuantifiers(mk<AND>(pre, phase), dstVars);
          pre = weakenForHardVars(pre, dstVars);
          pre = replaceAll(pre, dstVars, srcVars);
          pre = projectVar(pre, cnt);
          pre = u.removeRedundantConjuncts(mk<AND>(preCur, pre));
        }
        phase = phaseCur;
      }
      return pre;
    }

    bool updateRanges(int invNum, ArrAccessIter* newer)
    {
      for (int i = 0; i < qvits[invNum].size(); i++)
      {
        auto & existing = qvits[invNum][i];
        if (existing->iter != newer->iter) continue;
        Expr newra = replaceAll(newer->range, newer->qv, existing->qv);
        bool toRepl = false;
        if (u.implies(newra, existing->range))
        {
          if (newer->closed == existing->closed)
            return false;
          if (newer->closed && !existing->closed)
            toRepl = true;
        }
        if (toRepl || u.implies(existing->range, newra))// new one is more general
        {
          if (newer->closed || !existing->closed)
          {
            qvits[invNum][i] = newer;
            if (printLog >= 2) outs () << "Re";     // continued in `createArrAcc`
            return true;
          }
          if (!newer->closed && existing->closed)
            return false;
        }
      }
      qvits[invNum].push_back(newer);
      return true;
    }

    void initializeAux(ExprSet& cands, BndExpl& bnd, Expr dcl, int cycleNum, Expr pref)
    {
      vector<int>& cycle = ruleManager.cycles[dcl][cycleNum];
      HornRuleExt* hr = &ruleManager.chcs[cycle[0]];
      Expr rel = hr->srcRelation;
      ExprVector& srcVars = hr->srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;
      assert(srcVars.size() == dstVars.size());

      int invNum = getVarIndex(rel, decls);
      prefs[invNum] = pref;
      Expr ssa = bnd.toExpr(cycle);
      ssa = replaceAll(ssa, bnd.bindVars.back(), dstVars);
      ssas[invNum] = ssa;
      ssa = rewriteSelectStore(ssa);
      retrieveDeltas(ssa, srcVars, dstVars, cands);
      generateMbps(invNum, ssa, srcVars, dstVars, cands);

      if (dDisj || containsOp<ARRAY_TY>(ssas[invNum]))
      {
        generateMbpDecisionTree(invNum, srcVars, dstVars);
        mbpDt[invNum].deleteIntermPaths();
        strengthenMbpDecisionTree(invNum, srcVars, dstVars);
        if (printLog >= 2)
          outs () << "MBPs are organized as a decision tree (with "
                  << mbpDt[invNum].paths.size() << " possible path(s))\n";
        if (printLog >= 3)
          mbpDt[invNum].print();
      }

      if (qvits[invNum].size() > 0) return;
      if (!containsOp<ARRAY_TY>(ssas[invNum])) return;

      filter (ssas[invNum], bind::IsConst (),
                                inserter(qvars[invNum], qvars[invNum].begin()));
      for (int i = 0; i < dstVars.size(); i++)
      {
        Expr a = srcVars[i];
        Expr b = dstVars[i];
        if (!bind::isIntConst(a)) continue;
        if (u.implies(ssa, mk<EQ>(a, b))) continue;

        if (printLog >= 3)
          outs () << "Considering variable " << a << " as a counter \n";
        for (int p = 0; p < mbpDt[invNum].paths.size(); p++)
        {
          if (printLog >= 3) outs () << "MBP Path # " << p <<"\n";
          Expr extPref = pref;
          vector<int> extMbp;
          tribool grows = indeterminate;
          auto &path = mbpDt[invNum].paths[p];
          for (int m = 0; m < path.size(); m++)
          {
            Expr & mbp = mbpDt[invNum].tree_cont[path[m]];
            tribool growsCur = u.implies(mk<AND>(mbp, ssa), mk<GEQ>(b, a));
            if (growsCur != 1)
              if (!u.implies(mk<AND>(mbp, ssa), mk<GEQ>(a, b)))
                growsCur = indeterminate;

            if (printLog >= 3)
            {
              if (indeterminate(growsCur))
                outs () << "  mbp 👎: " << mbp << "\n";
              else outs () << "  mbp 👍 for " << a << ": " << mbp << "\n";
            }
            bool toCont = true;
            if (extMbp.empty())                         // new meta-phase begins
            {
              grows = growsCur;
              if (!indeterminate(growsCur))
              {
                extMbp = {m};
                if (m > 0)
                {
                  extPref = u.simplifiedAnd(ssa, mbpDt[invNum].tree_cont[path[m-1]]);
                  extPref = keepQuantifiersRepl (extPref, dstVars);
                  extPref = u.removeITE(replaceAll(extPref, dstVars, srcVars));
                }
              }
              toCont = false;
            }
            else if (grows == growsCur && (!indeterminate(growsCur)))
            {                // meta-phase continues
              extMbp.push_back(m);
              toCont = false;
            }

            // for the last one, or any where the cnt direction changes:
            if (!extMbp.empty() && (toCont || m == path.size() - 1))
              if (createArrAcc(rel, invNum, a, (bool)grows, extMbp, extPref,
                generatePostcondsFromPhases(invNum, a, extMbp, ssa, p,
                                                            srcVars, dstVars)))
                  extMbp.clear();               // 👍 for the next phase
          }
        }
      }

      if (!qvits[invNum].empty()) {
        if (printLog >= 3) outs() << "rel: " << rel << " : has arrays\n";
        ruleManager.hasArrays[rel] = true;
      }
    }
  };

  // same as learnInvariants3, to unify somehow, maybe
  inline void learnInvariants4(string smt, unsigned maxAttempts, unsigned to,
       bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
       bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
       bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
       bool dSee, bool ser, int debug)
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

    RndLearnerV4 ds(m_efac, z3, ruleManager, to, freqs, aggp, mut, dat,
                    doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp,
                    dFwd, dRec, dGenerous, debug);

    map<Expr, ExprSet> cands;
    for (auto& cyc : ruleManager.cycles)
    {
      Expr rel = cyc.first;
      for (int i = 0; i < cyc.second.size(); i++)
      {
        assert(rel == ruleManager.chcs[cyc.second[i][0]].srcRelation);
        if (ds.initializedDecl(rel)) continue;
        ds.initializeDecl(rel);
        if (!dSee) continue;

        Expr pref = bnd.compactPrefix(rel, i);
        ExprSet tmp;
        getConj(pref, tmp);
        for (auto & t : tmp)
        if (hasOnlyVars(t, ruleManager.invVars[rel]))
        cands[rel].insert(t);

        if (mut > 0) ds.mutateHeuristicEq(cands[rel], cands[rel], rel, true);
        ds.initializeAux(cands[rel], bnd, rel, i, pref);
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
