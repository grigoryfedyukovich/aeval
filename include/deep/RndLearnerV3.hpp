#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearner.hpp"

#ifdef HAVE_ARMADILLO
#include "DataLearner.hpp"
#endif

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearnerV3 : public RndLearnerV2
  {
    private:

    ExprSet checked;
    set<HornRuleExt*> propped;
    map<int, ExprVector> candidates;
    map<int, deque<Expr>> deferredCandidates;
    int updCount = 1;
    bool boot = true;

    // extra options for disjunctive invariants
    unsigned dCandNum = 0;
    unsigned dAttNum = 100;
    unsigned dDepNum = 3;
    bool dAllMbp;
    bool dAddProp;
    bool dAddDat;
    bool dStrenMbp;

    map<int, Expr> iterators; // per cycle
    map<int, Expr> preconds;
    map<int, Expr> postconds;
    map<int, Expr> ssas;
    map<int, Expr> prefs;
    map<int, ExprSet> qvars;
    map<int, bool> iterGrows;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, unsigned to, bool freqs, bool aggp,
                  bool _dAllMbp, bool _dAddProp, bool _dAddDat, bool _dStrenMbp) :
      RndLearnerV2 (efac, z3, r, to, freqs, aggp),
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

    Expr renameCand(Expr newCand, ExprVector& varsRenameFrom, int invNum)
    {
      for (auto & v : invarVars[invNum])
        newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
      return newCand;
    }

    Expr eliminateQuantifiers(Expr e, ExprVector& varsRenameFrom, int invNum, bool bwd)
    {
      ExprSet complex;
      if (!containsOp<FORALL>(e))
      {
        e = rewriteSelectStore(e);
        findComplexNumerics(e, complex);
      }
      ExprMap repls;
      ExprMap replsRev;
      map<Expr, ExprSet> replIngr;
      for (auto & a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>
              ("__repl_" + lexical_cast<string>(repls.size()), m_efac));
        repls[a] = repl;
        replsRev[repl] = a;
        ExprSet tmp;
        filter (a, bind::IsConst (), inserter (tmp, tmp.begin()));
        replIngr[repl] = tmp;
      }
      Expr eTmp = replaceAll(e, repls);

      ExprSet ev3;
      filter (eTmp, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(varsRenameFrom.begin(), varsRenameFrom.end(), *it) != varsRenameFrom.end()) it = ev3.erase(it);
        else
        {
          Expr tmp = replsRev[*it];
          if (tmp == NULL) ++it;
          else
          {
            ExprSet tmpSet = replIngr[*it];
            minusSets(tmpSet, varsRenameFrom);
            if (tmpSet.empty()) it = ev3.erase(it);
            else ++it;
          }
        }
      }

      eTmp = ufo::eliminateQuantifiers(eTmp, ev3);
      if (bwd) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(/*simplifyArithm*/(eTmp /*, false, true*/));
      e = replaceAll (eTmp, replsRev);
      e = renameCand(e, varsRenameFrom, invNum);
      return e;
    }

    void addPropagatedArrayCands(Expr rel, int invNum, Expr candToProp)
    {
      vector<int> tmp;
      ruleManager.getCycleForRel(rel, tmp);
      if (tmp.size() != 1) return; // todo: support

      Expr fls = replaceAll(candToProp->last()->right(),
                            *arrAccessVars[invNum].begin(), iterators[invNum]);
      Expr bdy = rewriteSelectStore(ruleManager.chcs[tmp[0]].body);

      ExprVector ev;
      for (int h = 0; h < ruleManager.chcs[tmp[0]].dstVars.size(); h++)
      {
        Expr var = ruleManager.chcs[tmp[0]].srcVars[h];
        if (iterators[invNum] == var)
          ev.push_back(iterators[invNum]);
        else
          ev.push_back(ruleManager.chcs[tmp[0]].dstVars[h]);
      }

      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(fls, cnjs);
      getConj(bdy, cnjs);
      for (auto & a : cnjs) // hack
      {
        if (isOpX<EQ>(a) && !isNumeric(a->left())) continue;
        newCnjs.insert(a);
      }
      ExprMap mp;
      bdy = replaceSelects(conjoin(newCnjs, m_efac), mp);
      for (auto & a : mp)
      {
        if (!emptyIntersect(a.first, ruleManager.chcs[tmp[0]].dstVars))
        {
          ev.push_back(a.second);
        }
      }

      Expr newCand2;
      cnjs.clear();
      getConj(eliminateQuantifiers(bdy, ev, invNum, false), cnjs);
      for (auto & c : cnjs)
      {
        if (u.isTrue(c) || u.isFalse(c)) continue;
        Expr e = ineqNegReverter(c);
        if (isOp<ComparissonOp>(e))
        {
          for (auto & a : mp) e = replaceAll(e, a.second, a.first);
          if (containsOp<ARRAY_TY>(e) && !emptyIntersect(iterators[invNum], e))
          {
            e = replaceAll(e, iterators[invNum], *arrAccessVars[invNum].begin());
            e = renameCand(e, ruleManager.chcs[tmp[0]].dstVars, invNum);

            // workaround: it works only during bootstrapping now
            arrCands[invNum].insert(e);
          }
        }
      }
    }

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, Expr relFrom, ExprVector& varsRenameFrom, Expr rel, bool seed, bool fwd)
    {
      if (!containsOp<FORALL>(candToProp) && !u.isSat(candToProp, constraint))
        return false; // sometimes, maybe we should return true.

      int invNum = getVarIndex(rel, decls);
      Expr newCand;

      if (containsOp<FORALL>(candToProp))
      {
        // GF: not tested for backward propagation
        if (fwd == false) return true;
        if (finalizeArrCand(candToProp, constraint, relFrom))
        {
          addPropagatedArrayCands(rel, invNum, candToProp);
          newCand = getForallCnj(eliminateQuantifiers(
                        mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;
          // GF: temporary workaround:
          // need to support Houdini for arrays, to be able to add newCand and newCand1 at the same time
          Expr newCand1 = replaceArrRangeForIndCheck(invNum, newCand, true);
          auto candsTmp = candidates;
          candidates[invNum].push_back(newCand);
          bool res = checkCand(invNum, false) &&
                     propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
          if (!candidates[invNum].empty()) return res;
          if (newCand1 == NULL) return true;
          candidates = candsTmp;
          candidates[invNum].push_back(newCand1);
        }
        else
        {
          // very ugly at the moment, to be revisited
          newCand = getForallCnj(eliminateQuantifiers(
                          mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;
          candidates[invNum].push_back(newCand);
        }
        return checkCand(invNum, false) &&
               propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
      }
      newCand = eliminateQuantifiers(
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
      SamplFactory& sf = sfs[invNum].back();
      Expr allLemmas = sf.getAllLemmas();
      if (containsOp<FORALL>(cnd) || containsOp<FORALL>(allLemmas))
      {
        if (containsOp<FORALL>(cnd))
        {
          auto hr = ruleManager.getFirstRuleOutside(decls[invNum]);
          assert(hr != NULL);

          ExprSet cnjs;
          ExprSet newCnjs;
          Expr it = iterators[invNum];
          if (it != NULL) cnd = replaceArrRangeForIndCheck (invNum, cnd);
        }
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

      cand = replaceAll(cand, cand->last()->left(), conjoin(arrIterRanges[invNum], m_efac));
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
      Expr itRepl = iterators[invNum];
      Expr post = postconds[invNum];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(cand->last()->left(), cnjs);

      // TODO: support the case when there are two or more quantified vars

      Expr it = bind::fapp(cand->arg(0));
      ExprSet extr;
      if      (iterGrows[invNum] && fwd)   extr.insert(mk<GEQ>(it, itRepl));
      else if (iterGrows[invNum] && !fwd)   extr.insert(mk<LT>(it, itRepl));
      else if (!iterGrows[invNum] && fwd)  extr.insert(mk<LEQ>(it, itRepl));
      else if (!iterGrows[invNum] && !fwd)  extr.insert(mk<GT>(it, itRepl));

      extr.insert(cand->last()->left());
      return replaceAll(cand, cand->last()->left(), conjoin(extr, m_efac));
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
                  sf.learnedExprs.insert(newCand);
                }
              }
            }
          }
        }
      }
    }

    void assignPrioritiesForLearned()
    {
//      bool progress = true;
      for (auto & cand : candidates)
      {
        if (cand.second.size() > 0)
        {
          ExprVector invVars;
          for (auto & a : invarVars[cand.first]) invVars.push_back(a.second);
          SamplFactory& sf = sfs[cand.first].back();
          for (auto b : cand.second)
          {
            b = simplifyArithm(b);
            if (containsOp<ARRAY_TY>(b) || findNonlin(b))
            {
              sf.learnedExprs.insert(b);
            }
            else
            {
              Expr learnedCand = normalizeDisj(b, invVars);
              Sampl& s = sf.exprToSampl(learnedCand);
              sf.assignPrioritiesForLearned();
              if (!u.implies(sf.getAllLemmas(), learnedCand))
                sf.learnedExprs.insert(learnedCand);
            }
//            else progress = false;
          }
        }
      }
//            if (progress) updateGrammars(); // GF: doesn't work great :(
    }

    Expr mkImplCnd(Expr pre, Expr cand)
    {
      if (isOpX<FORALL>(cand))
      {
        Expr tmp = cand->last()->right();
        return replaceAll(cand, tmp, mkImplCnd(pre, tmp));
      }
      return mk<IMPL>(pre, cand);
    }

    bool synthesizeDisjLemmas(int invNum, int cycleNum, Expr rel,
                              Expr cnd, Expr splitter, Expr ind, unsigned depth)
    {
      if (dCandNum++ == dAttNum || depth == dDepNum) return true;
      Expr invs = conjoin(sfs[invNum].back().learnedExprs, m_efac);
      if (isOpX<FORALL>(cnd)) cnd = replaceArrRangeForIndCheck (invNum, cnd);
      vector<int>& cycle = ruleManager.cycles[cycleNum];
      ExprVector& srcVars = ruleManager.chcs[cycle[0]].srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;
      Expr cndPrime = replaceAll(cnd, srcVars, dstVars);
      Expr cndSsa = mk<AND>(cnd, ssas[invNum]);
      Expr cndSsaPr = mk<AND>(cndSsa, cndPrime);

      ExprVector mbps;

      while (true)
      {
        Expr avail = mkNeg(disjoin(mbps, m_efac));
        Expr fla;     // to weaken MBP further
        if (!isOpX<TRUE>(splitter) || !u.isSat(avail, prefs[invNum], cndSsaPr))
          if (!u.isSat(avail, splitter, cndSsaPr))
            if (!u.isSat(avail, splitter, cndSsa)){ break; }
            else fla = mk<AND>(splitter, cndSsa);
          else fla = mk<AND>(splitter, cndSsaPr);
        else fla = mk<AND>(prefs[invNum], cndSsaPr);

        Expr lastModel = u.getModel();
        if (lastModel == NULL) break;
        if (u.isModelSkippable()) break;

        Expr mbp = u.getWeakerMBP(
                     keepQuantifiers (
                       u.getTrueLiterals(ssas[invNum], lastModel), srcVars), fla, srcVars);
        bool toadd = true;
        for (int j = 0; j < mbps.size(); j++)
          if (u.isSat(mbps[j], mbp))
          {
            mbps[j] = mk<OR>(mbps[j], mbp);
            toadd = false;
            break;
          }
        if (toadd) mbps.push_back(mbp);
        if (isOpX<FORALL>(cnd)) break; // temporary workarond for arrays (z3 might fail in giving models)
        if (!dAllMbp) break;
      }

      for (auto mbp : mbps)
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
          Expr splitterArr = replaceAll(mk<AND>(splitter, mbp),
                    iterators[invNum], *arrAccessVars[invNum].begin());
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

        map<Expr, ExprSet> cands;

        if (dAddProp)
        {
          ExprSet s;
          s.insert(mbp);
          s.insert(splitter);
          s.insert(ind);
          s.insert(cnd);
          s.insert(ssas[invNum]);
          s.insert(mkNeg(replaceAll(mk<AND>(mk<AND>(splitter, ind), mbp), srcVars, dstVars)));
          Expr newCand = keepQuantifiers (conjoin(s, m_efac), dstVars);
          newCand = u.removeITE(replaceAll(newCand, dstVars, srcVars));
          getConj(newCand, cands[rel]);
        }

        if (dAddDat)
          getDataCandidates(cands, rel, mkNeg(mbp), mk<AND>(candImpl, invs));

        // postprocess behavioral arrCands
        if (!arrCands[invNum].empty())
          for (auto & a : arrCands[invNum])
            cands[rel].insert(
              sfs[invNum].back().af.getSimplCand(
                replaceAll(a, iterators[invNum], *arrAccessVars[invNum].begin())));

        for (auto & c : cands[rel])
        {
          if (c == cnd) continue;
          if(isOpX<FORALL>(cnd) && !isOpX<FORALL>(c)) continue;
          synthesizeDisjLemmas(invNum, cycleNum, rel, c, mk<AND>(splitter, mkNeg(mbp)), ind, depth + 1);
          if (isOpX<FORALL>(cnd)) break; // temporary workarond for arrays (z3 might fail in giving models)
        }
      }
      return true;
    }

    bool synthesize(unsigned maxAttempts, bool doDisj)
    {
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
        if (deferredCandidates[invNum].empty())
          cand = sf.getFreshCandidate(i < 25);  // try simple array candidates first
        else {
          cand = deferredCandidates[invNum].back();
          deferredCandidates[invNum].pop_back();
        }
        if (cand != NULL && isOpX<FORALL>(cand) && isOpX<IMPL>(cand->last()))
        {
          if (!u.isSat(cand->last()->left())) cand = NULL;
        }
        if (cand == NULL) continue;
        if (printLog) outs () << " - - - sampled cand (#" << i << ") for " << *decls[invNum] << ": " << *cand << "\n";
        if (!addCandidate(invNum, cand)) continue;

        bool lemma_found = checkCand(invNum);
        if (doDisj && (isOp<ComparissonOp>(cand) || isOpX<FORALL>(cand)))
        {
          dCandNum = 0;
          lemma_found = synthesizeDisjLemmas(invNum, cycleNum, rel, cand, mk<TRUE>(m_efac), mk<TRUE>(m_efac), 0) &&
                        multiHoudini(ruleManager.wtoCHCs);
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

    bool multiHoudini(vector<HornRuleExt*> worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) return false;
      map<int, ExprVector> candidatesTmp = candidates;
      bool res1 = true;
      for (auto &h: worklist)
      {
        HornRuleExt& hr = *h;

        if (hr.isQuery) continue;

        boost::tribool b = checkCHC(hr, candidatesTmp);
        if (b || indeterminate(b))
        {
          bool res2 = true;
          int ind = getVarIndex(hr.dstRelation, decls);

          Expr model = NULL;
          if (b) model = u.getModel(hr.dstVars);

          if (u.isModelSkippable(model, hr.dstVars, candidatesTmp))
          {
            // something went wrong with z3. do aggressive weakening (TODO: try bruteforce):
            // candidatesTmp[ind].clear();
            candidatesTmp[ind].pop_back();
            res2 = false;
          }
          else
          {
            ExprVector& ev = candidatesTmp[ind];
            ExprVector invVars;
            for (auto & a : invarVars[ind]) invVars.push_back(a.second);
            SamplFactory& sf = sfs[ind].back();

            for (auto it = ev.begin(); it != ev.end(); )
            {
              Expr repl = *it;
              for (auto & v : invarVars[ind]) repl = replaceAll(repl, v.second, hr.dstVars[v.first]);

              if (!u.isSat(model, repl))
              {
                if (hr.isFact)
                {
                  Expr failedCand = normalizeDisj(*it, invVars);
//                outs () << "failed cand for " << *hr.dstRelation << ": " << *failedCand << "\n";
                  Sampl& s = sf.exprToSampl(failedCand);
                  sf.assignPrioritiesForFailed();
                }
                if (boot)
                {
                  if (isOpX<EQ>(*it)) deferredCandidates[ind].push_back(*it);  //  prioritize equalities
                  else deferredCandidates[ind].push_front(*it);
                }
                it = ev.erase(it);
                res2 = false;
              }
              else
              {
                ++it;
              }
            }
          }

          if (recur && !res2)
          {
            res1 = false;
            break;
          }
        }
      }
      candidates = candidatesTmp;
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

    bool toCont(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));
      bool toCont = true;
      for (auto & expr : vars)
      {
        if (!findInvVar(invNum, expr, ve))
        {
          toCont = false;
          break;
        }
      }
      return toCont;
    }

    // heuristic to instantiate a quantified candidate for some particular instances
    void createGroundInstances (ExprSet& vals, ExprSet& res, Expr qcand, Expr iterVar)
    {
      ExprSet se;
      filter (qcand, bind::IsSelect (), inserter(se, se.begin()));

      for (auto & a : se)
      {
        if (iterVar == a->right())
        {
          for (auto & v : vals)
          {
            res.insert(replaceAll(qcand, iterVar, v));
          }
        }
      }
    }

    // heuristic to replace weird variables in candidates
    bool prepareArrCand (Expr& replCand, ExprMap& replLog, ExprVector& av,
                         ExprSet& tmpRanges, ExprSet& concreteVals, int ind, int i = 0)
    {
      if (av.empty()) return false;

      ExprSet se;
      filter (replCand, bind::IsSelect (), inserter(se, se.begin()));

      for (auto & a : se)
      {
        if (isOpX<MPZ>(a->right())  || (!findInvVar(ind, a->right(), av)))
        {
          if (isOpX<MPZ>(a->right()))
          {
            tmpRanges.insert(mk<EQ>(av[i], a->right()));
            concreteVals.insert(a->right());
          }
          // TODO:  try other combinations of replacements
          if (i >= av.size()) return false;
          replLog[a->right()] = av[i];
          replCand = replaceAll(replCand, a->right(), replLog[a->right()]);

          return prepareArrCand (replCand, replLog, av, tmpRanges, concreteVals, ind, i + 1);
        }
      }
      return true;
    }

    // adapted from doSeedMining
    void getSeeds(Expr invRel, map<Expr, ExprSet>& cands, bool analizeCode = true)
    {
      int ind = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[ind].back();
      ExprSet candsFromCode;
      bool analizedExtras = false;
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
        SeedMiner sm (hr, invRel, invarVars[ind], sf.lf.nonlinVars);

        if (analizeCode) sm.analizeCode();
        else sm.candidates.clear();
        if (!analizedExtras && hr.srcRelation == invRel)
        {
          sm.analizeExtras (cands[invRel]);
          analizedExtras = true;
        }
        for (auto &cand : sm.candidates) candsFromCode.insert(cand);

        // for arrays
        if (analizeCode && ruleManager.hasArrays[invRel])
        {
          tmpArrCands.insert(sm.arrCands.begin(), sm.arrCands.end());
          tmpArrSelects.insert(sm.arrSelects.begin(), sm.arrSelects.end());
          tmpArrFuns.insert(sm.arrFs.begin(), sm.arrFs.end());
          hasArrays = true;
        }
      }

      if (hasArrays)
      {
        Expr pre = preconds[ind];
        if (pre != NULL)
        {
          pre = ineqSimplifier(iterators[ind], pre);
          Expr qVar = bind::intConst(mkTerm<string> ("_FH_arr_it", m_efac));
          arrAccessVars[ind].push_back(qVar);

          assert (isOpX<EQ>(pre)); // TODO: support more

          ExprVector invAndIterVarsAll;
          for (auto & a : invarVars[ind]) invAndIterVarsAll.push_back(a.second);
          invAndIterVarsAll.push_back(qVar);

          Expr fla;
          if (pre->right() == iterators[ind])
            fla = (iterGrows[ind]) ? mk<GEQ>(qVar, pre->left()) :
                                     mk<LEQ>(qVar, pre->left());
          else if (pre->left() == iterators[ind])
            fla = (iterGrows[ind]) ? mk<GEQ>(qVar, pre->right()) :
                                     mk<LEQ>(qVar, pre->right());

          ExprSet tmp;
          getConj(postconds[ind], tmp);
          for (auto it = tmp.begin(); it != tmp.end(); )
            if (contains(*it, iterators[ind])) ++it; else it = tmp.erase(it);

          arrIterRanges[ind].insert(normalizeDisj(fla, invAndIterVarsAll));
          arrIterRanges[ind].insert(normalizeDisj(
                  replaceAll(conjoin(tmp, m_efac), iterators[ind], qVar), invAndIterVarsAll));

          // repair behavioral arrCands
          if (!arrCands[ind].empty())
          {
            ExprSet repCands;
            for (auto & a : arrCands[ind])
              repCands.insert(replaceAll(a, iterators[ind], qVar));
            arrCands[ind] = repCands;
          }
        }

        auto nested = ruleManager.getNestedRel(invRel);
        if (nested != NULL)
        {
          int invNumTo = getVarIndex(nested->dstRelation, decls);
          // only one variable for now. TBD: find if we need more
          Expr qVar2 = bind::intConst(mkTerm<string> ("_FH_nst_it", m_efac));
          arrAccessVars[ind].push_back(qVar2);

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
          arrIterRanges[ind].insert(
                replaceAll(replaceAll(range, *arrAccessVars[invNumTo].begin(), qVar2),
                      iterators[ind], *arrAccessVars[ind].begin()));
        }

        // process all quantified seeds
        for (auto & a : tmpArrCands)
        {
          if (u.isTrue(a) || u.isFalse(a)) continue;
          Expr replCand = replaceAllRev(a, sf.lf.nonlinVars);
          if (!u.isTrue(replCand) && !u.isFalse(replCand))
          {
            ExprMap replLog;
            ExprSet tmpRanges;
            ExprSet concreteVals;
            if (prepareArrCand (replCand, replLog, arrAccessVars[ind], tmpRanges, concreteVals, ind) &&
               (contains(replCand, iterators[ind]) || !emptyIntersect(replCand, arrAccessVars[ind])))
            {
              /*
              // very cheeky heuristic: sometimes restrict, but sometimes extend the range
              // depending on existing constants
              if (u.isSat(conjoin(tmpRanges, m_efac), conjoin(arrIterRanges[ind], m_efac)))
              {
                arrIterRanges[ind].insert(tmpRanges.begin(), tmpRanges.end());
              }
              else
              {
                for (auto & a : tmpArrCands)
                  createGroundInstances (concreteVals, candsFromCode, a, iterators[ind]);
              }
               */

              // at this point it should not happen, but sometimes it does. To debug.
              if (!findInvVar(ind, replCand, arrAccessVars[ind])) continue;

              for (auto iter : arrAccessVars[ind])
                arrCands[ind].insert(replaceAll(replCand, iterators[ind], iter));
            }
            else candsFromCode.insert(a);
          }
        }

        // trick for tiling benchs
        ExprSet afs;
        for (auto & a : tmpArrFuns)
        {
          ExprVector vars;
          filter (a, bind::IsConst(), std::inserter (vars, vars.begin ()));
          if (vars.size() != 1 || *vars.begin() == a) continue;
          afs.insert(replaceAll(a, *vars.begin(), arrAccessVars[ind][0]));
        }

        for (auto & s : afs)
        {
          for (auto & qcand : arrCands[ind])
          {
            ExprSet se;
            filter (qcand, bind::IsSelect (), inserter(se, se.begin()));
            for (auto & arrsel : se)
            {
              Expr qcandTmp = replaceAll(qcand, arrsel->right(), s);
              arrCands[ind].insert(qcandTmp);
            }
          }
        }
      }
      // process all quantifier-free seeds
      for (auto & cand : candsFromCode)
      {
        Expr replCand = replaceAllRev(cand, sf.lf.nonlinVars);
        // sanity check for replCand:
        if (toCont (ind, replCand, arrAccessVars[ind]) && addCandidate(ind, replCand))
          propagate (ind, replCand, true);
      }
    }

    void refreshCands(map<Expr, ExprSet>& cands)
    {
      cands.clear();
      for (auto & a : candidates)
      {
        cands[decls[a.first]].insert(a.second.begin(), a.second.end());
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

    void getDataCandidates(map<Expr, ExprSet>& cands, Expr srcRel = NULL,
                           Expr splitter = NULL, Expr invs = NULL){
#ifdef HAVE_ARMADILLO
      DataLearner dl(ruleManager, m_z3);
      if (srcRel == NULL || splitter == NULL) dl.computeData();
      for (auto & dcl : decls) {
        int invNum = getVarIndex(dcl, decls);
        ExprSet poly;
        if (srcRel == dcl && splitter != NULL) dl.computeData(srcRel, splitter, invs);
        dl.computePolynomials(dcl, poly);
        for (auto & a : dl.getConcrInvs(dcl)) cands[dcl].insert(a);
        mutateHeuristicEq(poly, cands[dcl], dcl, (splitter == NULL));
      }
#else
      outs() << "Skipping learning from data as required library (armadillo) not found\n";
#endif
    }

    void mutateHeuristicEq(ExprSet& src, ExprSet& dst, Expr dcl, bool toProp)
    {
        int invNum = getVarIndex(dcl, decls);
        ExprSet src2;
        map<Expr, ExprVector> substs;
        // create various combinations:
        for (auto a1 = src.begin(); a1 != src.end(); ++a1)
        {
          if (!isOpX<EQ>(*a1) || !isNumeric((*a1)->left())) continue;
          for (auto a2 = std::next(a1); a2 != src.end(); ++a2)
          {
            if (!isOpX<EQ>(*a2) || !isNumeric((*a2)->left())) continue;
            src2.insert(mk<EQ>(mk<PLUS>((*a1)->left(), (*a2)->left()),
                                         mk<PLUS>((*a1)->right(), (*a2)->right())));
            src2.insert(mk<EQ>(mk<MINUS>((*a1)->left(), (*a2)->left()),
                                         mk<MINUS>((*a1)->right(), (*a2)->right())));
            src2.insert(mk<EQ>(mk<PLUS>((*a1)->left(), (*a2)->right()),
                                         mk<PLUS>((*a1)->right(), (*a2)->left())));
            src2.insert(mk<EQ>(mk<MINUS>((*a1)->left(), (*a2)->right()),
                                         mk<MINUS>((*a1)->right(), (*a2)->left())));
          }
        }

        for (auto a : src)
        {
          if (!isOpX<EQ>(a) || !isNumeric(a->left())) continue;
          // before pushing them to the cand set, we do some small mutations to get rid of specific consts
          a = simplifyArithm(normalize(a));
          if (isOpX<EQ>(a) && isIntConst(a->left()) &&
              isNumericConst(a->right()) && lexical_cast<string>(a->right()) != "0")
            substs[a->right()].push_back(a->left());
          src2.insert(a);
        }

        for (auto a : src2)
        {
          if (!u.isSat(mk<NEG>(a))) continue;
          a = simplifyArithm(normalize(a));
          if (printLog) outs () << "CAND FROM DATA: " << *a << "\n";

          if (toProp) propagate(dcl, a, true);

          if (containsOp<ARRAY_TY>(a))
            arrCands[invNum].insert(a);
          else
            u.insertUnique(a, dst);
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
                    u.insertUnique(e, dst);
                  if (printLog) outs () << "CAND FROM DATA: " << *e << "\n";
                }
            }
          }
        }
    }

    bool bootstrap(bool doDisj)
    {
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
      //if (ruleManager.hasArrays)
      {
        for (auto & dcl: ruleManager.wtoDecls)
        {
          int invNum = getVarIndex(dcl, decls);
          SamplFactory& sf = sfs[invNum].back();
          for (auto it = arrCands[invNum].begin(); it != arrCands[invNum].end();
               it = arrCands[invNum].erase(it))
          {
            Expr c = *it;
            if (u.isTrue(c) || u.isFalse(c)) continue;

            Expr cand = sf.af.getSimplCand(c);
            if (printLog) outs () << "- - - bootstrapped cand for " << *dcl << ": " << *cand << "\n";

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
              deferredCandidates[invNum].push_back(cand);
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

      return false;
    }

    void updateGrammars()
    {
      // convert candidates to curCandidates and run the method from RndLearner
      for (int ind = 0; ind < invNumber; ind++)
      {
        if (candidates[ind].size() == 0) curCandidates[ind] = mk<TRUE>(m_efac);
        else curCandidates[ind] = conjoin(candidates[ind], m_efac);
      }
      updateRels();
      updCount++;
    }

    bool checkAllLemmas()
    {
      candidates.clear();
      for (int i = ruleManager.wtoCHCs.size() - 1; i >= 0; i--)
      {
        auto & hr = *ruleManager.wtoCHCs[i];
        boost::tribool b = checkCHC(hr, candidates);
        if (b) {
          if (!hr.isQuery)
          {
            outs() << "WARNING: Something went wrong" <<
              (ruleManager.hasArrays[hr.srcRelation] || ruleManager.hasArrays[hr.dstRelation] ?
              " (possibly, due to quantifiers)" : "") <<
              ". Restarting...\n";

            for (int i = 0; i < decls.size(); i++)
            {
              SamplFactory& sf = sfs[i].back();
              ExprSet lms = sf.learnedExprs;
              for (auto & l : lms) candidates[i].push_back(l);
            }
            multiHoudini(ruleManager.wtoCHCs);
            assignPrioritiesForLearned();

            return false;
            assert(0);    // only queries are allowed to fail
          }
          else
            return false; // TODO: use this fact somehow
        }
        else if (indeterminate(b)) return false;
      }
      return true;
    }

    boost::tribool checkCHC (HornRuleExt& hr, map<int, ExprVector>& annotations)
    {
      ExprSet exprs;
      exprs.insert(hr.body);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        ExprSet lms = sf.learnedExprs;
        for (auto & a : annotations[ind]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.srcVars[v.first]);
          exprs.insert(a);
        }
      }

      if (!hr.isQuery)
      {
        int ind = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        ExprSet lms = sf.learnedExprs;
        ExprSet negged;
        for (auto & a : annotations[ind]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.dstVars[v.first]);
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

      if (iterators[invNum] != NULL) return;    // GF: TODO more sanity checks (if needed)

      ExprSet ssa;
      if (!containsOp<ARRAY_TY>(ssas[invNum])) return; // todo: support

      getConj(ssas[invNum], ssa);

      filter (ssas[invNum], bind::IsConst (), inserter(qvars[invNum], qvars[invNum].begin()));
      postconds[invNum] = ruleManager.getPrecondition(hr);

      for (int i = 0; i < dstVars.size(); i++)
      {
        Expr a = srcVars[i];
        Expr b = dstVars[i];
        if (!bind::isIntConst(a) /*|| !contains(postconds[invNum], a)*/) continue;

        // TODO: pick one if there are multiple available
        if (u.implies(ssas[invNum], mk<GT>(a, b)))
        {
          iterators[invNum] = a;
          iterGrows[invNum] = false;
          ruleManager.iterator[rel] = i;
          break;
        }
        else if (u.implies(ssas[invNum], mk<LT>(a, b)))
        {
          iterators[invNum] = a;
          iterGrows[invNum] = true;
          ruleManager.iterator[rel] = i;
          break;
        }
      }

      ssa.clear();
      getConj(pref, ssa);
      for (auto & a : ssa)
      {
        if (contains(a, iterators[invNum]) && isOpX<EQ>(a))
        {
          preconds[invNum] = a;
          break;
        }
      }

      if (iterators[invNum] != NULL)
        ruleManager.hasArrays[rel] = true;
    }

    void simplifyLemmas()
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        u.removeRedundantConjuncts(sf.learnedExprs);
      }
    }

    void printSolution(bool simplify = true)
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        ExprSet lms = sf.learnedExprs;
        outs () << "(define-fun " << *rel << " (";
        for (auto & b : ruleManager.invVars[rel])
          outs () << "(" << *b << " " << u.varType(b) << ")";
        outs () << ") Bool\n  ";
        Expr tmp = conjoin(lms, m_efac);
        if (simplify && !containsOp<FORALL>(tmp)) u.removeRedundantConjuncts(lms);
        Expr res = simplifyArithm(conjoin(lms, m_efac));
        u.print(res);
        outs () << ")\n";
        assert(hasOnlyVars(res, ruleManager.invVars[rel]));
      }
    }
  };

  inline void learnInvariants3(string smt, unsigned maxAttempts, unsigned to, bool freqs, bool aggp,
                               bool enableDataLearning, bool doElim, bool doDisj,
                               bool dAllMbp, bool dAddProp, bool dAddDat, bool dStrenMbp)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt, doElim);
    BndExpl bnd(ruleManager);
    if (!ruleManager.hasCycles())
    {
      bnd.exploreTraces(1, ruleManager.chcs.size(), true);
      return;
    }

    RndLearnerV3 ds(m_efac, z3, ruleManager, to, freqs, aggp, dAllMbp, dAddProp, dAddDat, dStrenMbp);
    map<Expr, ExprSet> cands;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);

    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr pref = bnd.compactPrefix(i);
      Expr rel = ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation;
      ExprSet tmp;
      getConj(pref, tmp);
      for (auto & t : tmp)
        if(hasOnlyVars(t, ruleManager.invVars[rel]))
          cands[rel].insert(t);
      ds.mutateHeuristicEq(cands[rel], cands[rel], rel, true);
      ds.initializeAux(bnd, i, pref);
    }
    if (enableDataLearning) ds.getDataCandidates(cands);
    for (auto& dcl: ruleManager.wtoDecls) ds.addCandidates(dcl, cands[dcl]);
    for (auto& dcl: ruleManager.wtoDecls) ds.getSeeds(dcl, cands);
    ds.refreshCands(cands);
    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)], false);
    ds.calculateStatistics();
    if (ds.bootstrap(doDisj)) return;
    std::srand(std::time(0));
    ds.synthesize(maxAttempts, doDisj);
  }
}

#endif
