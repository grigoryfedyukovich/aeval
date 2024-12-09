#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "Horn.hpp"
#include "Distribution.hpp"
#include "ae/AeValSolver.hpp"
#include <limits>

using namespace std;
using namespace boost;
namespace ufo
{
  class BndExpl
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;
    Expr extraLemmas;

    ExprVector bindVars1;

    int tr_ind; // helper vars
    int pr_ind;
    int k_ind;

    Expr inv;   // 1-inductive proof

    bool debug;

    public:

    BndExpl (CHCs& r, bool d = false) :
      m_efac(r.m_efac), ruleManager(r), u(m_efac), debug(d) {}

    BndExpl (CHCs& r, Expr lms, bool d = false) :
      m_efac(r.m_efac), ruleManager(r), u(m_efac), extraLemmas(lms), debug(d) {}

    map<Expr, ExprSet> concrInvs;

    void guessRandomTrace(vector<int>& trace)
    {
      std::srand(std::time(0));
      Expr curRel = mk<TRUE>(m_efac);

      while (curRel != ruleManager.failDecl)
      {
        int range = ruleManager.outgs[curRel].size();
        int chosen = guessUniformly(range);
        int chcId = ruleManager.outgs[curRel][chosen];
        curRel = ruleManager.chcs[chcId].dstRelation;
        trace.push_back(chcId);
      }
    }

    void getAllTraces (Expr src, Expr dst, int len, vector<int> trace, vector<vector<int>>& traces)
    {
      if (len == 1)
      {
        for (auto a : ruleManager.outgs[src])
        {
          if (ruleManager.chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : ruleManager.outgs[src])
        {
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(ruleManager.chcs[a].dstRelation, dst, len-1, newtrace, traces);
        }
      }
    }

    Expr compactPrefix (int num)
    {
      vector<int>& pr = ruleManager.prefixes[num];
      if (pr.size() == 0) return mk<TRUE>(m_efac);

      ExprVector ssa;
      getSSA(pr, ssa);
      while (!(bool)u.isSat(ssa)) ssa.erase(ssa.begin());
      Expr pref = conjoin(ssa, m_efac);
      pref = rewriteSelectStore(pref);
      pref = keepQuantifiersRepl(pref, bindVars.back());
      return replaceAll(pref, bindVars.back(), ruleManager.chcs[ruleManager.cycles[num][0]].srcVars);
    }

    vector<ExprVector> bindVars;

    Expr toExpr(vector<int>& trace)
    {
      ExprVector ssa;
      getSSA(trace, ssa);
      return conjoin(ssa, m_efac);
    }

    void getSSA(vector<int>& trace, ExprVector& ssa)
    {
      ExprVector bindVars2;
      bindVars.clear();
      ExprVector bindVars1 = ruleManager.chcs[trace[0]].srcVars;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int s = 0; s < trace.size(); s++)
      {
        auto &step = trace[s];
        bindVars2.clear();
        HornRuleExt& hr = ruleManager.chcs[step];
        Expr body = hr.body;
        if (!hr.isFact && extraLemmas != NULL) body = mk<AND>(extraLemmas, body);

        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          body = replaceAll(body, hr.srcVars[i], bindVars1[i]);
        }

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          bool kept = false;
          for (int j = 0; j < hr.srcVars.size(); j++)
          {
            if (hr.dstVars[i] == hr.srcVars[j])
            {
              bindVars2.push_back(bindVars1[i]);
              kept = true;
            }
          }
          if (!kept)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr.dstVars[i],new_name));
          }

          body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
        }

        for (int i = 0; i < hr.locVars.size(); i++)
        {
          Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
          Expr var = cloneVar(hr.locVars[i], new_name);

          body = replaceAll(body, hr.locVars[i], var);
        }

        ssa.push_back(body);
        bindVars.push_back(bindVars2);
        bindVars1 = bindVars2;
      }
    }

    bool exploreTraces(int cur_bnd, int bnd, bool print = false)
    {
      bool unsat = true;
      int num_traces = 0;

      while (unsat && cur_bnd <= bnd)
      {
        vector<vector<int>> traces;
        vector<int> empttrace;

        getAllTraces(mk<TRUE>(m_efac), ruleManager.failDecl, cur_bnd++, vector<int>(), traces);

        for (auto &a : traces)
        {
          num_traces++;
          unsat = bool(!u.isSat(toExpr(a)));
          if (!unsat) break;
        }
      }

      if (print)
      {
        if (unsat)
          outs () << "Success after complete unrolling (" << (cur_bnd - 1)<< " step)\n";
        else
          outs () << "Counterexample of length " << (cur_bnd - 1) << " found\n";
      }
      return unsat;
    }

    Expr getCexInputs(ExprVector& vars)
    {
      Expr cex = u.getModel(bindVars[0]);
      for (int i = 0; i < bindVars[0].size(); i++)
        cex = replaceAll(cex, bindVars[0][i], vars[i]);
      return cex;
    }

    bool kIndIterBase(int bnd1, int bnd2)
    {
      assert (bnd1 <= bnd2);
      assert (bnd2 > 1);
      return exploreTraces(bnd1, bnd2);
    }

    bool kIndIter(int bnd1, int bnd2)
    {
      assert (bnd1 <= bnd2);
      assert (bnd2 > 1);
      bool init = exploreTraces(bnd1, bnd2);
      if (!init)
      {
        outs() << "Base check failed at step " << bnd2 << "\n";
        exit(0);
      }

      k_ind = ruleManager.chcs.size(); // == 3

      for (int i = 0; i < k_ind; i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
      }

      ruleManager.chcs.push_back(HornRuleExt());   // trick for now: a new artificial CHC
      HornRuleExt& hr = ruleManager.chcs[k_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      hr.srcVars = tr.srcVars;
      hr.dstVars = tr.dstVars;
      hr.locVars = tr.locVars;

      hr.body = mk<AND>(tr.body, mkNeg(pr.body));

      if (extraLemmas != NULL) hr.body = mk<AND>(extraLemmas, hr.body);

      for (int i = 0; i < hr.srcVars.size(); i++)
      {
        hr.body = replaceAll(hr.body, pr.srcVars[i], hr.srcVars[i]);
      }

      vector<int> gen_trace;
      for (int i = 1; i < bnd2; i++) gen_trace.push_back(k_ind);
      gen_trace.push_back(pr_ind);
      Expr q = toExpr(gen_trace);
      bool res = bool(!u.isSat(q));

      if (bnd2 == 2) inv = mkNeg(pr.body);

      // prepare for the next iteration
      ruleManager.chcs.erase (ruleManager.chcs.begin() + k_ind);

      return res;
    }

    Expr getInv() { return inv; }

    Expr getBoundedItp(int k)
    {
      assert(k >= 0);

      int fc_ind;
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
        if (r.isFact) fc_ind = i;
      }

      HornRuleExt& fc = ruleManager.chcs[fc_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      Expr prop = pr.body;
      Expr init = fc.body;
      for (int i = 0; i < tr.srcVars.size(); i++)
      {
        init = replaceAll(init, tr.dstVars[i],  tr.srcVars[i]);
      }

      Expr itp;

      if (k == 0)
      {
        itp = getItp(init, prop);
      }
      else
      {
        vector<int> trace;
        for (int i = 0; i < k; i++) trace.push_back(tr_ind);

        Expr unr = toExpr(trace);
        for (int i = 0; i < pr.srcVars.size(); i++)
        {
          prop = replaceAll(prop, pr.srcVars[i], bindVars.back()[i]);
        }
        itp = getItp(unr, prop);
        if (itp != NULL)
        {
          for (int i = 0; i < pr.srcVars.size(); i++)
          {
            itp = replaceAll(itp, bindVars.back()[i], pr.srcVars[i]);
          }
        }
        else
        {
          itp = getItp(init, mk<AND>(unr, prop));
        }
      }
      return itp;
    }

    void fillVars(Expr srcRel, ExprVector vars, int l, int s, vector<int>& mainInds, vector<int>& arrInds, vector<ExprVector>& versVars, ExprSet& allVars)
    {
      for (int l1 = l; l1 < bindVars.size(); l1 = l1 + s)
      {
        ExprVector vers;
        int ai = 0;

        for (int i = 0; i < vars.size(); i++) {
          int var = mainInds[i];
          Expr bvar;
          if (var >= 0)
          {
            if (ruleManager.hasArrays[srcRel])
              bvar = bindVars[l1-1][var];
            else
              bvar = bindVars[l1][var];
          }
          else
          {
            bvar = mk<SELECT>(bindVars[l1][arrInds[ai]], bindVars[l1 - 1][-1 * var - 1]);
            allVars.insert(bindVars[l1][arrInds[ai]]);
            ai++;
          }
          vers.push_back(bvar);
        }
        versVars.push_back(vers);
        allVars.insert(vers.begin(), vers.end());
      }
    }

    void getOptimConstr(vector<ExprVector>& versVars, int vs, ExprVector& diseqs)
    {
      for (auto v : versVars)
        for (int i = 0; i < v.size(); i++)
          for (int j = i + 1; j < v.size(); j++)
            diseqs.push_back(mk<ITE>(mk<NEQ>(v[i], v[j]), mkMPZ(1, m_efac), mkMPZ(0, m_efac)));

      for (int i = 0; i < vs; i++)
        for (int j = 0; j < versVars.size(); j++)
          for (int k = j + 1; k < versVars.size(); k++)
            diseqs.push_back(mk<ITE>(mk<NEQ>(versVars[j][i], versVars[k][i]), mkMPZ(1, m_efac), mkMPZ(0, m_efac)));
    }

    // used for a loop and a splitter
    bool unrollAndExecuteSplitter(
          Expr srcRel,
          ExprVector& srcVars,
				  vector<vector<double> >& models,
          Expr splitter, Expr invs, int k = 10)
    {
      assert (splitter != NULL);

      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      for (int cyc = 0; cyc < ruleManager.cycles.size(); cyc++)
      {
        vector<int> mainInds;
        vector<int> arrInds;
        auto & loop = ruleManager.cycles[cyc];
        if (srcRel != ruleManager.chcs[loop[0]].srcRelation) continue;
        if (models.size() > 0) continue;

        ExprVector vars;
        for (int i = 0; i < ruleManager.chcs[loop[0]].srcVars.size(); i++)
        {
          Expr var = ruleManager.chcs[loop[0]].srcVars[i];
          if (bind::isIntConst(var))
          {
            mainInds.push_back(i);
            vars.push_back(var);
          }
          else if (isConst<ARRAY_TY> (var) && ruleManager.hasArrays[srcRel])
          {
            for (auto it : ruleManager.iterators[srcRel])
            {
              vars.push_back(mk<SELECT>(var, ruleManager.chcs[loop[0]].srcVars[it]));
              mainInds.push_back(-1 * it - 1); // to be on the negative side
              arrInds.push_back(i);
            }
          }
        }

        if (vars.size() < 2 && cyc == ruleManager.cycles.size() - 1)
          continue; // does not make much sense to run with only one var when it is the last cycle
        srcVars = vars;

        auto & prefix = ruleManager.prefixes[cyc];
        vector<int> trace;
        int l = 0;                              // starting index (before the loop)
        if (ruleManager.hasArrays[srcRel]) l++; // first iter is usually useless

        for (int j = 0; j < k; j++)
          for (int m = 0; m < loop.size(); m++)
            trace.push_back(loop[m]);

        ExprVector ssa;
        getSSA(trace, ssa);
        ssa.push_back(mk<AND>(mkNeg(splitter),
                  replaceAll(invs, ruleManager.chcs[loop.back()].dstVars, bindVars[loop.size() - 1])));
        ssa.push_back(
                  replaceAll(splitter, ruleManager.chcs[loop[0]].srcVars, bindVars[loop.size() - 1]));
        bindVars.pop_back();
        int traceSz = trace.size();

        // compute vars for opt constraint
        vector<ExprVector> versVars;
        ExprSet allVars;
        ExprVector diseqs;
        fillVars(srcRel, vars, l, loop.size(), mainInds, arrInds, versVars, allVars);
        getOptimConstr(versVars, vars.size(), diseqs);

        Expr cntvar = bind::intConst(mkTerm<string> ("_FH_cnt", m_efac));
        allVars.insert(cntvar);
        allVars.insert(bindVars.back().begin(), bindVars.back().end());
        ssa.push_back(mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

        auto res = u.isSat(ssa);
        if (indeterminate(res) || !res)
        {
          if (debug) outs () << "Unable to solve the BMC formula for " <<  srcRel << " and splitter " << splitter <<"\n";
          continue;
        }
        ExprMap allModels;
        u.getOptModel<GT>(allVars, allModels, cntvar);

        ExprSet splitterVars;
        set<int> splitterVarsIndex; // Get splitter vars here
        filter(splitter, bind::IsConst(), inserter(splitterVars, splitterVars.begin()));
        for (auto & a : splitterVars)
          splitterVarsIndex.insert(getVarIndex(a, ruleManager.chcs[loop[0]].srcVars));

        if (debug) outs () << "\nUnroll and execute the cycle for " <<  srcRel << " and splitter " << splitter <<"\n";
        for (int j = 0; j < versVars.size(); j++)
        {
          vector<double> model;
          if (debug) outs () << "  model for " << j << ": [";
          bool toSkip = false;
          SMTUtils u2(m_efac);
          ExprSet equalities;

          for (auto i: splitterVarsIndex)
          {
            Expr srcVar = ruleManager.chcs[loop[0]].srcVars[i];
            Expr bvar = versVars[j][i];
            if (isOpX<SELECT>(bvar)) bvar = bvar->left();
            Expr m = allModels[bvar];
            if (m == NULL) { toSkip = true; break; }
            equalities.insert(mk<EQ>(srcVar, m));
          }
          if (toSkip) continue;
          equalities.insert(splitter);

          if (u2.isSat(equalities)) //exclude models that don't satisfy splitter
          {
            vector<double> model;

            for (int i = 0; i < vars.size(); i++) {
              Expr bvar = versVars[j][i];
              Expr m = allModels[bvar];
              double value;
              if (m != NULL && isOpX<MPZ>(m))
              {
                if (lexical_cast<cpp_int>(m) > max_double ||
                    lexical_cast<cpp_int>(m) < -max_double)
                {
                  toSkip = true;
                  break;
                }
                value = lexical_cast<double>(m);
              }
              else
              {
                toSkip = true;
                break;
              }
              model.push_back(value);
              if (debug) outs () << *bvar << " = " << *m << ", ";
              if (j == 0)
              {
                if (isOpX<SELECT>(bvar))
                  concrInvs[srcRel].insert(mk<EQ>(vars[i]->left(), allModels[bvar->left()]));
                else
                  concrInvs[srcRel].insert(mk<EQ>(vars[i], m));
              }
            }
            if (!toSkip) models.push_back(model);
          }
          else
          {
            if (debug) outs () << "   <  skipping  >      ";
          }
          if (debug) outs () << "\b\b]\n";
        }
      }

      return true;
    }

    //used for multiple loops to unroll inductive clauses k times and collect corresponding models
    bool unrollAndExecuteMultiple(
          map<Expr, ExprVector>& srcVars,
				  map<Expr, vector<vector<double> > > & models, int k = 10)
    {
      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      map<int, bool> chcsConsidered;
      map<int, Expr> exprModels;

      for (int cyc = 0; cyc < ruleManager.cycles.size(); cyc++)
      {
        vector<int> mainInds;
        vector<int> arrInds;
        auto & loop = ruleManager.cycles[cyc];
        Expr srcRel = ruleManager.chcs[loop[0]].srcRelation;
        if (models[srcRel].size() > 0) continue;

        ExprVector vars;
        for (int i = 0; i < ruleManager.chcs[loop[0]].srcVars.size(); i++)
        {
          Expr var = ruleManager.chcs[loop[0]].srcVars[i];
          if (bind::isIntConst(var))
          {
            mainInds.push_back(i);
            vars.push_back(var);
          }
          else if (isConst<ARRAY_TY> (var) && ruleManager.hasArrays[srcRel])
          {
            for (auto it : ruleManager.iterators[srcRel])
            {
              vars.push_back(mk<SELECT>(var, ruleManager.chcs[loop[0]].srcVars[it]));
              mainInds.push_back(-1 * it - 1);  // to be on the negative side
              arrInds.push_back(i);
            }
          }
        }

        if (vars.size() < 2 && cyc == ruleManager.cycles.size() - 1)
          continue; // does not make much sense to run with only one var when it is the last cycle
        srcVars[srcRel] = vars;

        auto & prefix = ruleManager.prefixes[cyc];
        vector<int> trace;
        Expr lastModel = mk<TRUE>(m_efac);

        for (int p = 0; p < prefix.size(); p++)
        {
          if (chcsConsidered[prefix[p]] == true)
          {
            Expr lastModelTmp = exprModels[prefix[p]];
            if (lastModelTmp != NULL) lastModel = lastModelTmp;
            trace.clear(); // to avoid CHCs at the beginning
          }
          trace.push_back(prefix[p]);
        }

        int l = trace.size() - 1; // starting index (before the loop)
        if (ruleManager.hasArrays[srcRel]) l++; // first iter is usually useless

        for (int j = 0; j < k; j++)
          for (int m = 0; m < loop.size(); m++)
            trace.push_back(loop[m]);

        int backCHC = -1;
        for (int i = 0; i < ruleManager.chcs.size(); i++)
        {
          auto & r = ruleManager.chcs[i];
          if (i != loop[0] && !r.isQuery && r.srcRelation == srcRel)
          {
            backCHC = i;
            chcsConsidered[i] = true; // entry condition for the next loop
            trace.push_back(i);
            break;
          }
        }

        ExprVector ssa;
        getSSA(trace, ssa);
        bindVars.pop_back();
        int traceSz = trace.size();

        // compute vars for opt constraint
        vector<ExprVector> versVars;
        ExprSet allVars;
        ExprVector diseqs;
        fillVars(srcRel, vars, l, loop.size(), mainInds, arrInds, versVars, allVars);
        getOptimConstr(versVars, vars.size(), diseqs);

        Expr cntvar = bind::intConst(mkTerm<string> ("_FH_cnt", m_efac));
        allVars.insert(cntvar);
        allVars.insert(bindVars.back().begin(), bindVars.back().end());
        ssa.insert(ssa.begin(), mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

        bool toContinue = false;
        bool noopt = false;
        while (true)
        {
          if (ssa.size() - loop.size() < 2)
          {
            if (debug) outs () << "Unable to find a suitable unrolling for " << *srcRel << "\n";
            toContinue = true;
            break;
          }

          if (u.isSat(lastModel, conjoin(ssa, m_efac)))
          {
            if (backCHC != -1 && trace.back() != backCHC &&
                trace.size() != traceSz - 1) // finalizing the unrolling (exit CHC)
            {
              trace.push_back(backCHC);
              ssa.clear();                   // encode from scratch
              getSSA(trace, ssa);
              bindVars.pop_back();
              noopt = true;   // TODO: support optimization queries
            }
            else break;
          }
          else
          {
            noopt = true;      // TODO: support
            if (trace.size() == traceSz)
            {
              trace.pop_back();
              ssa.pop_back();
              bindVars.pop_back();
            }
            else
            {
              trace.resize(trace.size()-loop.size());
              ssa.resize(ssa.size()-loop.size());
              bindVars.resize(bindVars.size()-loop.size());
            }
          }
        }

        if (toContinue) continue;
        map<int, ExprSet> ms;

        ExprMap allModels;
        if (noopt)
          u.getModel(allVars, allModels);
        else
          u.getOptModel<GT>(allVars, allModels, cntvar);

        if (debug) outs () << "\nUnroll and execute the cycle for " <<  srcRel << "\n";
        for (int j = 0; j < versVars.size(); j++)
        {
          vector<double> model;
          bool toSkip = false;
          if (debug) outs () << "  model for " << j << ": [";

          for (int i = 0; i < vars.size(); i++) {
            Expr bvar = versVars[j][i];
            Expr m = allModels[bvar];
            double value;
            if (m != NULL && isOpX<MPZ>(m))
            {
              if (lexical_cast<cpp_int>(m) > max_double ||
                  lexical_cast<cpp_int>(m) < -max_double)
              {
                toSkip = true;
                break;
              }
              value = lexical_cast<double>(m);
            }
            else
            {
              toSkip = true;
              break;
            }
            model.push_back(value);
            if (debug) outs () << *bvar << " = " << *m << ", ";
            if (!containsOp<ARRAY_TY>(bvar))
              ms[i].insert(mk<EQ>(vars[i], m));
          }
          if (toSkip)
          {
            if (debug) outs () << "\b\b   <  skipping  >      ]\n";
          }
          else
          {
            models[srcRel].push_back(model);
            if (debug) outs () << "\b\b]\n";
          }
        }

        for (auto & a : ms)
          concrInvs[srcRel].insert(simplifyArithm(disjoin(a.second, m_efac)));

        // although we care only about integer variables for the matrix above,
        // we still keep the entire model to bootstrap the model generation for the next loop
        if (chcsConsidered[trace.back()])
        {
          ExprSet mdls;
          for (auto & a : bindVars.back())
            if (allModels[a] != NULL)
              mdls.insert(mk<EQ>(a, allModels[a]));
          exprModels[trace.back()] = replaceAll(conjoin(mdls, m_efac),
            bindVars.back(), ruleManager.chcs[trace.back()].srcVars);
        }
      }

      return true;
    }
  };

  inline void unrollAndCheck(string smt, int bnd1, int bnd2)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BndExpl ds(ruleManager, false);
    ds.exploreTraces(bnd1, bnd2, true);
  };

  inline bool kInduction(CHCs& ruleManager, int bnd)
  {
    if (ruleManager.chcs.size() != 3)
    {
      outs () << "currently not supported\n";
      return false;
    }

    BndExpl ds(ruleManager, false);

    bool success = false;
    int i;
    for (i = 2; i < bnd; i++)
    {
      if (ds.kIndIter(i, i))
      {
        success = true;
        break;
      }
    }

    outs () << "\n" <<
      (success ? "K-induction succeeded " : "Unknown result ") <<
      "after " << (i-1) << " iterations\n";

    return success;
  };

  inline void kInduction(string smt, int bnd)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    kInduction(ruleManager, bnd);
  };
}

#endif
