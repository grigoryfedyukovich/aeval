#ifndef TGLBEXPL__HPP__
#define TGLBEXPL__HPP__

#include "TGBndExpl.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class TGLBExpl : public TGBndExpl
  {
    protected:
    bool prio;
    bool prune;
    std::time_t tm;
    double th;
    SMTUtils u2;

    public:

    TGLBExpl (CHCs& r, int l, int t, bool p, bool u, int to, double h, bool d = false) :
      TGBndExpl(r, l, t, to, d), u2(m_efac, to), prio(p), prune(u), th(h) {
        tm = std::time(nullptr);
        std::localtime(&tm);
      }

    bool checkCovered(int tr, int c, int &tot)
    {
      auto & chc = ruleManager.chcs[c];

      if (chc.bodies.size() <= 1)
      {
        tot++;
        return true;
      }

      for (int i = 0; i < chc.bodies.size(); i++)
      {
        Expr b = chc.bodies[i];
        if (find(chc.covered.begin(), chc.covered.end(), i) == chc.covered.end())
        {
          if (!chc.isQuery)
            b = replaceAll(b, chc.dstVars, bindVars[tr]);
          if (!chc.isFact)
            b = replaceAll(b, chc.srcVars, bindVars[tr-1]);

          b = replaceAll(b, chc.locVars, bindLocVars[tr]);
          if (bool(u.eval(b)))
          {
            bodiesCnjs.push_back(chc.bodies[i]);
            chc.covered.push_back(i);
            tot++;
          }
        }
      }
      return chc.covered.size() == chc.bodies.size();
    }

    set<int> todoCHCs;
    void fillTodos()
    {
      // get points of control-flow divergence
      for (auto & d : ruleManager.decls)
        if (ruleManager.outgs[d->left()].size() > 1)
          for (auto & o : ruleManager.outgs[d->left()])
            todoCHCs.insert(o);

      // add bodies with disjs
      for (int i = 0; i < ruleManager.chcs.size(); i++)
        if (ruleManager.chcs[i].bodies.size() > 1)
          todoCHCs.insert(i);

      // if the code is straight, just add queries
      if (todoCHCs.empty())
        for (int i = 0; i < ruleManager.chcs.size(); i++)
          if (ruleManager.chcs[i].isQuery)
            todoCHCs.insert(i);
    }

    int getNumUnvis(vector<int> &g)
    {
      int n = 0;
      for (auto i : g)
        if (find(todoCHCs.begin(), todoCHCs.end(), i) != todoCHCs.end())
          n++;
      return n;
    }

    void print(vector<int> &g)
    {
      if (g.empty()) return;
      outs () << "  " << ruleManager.chcs[g[0]].srcRelation;
      for (auto f : g)
        outs () << " -> [" << f << ", " << ruleManager.chcs[f].usesKeys << "] "
                        << ruleManager.chcs[f].dstRelation << "("
                        << ruleManager.chcs[f].covered.size() << "/"
                        << ruleManager.chcs[f].bodies.size() << ")";
      outs () << "\n";
    }

    void print(set<int> &g)
    {
      if (g.empty()) return;
      for (auto f : g)
        outs () << ruleManager.chcs[f].srcRelation << " -> [" << f << ", "
                << ruleManager.chcs[f].usesKeys << "] "
                << ruleManager.chcs[f].dstRelation << "("
                << ruleManager.chcs[f].covered.size() << "/"
                << ruleManager.chcs[f].bodies.size() << ")\n";
      outs () << "\n";
    }

    void unroll(vector<int> &o, vector<vector<int>> &n1, vector<vector<int>> &n2)
    {
      for (Expr l : ruleManager.loopheads)
      {
        for (int i = o.size() - 1; i >= 0; i--)
        {
          if (ruleManager.chcs[o[i]].dstRelation == l)
          {
            vector<int> c1;
            getLastChunk(o, c1, i);

            if (compatibleConnections[c1].empty())
              compatibleConnections[c1] = ruleManager.cycles[l];

            for (auto a : compatibleConnections[c1])
            {
              assert(ruleManager.chcs[a.back()].dstRelation == l);

              if (emptCycls[a] && emptCyclsVisited[a]) continue;

              vector<int> nn = o;
              nn.insert(nn.begin() + i + 1, a.begin(), a.end());
              if (!containsWeak(traces_considered, nn))
                unique_push_back(nn, n1);
            }

            break; // experiment: exit early,
                   // because other alternatives are considered at different levels
          }
        }
      }
    }

    void pruneLast(vector<int> &a)
    {
      if (!prune) return;
      auto & lhs = ruleManager.loopheads;
      while (!a.empty())
      {
        if (find(todoCHCs.begin(), todoCHCs.end(), a.back()) == todoCHCs.end() &&
            find(lhs.begin(), lhs.end(),
                  ruleManager.chcs[a.back()].dstRelation) == lhs.end())
          a.pop_back();
        else break;
      }
    }

    bool cannotSkip(vector<int> &a, int init = 0)
    {
      auto & lhs = ruleManager.loopheads;
      for (int j = 0; j < init; j++)
      {
        if (find(lhs.begin(), lhs.end(), ruleManager.chcs[a[j]].dstRelation) != lhs.end())
        {
          bool found = false;
          for (int i = init; i < a.size(); i++)
          {
            found |= (ruleManager.chcs[a[j]].dstRelation == ruleManager.chcs[a[i]].dstRelation);
          }
          if (!found) return true;
        }
      }
      return false;
    }

    int getLHcount(vector<int> &a, int init = 0)
    {
      auto & lhs = ruleManager.loopheads;
      int c = 0;
      for (int i = init; i < a.size(); i++)
      // for (auto & v : a)
      {
        auto &v = a[i];
        if (find(lhs.begin(), lhs.end(), ruleManager.chcs[v].dstRelation)
          != lhs.end()) c++;
      }
      return c;
    }

    bool findPref(vector<int>& g, vector<vector<int>> & gs)
    {
      for (auto & h : gs)
      {
        int i, j;
        for (i = 0, j = 0; i < g.size() && j < h.size(); i++, j++)
          if (g[i] != h[i]) break;
        if (i == g.size()) return true;
      }
      return false;
    }

    int weight(int i)
    {
      if (find(todoCHCs.begin(), todoCHCs.end(), i) == todoCHCs.end())
        return 0;
      return 1;
      // TODO:  if (chc.bodies.size() > 1) return....
      // TODO: num of conjuncts
    }

    int weight(vector<int>& g)
    {
      int cur = 0;
      for (auto i : g) cur += weight(i);
      return cur;
    }

    int getNext(vector<vector<int>> & cntr, vector<vector<int>>::iterator & n)
    {
      int curMax = 0;
      for (auto it = cntr.begin(); it != cntr.end(); ++it)
      {
        int cur = weight(*it);
        if (cur > curMax)
        {
          n = it;
          curMax = cur;
        }
      }
      return curMax;
    }

    void findEmpt(vector<int>& g)
    {
      for (auto & a : emptCycls)
      {
        if (!a.second) continue;
        auto & t = a.first;
        for (int i = 0; i < g.size(); i++)
        {
          if (g[i] == t[0])
          {
            int j = 1;
            i++;
            for (; j < t.size() && i < g.size(); i++, j++)
              if (g[i] != t[j]) break;
            if (j == t.size())
            {
              emptCyclsVisited[t] = true;
            }
            break;
          }
        }
      }
    }

    void success(vector<int>& g)
    {
      int rem = todoCHCs.size();
      int tot = 0;
      for (int i = 0; i < g.size(); i++)
      {
        if (find(todoCHCs.begin(), todoCHCs.end(), g[i]) != todoCHCs.end())
          if (checkCovered(i, g[i], tot))
            todoCHCs.erase(g[i]);
      }
      if (tot > 0)
      {
        outs () << "\nNEW TEST: ";
        print(g);
        outs () << "\n\n";
        if (getTest(false)) printTest();
        findEmpt(g);
      }
      pruneLast(g);
      if (rem != todoCHCs.size())
      {
        outs () << "Rem TODOs: " << todoCHCs.size()
                << "    (sz = " << g.size() << ")" << "\n";
        outs().flush();
      }
    }

    bool addDisjContr (vector<int> & g, ExprVector& blocked)
    {
      bool hasDisj = false;
      for (int s = 0; s < g.size(); s++)
      {
        auto & chc = ruleManager.chcs[g[s]];
        if (chc.bodiesSz > 1)
        {
          ExprVector varsToDisable;
          for (int i = chc.locVars.size() - chc.bodiesSz, j = 0;
                   i < chc.locVars.size(); i++, j++)
            if (find(chc.covered.begin(), chc.covered.end(), j) !=
                                          chc.covered.end())
              varsToDisable.push_back(mk<NEG>(bindLocVars[s][i]));
            else
              hasDisj = true;

          if (!varsToDisable.empty())
            blocked.push_back(
              mk<ITE>(conjoin(varsToDisable, m_efac),
                mkMPZ(1, m_efac), mkMPZ(0, m_efac)));
        }
      }
      return hasDisj;
    }

    void oneRound(vector<vector<int>> & cntr, vector<vector<int>>& prio3)
    {
      int sz;
      int c = 0;
      int numTodos = 9999;
      while (true)
      {
        if (std::difftime(std::time(nullptr), tm) > th)
        {
          outs () << "finishing the round earlier: " << numTodos << "\n";
          return;
        }

        vector<vector<int>>::iterator git;
        numTodos = getNext(cntr, git);
        if (numTodos == 0) {
          break;
        }
        c++;

        vector<int> g = *git;
        cntr.erase(git);

        if (already_unsat(g, sz))
        {
          if (cannotSkip(g, sz))
          {
            pruneLast(g);
            unique_push_back(g, prio3); // unsat push
          }
          continue;
        }

        ExprVector ssa, blocked;
        getSSA(g, ssa);

        auto res = u.isSatIncrem(ssa, sz);

        auto h = g;
        if (true != res)
        {
          assert (sz > 0);
          h.resize(sz - 1);
          u.pop();
        }
        // else it should be SAT

        bool hasDisj = addDisjContr(h, blocked);

        int j = -1;
        if (blocked.empty())
        {
          assert (sz > 0);
          if (res == false)
          {
            u.reSolve(0);   // need to get model
          }
        }
        else
        {
          for (j = blocked.size(); j >= 0; j--)
          {
            auto res2 = u.isSat(mk<EQ>(mkMPZ(j, m_efac), mkplus(blocked, m_efac)),
                                                            false /* increm */);
            if (res2 == true) break;
            u.pop();
          }
          assert(j >= 0);
          // if j == 0 then no blocked were used.
          // SSA is still SAT
        }
        success(h);
        if (true == res)
        {
          if ((hasDisj && j == -1) || j > 0)
            unique_push_back(h, cntr);
          else
            unique_push_back(h, prio3);
        }
        else if (false == res)
        {
          if (sz > 0)
          {
            if (cannotSkip(g, sz))
            {
              outs () << "    unsat push\n";
              unique_push_back(g, prio3);   // unsat push
            }
            outs () << "    none\n";
            g.resize(sz);
            unsat_prefs.insert(g);
          }
        }
        else
        {
          if (debug) assert(0 && "indeterminate");
        }
      }

      vector<vector<int>> tmp;
      for (auto & a : cntr)
      {
        pruneLast(a);
        unique_push_back(a, tmp);
      }
      cntr = tmp;
    }

    vector<vector<int>> traces_considered;
    void exploreRec(vector<vector<int>> & traces, int lvl, string name)
    {

      outs () << "\n-----------------\nentering lvl: " << lvl << ", \"" << name << "\"\n";
      vector<vector<int>> traces_tmp, traces_prt, traces_prio, traces_unsat_cond, traces_unsat;
      if (lvl == 1000) return;
      if (lvl == 3) exit(0);

      if (std::difftime(std::time(nullptr), tm) > th) return;

      if (lvl == 0)
        traces_prt = traces;
      else
      {
        for (auto & t : traces)
        {
          pruneLast(t);
          unique_push_back(t, traces_tmp);
        }
        while (!traces_tmp.empty())
        {
          int cur_len = 0;    // find longest pref
          int cur_ind = 0;
          for (int j = 0; j < traces_tmp.size(); j++)
          {
            if (traces_tmp[j].size() > cur_len)
            {
              cur_len = traces_tmp[j].size();
              cur_ind = j;
            }
          }
          if (!findPref(traces_tmp[cur_ind], traces_prt) &&
              !findPref(traces_tmp[cur_ind], traces_unsat))
          {
            unroll(traces_tmp[cur_ind], traces_prt, traces_unsat);
          }
          traces_tmp.erase(traces_tmp.begin() + cur_ind);
        }
      }

      if (traces_prt.empty())
      {
        outs () << "exiting lvl: " << lvl << " (ingloriously)\n";
        return;
      }
      outs () << "considering " << traces_prt.size() << " traces\n";

      oneRound(traces_prt, traces_unsat);
      outs () << "  round finished: " << traces_prt.size() << " / " << traces_unsat.size() << "\n";

      for (auto & a : traces_unsat)
      {
        traces_prt.push_back(a);
      }
      if (!prio)
      {
        exploreRec(traces_prt, lvl + 1, "next");
      }
      else
      {
        for (int i = lvl + ruleManager.loopheads.size(); i >= 0; i--)
        {
          vector<vector<int>> traces_next;
          for (auto & a : traces_prt)
            if (getLHcount(a) == i)
              traces_next.push_back(a);
          exploreRec(traces_next, lvl + 1, "next_" + lexical_cast<string>(i));
        }
      }

      outs () << "exiting lvl: " << lvl << "\n";
    }


    map<Expr, map<Expr, vector<vector<int>>>> pres, posts;
    map<Expr, map<vector<int>, Expr>> post, pre;
    map<Expr, map<Expr, vector<vector<int>>>> postPre;
    map<vector<int>, Expr> ppprefs, ppsuffs;

    Expr getVal(map<vector<int>, Expr>& mp, vector<int> & t)
    {
      for (auto & a : mp)
      {
        if (a.first.size() == t.size())
        {
          bool toSkip = false;
          for (int i = 0; i < t.size(); i++)
          {
            if (a.first[i] != t[i])
            {
              toSkip = true;
              break;
            }
          }
          if (toSkip) continue;
          return a.second;
        }
      }
      return NULL;
    }

    bool containsWeak(vector < vector<int> > & vec, vector<int> & t)
    {
      for (auto & a : vec)
      {
        if (a.size() >= t.size())
        {
          bool toSkip = false;
          for (int i = 0; i < t.size(); i++)
          {
            if (a[i] != t[i])
            {
              toSkip = true;
              break;
            }
          }
          if (toSkip) continue;
          return true;
        }
      }
      return false;
    }

    int stat = 0, stat1 = 0, stat2 = 0;

    Expr getDFreeAbstr(Expr ssa)
    {
      ExprSet dsjs, cnjs;
      getDisj(ssa, dsjs);
      Expr n = distribDisjoin(dsjs, m_efac);
      getConj(n, cnjs);
      for (auto it = cnjs.begin(); it != cnjs.end();)
        if (isOpX<OR>(*it)) it = cnjs.erase(it);
        else ++it;
      return conjoin(cnjs, m_efac);
    }

    void computePrePost(vector<int> & t)
    {
      ExprVector ssa;
      getSSA(t, ssa);
      for (auto & s : ssa)
        if (qeUnsupported(s)) return;

      Expr srcRel = ruleManager.chcs[t[0]].srcRelation;
      Expr dstRel = ruleManager.chcs[t.back()].dstRelation;
      auto & srcVars = ruleManager.invVars[srcRel];
      auto & dstVars = ruleManager.invVars[dstRel];

      int sz;
      auto & lhs = ruleManager.loopheads;
      Expr p;
      ExprVector invs;

      if (!srcVars.empty())
      {
        ExprVector shortSSA;
        vector<int> shortT;

        for (int i = 0; i < t.size(); i++)
        {
          auto abstr = getDFreeAbstr(ssa[i]);
          assert((bool)u.implies(ssa[i], abstr));
          if (isOpX<TRUE>(abstr)) break;

          auto r = ruleManager.chcs[t[i]].srcRelation;
          if (r != srcRel && find(lhs.begin(), lhs.end(), r) != lhs.end())
            assert(0);

          shortT.push_back(t[i]);
          shortSSA.push_back(abstr);
        }

        p = getVal(ppprefs, shortT);
        bool alreadyGenerated = (p != NULL);
        if (alreadyGenerated)
        {
          pres[srcRel][p].push_back(t);
          pre[srcRel][t] = p;
          totsving2++;
        }
        else
        {
          p = mk<TRUE>(m_efac);
        }

        if (!alreadyGenerated)
        {
          int i, last = 0;
          int sz = shortSSA.size();
          auto tmp = shortT;
          for (i = 0; i < sz; i++)
          {
            stat1++;
            p = simplifyBool(keepQuantifiers(mk<AND>(p, shortSSA[sz - i - 1]),
                            (i == sz - 1 ? srcVars : bindVars[sz - i - 2])));

            if (isOpX<TRUE>(p))
            {
              last++;
              tmp.pop_back();
              Expr q = getVal(ppprefs, tmp);
              if (q != NULL)
              {
                alreadyGenerated = true;
                totsving++;
                p = ppprefs[tmp];
                break;
              }
            }
          }

          if (!isOpX<TRUE>(p))
          {
            if(!alreadyGenerated) stat++;
            sums1++;
          }
          pres[srcRel][p].push_back(t);
          pre[srcRel][t] = p;
          ppprefs[shortT] = p;

          tmp = shortT;
          for (int j = 0; j < last; j++)
          {
            tmp.pop_back();
            ppprefs[tmp] = p;
          }
        }

        // check if it is an invariant:
        if (srcRel == dstRel && !isOpX<TRUE>(p))
        {
          ExprSet cnjs;
          getConj(p, cnjs);
          for (auto c : cnjs)
          {
            Expr d = replaceAll(c, srcVars, bindVars.back());
            ExprVector tmp = ssa;
            tmp.push_back(mkNeg(d));

            if (false == u.isSatIncrem(tmp, sz))
              invs.push_back(c);
          }
        }
      }

      if (!dstVars.empty())
      {
        ExprVector shortSSA;
        vector<int> shortT;

        for (int i = 1; i <= t.size(); i++)
        {
          auto ind = t.size() - i;
          auto abstr = getDFreeAbstr(ssa[ind]);
          assert((bool)u.implies(ssa[ind], abstr));
          if (isOpX<TRUE>(abstr)) break;

          auto r = ruleManager.chcs[t[ind]].dstRelation;
          if (r != dstRel && find(lhs.begin(), lhs.end(), r) != lhs.end())
            assert(0);

          shortT.insert(shortT.begin(), t[ind]);
          shortSSA.insert(shortSSA.begin(), abstr);
        }

        int offset = t.size() - shortSSA.size();

        p = getVal(ppsuffs, shortT);
        bool alreadyGenerated = (p != NULL);
        if (alreadyGenerated)
        {
          invs.push_back(p);
          p = conjoin(invs, m_efac);
          totsving2++;
          posts[dstRel][p].push_back(t);
          post[dstRel][t] = p;
        }
        else
        {
          p = mk<TRUE>(m_efac);
        }

        if (!alreadyGenerated)
        {
          int i, last = 0;
          auto tmp = shortT;
          for (i = 0; i < shortSSA.size(); i++)
          {
            stat1++;
            p = simplifyBool(keepQuantifiers(mk<AND>(p, shortSSA[i]),
                                        bindVars[offset + i]));
            if (isOpX<TRUE>(p))
            {
              last++;
              tmp.erase(tmp.begin());
              auto q = getVal(ppsuffs, tmp);
              if (q != NULL)
              {
                alreadyGenerated = true;
                totsving++;
                p = q;
                break;
              }
            }
          }

          if (!alreadyGenerated)
          {
            assert(offset + i == bindVars.size());
            p = replaceAll(p, bindVars.back(), dstVars);
          }

          invs.push_back(p);
          p = conjoin(invs, m_efac);

          if (!isOpX<TRUE>(p))
          {
            if(!alreadyGenerated) stat++;
            sums2++;
          }

          posts[dstRel][p].push_back(t);
          post[dstRel][t] = p;
          ppsuffs[shortT] = p;

          tmp = shortT;
          for (int j = 0; j < last; j++)
          {
            tmp.erase(tmp.begin());
            ppsuffs[tmp] = p;
          }
        }
      }
    }

    set< vector<int> > traceChunks;

    void splitTraceToChunks(vector<int>& t, vector< vector<int> > & chunks,
                                            int i = 0, int sz = -1)
    {
      if (sz == -1) sz = t.size() - 1;
      int j = i;
      while (j <= sz)
      {
        for (Expr l : ruleManager.loopheads)
        {
          if (ruleManager.chcs[t[j]].dstRelation == l || j == sz)
          {
            vector<int> tmp;
            for (int k = i; k <= j; k++) tmp.push_back(t[k]);
            chunks.push_back(tmp);
            i = j + 1;
            break;
          }
        }
        j++;
      }
    }

    void getFirstChunk(vector<int>& t, vector<int>& c, int in = 0)
    {
      vector< vector<int> > chunks;
      splitTraceToChunks(t, chunks, in, -1);
      assert(!chunks.empty());
      c = chunks[0];
    }

    void getLastChunk(vector<int>& t, vector<int>& c, int sz = -1)
    {
      vector< vector<int> > chunks;
      splitTraceToChunks(t, chunks, 0, sz);
      assert(!chunks.empty());
      c = chunks.back();
    }

    map< vector<int>, vector < vector<int> > > compatibleConnections;

    int totsving = 0, totsving2 = 0, sums1 = 0, sums2 = 0;

    tribool findPair(map<pair<Expr, Expr>, bool>& pairs, Expr a, Expr b)
    {
      if (a == NULL || b == NULL) return true;
      if (isOpX<TRUE>(a) && !isOpX<TRUE>(b)) return true;
      if (isOpX<TRUE>(b) && !isOpX<TRUE>(a)) return true;
      for (auto & p : pairs)
        if (p.first.first == a && p.first.second == b)
          return p.second;
      return indeterminate;
    }

    map<vector<int>, bool> emptCycls, emptCyclsVisited;
    void findUselessPaths(vector<vector<int>> & init)
    {
      int sz;
      outs () << "total for global: " << init.size() << "\n";
      for (auto it = init.begin(); it != init.end(); )
      {
        auto t = *it;
        int i = 0, j = 0, sz;
        bool unsat = false;
        while (j < t.size() && !unsat)
        {
          bool lhfound = false;
          for (Expr l : ruleManager.loopheads)
          {
            if (ruleManager.chcs[t[j]].dstRelation == l || j == t.size() - 1)
            {
              vector<int> tmp;
              for (int k = i; k <= j; k++) tmp.push_back(t[k]);
              ExprVector ssa;
              getSSA(tmp, ssa);
              if (false == u2.isSatIncrem(ssa, sz)) unsat = true;
              lhfound = true;
              break;
            }
          }
          if (lhfound) i = j + 1;
          j++;
        }
        if (unsat) it = init.erase(it);
        else ++it;
      }

      outs () << "upd for global: " << init.size() << "\n";
      outs().flush();

      auto & lhs = ruleManager.loopheads;
      for (auto it1 = ruleManager.cycles.begin(); it1 != ruleManager.cycles.end();)
      {
        auto & a = *it1;
        outs () << "====\ntotal for " << a.first << ": " << a.second.size() << "\n";
        int emnum = 0;
        int remnum = 0;
        for (auto it2 = a.second.begin(); it2 != a.second.end(); )
        {
          auto & t = *it2;
          bool toSkip = false;

          for (int i = 0; i < t.size(); i++)
          {
            auto r = ruleManager.chcs[t[i]].srcRelation;
            if (r != a.first && find(lhs.begin(), lhs.end(), r) != lhs.end())
            {
              toSkip = true;
              break;
            }
          }
          if (toSkip)
          {
            ++it2;
            continue;
          }

          ExprVector ssa;
          getSSA(t, ssa);
          auto & v1 = ruleManager.chcs[t[0]].srcVars;
          auto & v2 = bindVars.back();
          assert(v1.size() == v2.size());
          ExprVector tmp;
          for (int i = 0; i < v1.size(); i++)
            tmp.push_back(mk<EQ>(v1[i], v2[i]));
          ssa.push_back(mk<NEG>(conjoin(tmp, m_efac)));

          int sz;
          auto res = u2.isSatIncrem(ssa, sz);
          if (res == false && sz != -1)
          {
            if (sz != ssa.size())
            {
              outs () << "remove cyc:\n";
              print(t);
              remnum++;
              it2 = a.second.erase(it2);
              continue;
            }
            else
            {
              outs () << "empty cyc:\n";
              print(t);
              emnum++;
              emptCycls[t] = true;
            }
          }
          it2++;
        }
        outs () << "updated number of cycles for " << a.first << ": " << a.second.size() << "\n";
        outs () << "removed cycles found: " << remnum << "\n";
        outs () << "empty cycles found: " << emnum << "\n";
        if (a.second.empty())
        {
          for (auto it3 = ruleManager.loopheads.begin(); it3 != ruleManager.loopheads.end();)
          {
            if ((*it3) == a.first)
            {
              outs () << "loophead erased: " << a.first << "\n";
              ruleManager.loopheads.erase(it3);
              break;
            }
            else ++it3;
          }
          it1 = ruleManager.cycles.erase(it1);
        }
        else
        {
          it1++;
        }
      }
    }

    void useConcreteSumms(vector< vector<int> >& chunks)
    {
      auto & lhs = ruleManager.loopheads;
      int sz;
      Expr l = NULL;
      for (auto it = lhs.begin(); it != lhs.end(); ++it)
      {
        bool allEmpty = false;
        for (auto & c : ruleManager.cycles[*it])
          if (emptCycls[c]) allEmpty = true;
        if (allEmpty) continue;
        assert(l == NULL);
        l = *it;
      }
      assert(l != NULL);
      // outs () << "   proceed with loophead " << l << "\n";
      set< vector<int> > tmpChunks;
      for (auto & a : chunks)
      {
        bool found = false;
        for (auto & b : tmpChunks)
        {
          bool eq = true;
          if (a.size() == b.size())
          {
            for (int j = 0; j < a.size(); j++)
            {
              if (a[j] != b[j])
              {
                eq = false;
                break;
              }
            }
          }
          else eq = false;
          if (eq)
          {
            found = true;
            break;
          }
        }
        if (!found)
          tmpChunks.insert(a);
      }

      map<int, ExprSet> vars;
      for (int k = 0; k < ruleManager.invVars[l].size(); k++)
      {
        ExprSet vall;
        bool tooMany = false;
        for (auto c : tmpChunks)
        {
          Expr rel1 = ruleManager.chcs[c[0]].srcRelation;
          Expr rel2 = ruleManager.chcs[c.back()].dstRelation;
          if (!(rel1 != l && rel2 == l)) continue;

          ExprVector ssa;
          getSSA(c, ssa);
          int i;
          for (i = 0; i < 10; i++)
          {
            if (u2.isSatIncrem(ssa, sz))
            {
              Expr val = u2.getModel(bindVars.back()[k]);
              ssa.push_back(mk<NEQ>(bindVars.back()[k], val));
              vall.insert(val);
            }
            else break;
          }
          if (i == 10)
          {
            tooMany = true;
            break;
          }
        }
        if (!tooMany)
        {
          vars[k] = vall;
        }
      }

      int compat = 0, incompat = 0;

      ExprVector pvars;
      for (auto & g : vars)
      {
        Expr var = ruleManager.invVars[l][g.first];

        ExprVector tl;
        for (auto & h : g.second) tl.push_back(mk<EQ>(var, h));
        pvars.push_back(disjoin(tl, m_efac));
      }

      Expr mpost = conjoin(pvars, m_efac);
      for (auto cyc : ruleManager.cycles[l])
      {
        ExprVector ssa;
        getSSA(cyc, ssa);

        ExprVector ssat = ssa;
        ssat.push_back(mpost);

        if (u2.isSatIncrem(ssat, sz))
        {
          compat++;
          for (auto c1 : tmpChunks)
          {
            Expr rel1 = ruleManager.chcs[c1[0]].srcRelation;
            Expr rel2 = ruleManager.chcs[c1.back()].dstRelation;
            if (rel1 != l && rel2 == l)
            {
              compatibleConnections[c1].push_back(cyc);
            }
          }
        }

        ExprVector sums;
        for (auto & g : vars)
        {
          Expr var = ruleManager.invVars[l][g.first];
          Expr varPr = bindVars.back()[g.first];

          int i;
          ExprVector tmp;
          for (i = 0; i < 10; i++)
          {
            if (u2.isSatIncrem(ssa, sz))
            {
              Expr newVal = u2.getModel(varPr);
              ssa.push_back(mk<NEQ>(varPr, newVal));
              tmp.push_back(mk<EQ>(var, newVal));
            }
            else break;
          }
          if (i == 10) continue; // hardcoded bound

          outs () << "finite possible vals of #" << g.first << "\n";
          sums.push_back(disjoin(tmp, m_efac));
        }

        if (sums.empty()) continue;
        Expr sum = conjoin(sums, m_efac);

        for (auto cyc2 : ruleManager.cycles[l])
        {
          ExprVector ssa2;
          getSSA(cyc2, ssa2);
          ssa2.push_back(sum);

          if (u2.isSatIncrem(ssa2, sz))
          {
            compat++;
            compatibleConnections[cyc].push_back(cyc2);
          }
          else
            incompat++;
        }
      }

      outs () << "(in)compatible connections: " << incompat << " / " << compat << "\n";
    }

    void getPrePostConds(vector<vector<int>> & init)
    {
      vector< vector<int> > chunks;
      for (auto & tr : init)
        splitTraceToChunks(tr, chunks);

      if (lookahead == 1)   // specific for FSM-like benchmarks
      {
        useConcreteSumms(chunks);
        return;
      }

      for (auto & a : ruleManager.cycles)
        for (auto & tr : a.second)
          if (!emptCycls[tr])
            splitTraceToChunks(tr, chunks);

      for (auto & a : chunks)
      {
        bool found = false;
        for (auto & b : traceChunks)
        {
          bool eq = true;
          if (a.size() == b.size())
          {
            for (int j = 0; j < a.size(); j++)
            {
              if (a[j] != b[j])
              {
                eq = false;
                break;
              }
            }
          }
          else eq = false;
          if (eq)
          {
            found = true;
            break;
          }
        }
        if (!found)
          traceChunks.insert(a);
      }

      outs () << "total number of chunks: " << traceChunks.size() << "\n";

      if (lookahead > 0)
        for (auto c : traceChunks)
          computePrePost(c);

      outs () << "total num of sums: " << sums1 <<" / " << sums2 << "\n";
      outs () << "QE/SMT calls during summarization: " << stat1 << " / " << stat2 << "\n";
      outs () << "total savings: " << totsving <<" / " << totsving2 << "\n";

      int tot = 0, tot2 = 0;
      map<pair<Expr, Expr>, bool> incomps;

      for (auto c1 : traceChunks)
      {
        auto lh = ruleManager.chcs[c1.back()].dstRelation;

        for (auto & tr : ruleManager.cycles[lh])
        {
          vector<int> c2;
          getFirstChunk(tr, c2);
          auto f = findPair(incomps, post[lh][c1], pre[lh][c2]);
          if (indeterminate(f))
          {
            if (true == u2.isSat(post[lh][c1], pre[lh][c2]))
            {
              compatibleConnections[c1].push_back(tr);
              incomps[ {post[lh][c1], pre[lh][c2]} ] = true;
            }
            else
            {
              incomps[ {post[lh][c1], pre[lh][c2]} ] = false;
              tot++;
            }
          }
          else if (f == true)
            compatibleConnections[c1].push_back(tr);
          else
            tot++;
        }
        tot2 += compatibleConnections[c1].size();
      }

      outs () << "(in)compatible connections: " << tot << " / " << tot2 << "\n";
    }

    void exploreTracesMaxLb(vector<vector<int>> & init)
    {
      outs () << "LB-MAX\n";
      fillTodos();
      outs () << "Total TODOs: " << todoCHCs.size() << "\n";

      findUselessPaths(init);
      getPrePostConds(init);
      exploreRec(init, 0, "init");
    }

    // original version; similar to TACAS'22
    void exploreTracesLBTG(int cur_bnd, int bnd)
    {
      outs () << "exploreTracesLBTG\n";
      fillTodos();

      while (cur_bnd <= bnd && !todoCHCs.empty())
      {
        outs () << "new iter with cur_bnd = "<< cur_bnd <<"\n";
        set<int> toErCHCs;
        for (auto & a : todoCHCs)
        {
          if (find(toErCHCs.begin(), toErCHCs.end(), a) != toErCHCs.end())
            continue;
          vector<vector<int>> traces;
          getAllTracesTG(mk<TRUE>(m_efac), a, cur_bnd, vector<int>(), traces);
          outs () << "  exploring traces (" << traces.size() << ") of length "
                  << cur_bnd << ";       # of todos = "
                  << (todoCHCs.size() - toErCHCs.size()) << "\n";

          int tot = 0;
          bool toBreak = false;
          for (int trNum = 0; trNum < traces.size() && !todoCHCs.empty() && !toBreak; )
          {
            auto & t = traces[trNum];
            set<int> apps;
            for (int i = 0; i < t.size(); i++)
              if (find(todoCHCs.begin(), todoCHCs.end(), t[i]) != todoCHCs.end() &&
                  find(toErCHCs.begin(), toErCHCs.end(), t[i]) == toErCHCs.end())
                apps.insert(i);
            if (apps.empty())
            {
              trNum++;
              continue;  // should not happen
            }
            tot++;

            auto & hr = ruleManager.chcs[t.back()];
            Expr lms = invs[hr.srcRelation];
            if (lms != NULL && (bool)u.isFalse(mk<AND>(lms, hr.body)))
            {
              outs () << "\n    unreachable: " << t.back() << "\n";
              toErCHCs.insert(t.back());
              unreach_chcs.insert(t.back());
              unsat_prefs.insert(t);
              trNum++;
              continue;
            }

            if (bool(u.isSat(toExpr(t))))
            {
              bodiesCnjs.clear();
              int tot = 0;
              for (auto & b : apps)
                if (checkCovered(b, t[b], tot))
                {
                  toErCHCs.insert(t[b]);
                  if (b == t.size() - 1)
                    toBreak = true;
                }
              if (tot > 0)
                if (getTest()) printTest();
            }
            else
            {
              if (ruleManager.chcs[t.back()].bodies.size() <= 1 ||
                  ruleManager.chcs[t.back()].covered.size() == 0)
                unsat_prefs.insert(t);
              trNum++;
            }
          }
          outs () << "    -> actually explored:  " << tot << ", |unsat prefs| = " << unsat_prefs.size() << "\n";
        }
        for (auto a : toErCHCs) todoCHCs.erase(a);
        cur_bnd++;
      }
      outs () << "Done with LBTG\n";
    }
  };
}

#endif
