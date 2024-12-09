#ifndef BOOLCOM__HPP__
#define BOOLCOM__HPP__

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  // adapted and restricted LinCom.hpp for Booleans (to be extended)

  typedef vector <int> boolcoms;

  struct Bterm
  {
    bool neg;
    int var;
  };

  inline bool operator== (const Bterm& a, const Bterm& b)
  {
    if (a.neg != b.neg) return false;
    if (a.var != b.var) return false;

    return true;
  }

  inline bool operator< (const Bterm& a, const Bterm& b)
  {
    return (a.var < b.var);
  }

  class Bdisj
  {
    public:

    int arity = 0;
    vector<Bterm> dstate;    // i.e., disjunctive-state

    Bdisj(){}

    bool empty()
    {
      return arity == 0;
    }

    void addDisj(Bterm& s)
    {
      arity++;
      dstate.push_back(s);
    }

    void normalizeOr()
    {
      std::sort(dstate.begin(), dstate.end());
    }
  };

  class Bfactory
  {
    private:

    ExprFactory &m_efac;
    ExprVector vars;
    vector<Bdisj> samples;
    vector<int> varInds;

    public:

    // set of fields related to guessing:

    density orAritiesDensity;
    map<int, map<int, density>> negDensity;
    map<int, map<int, density>> negDensityTmp; // for reinit
    map<int, density> varDensity;
    vector<vector<set<int>>> varCombinations;

    Bfactory(ExprFactory &_efac) : m_efac(_efac) {};

    void addVar(Expr var)
    {
      vars.push_back(var);
    }

    void initialize()
    {
      for (int i = 0; i < vars.size(); i++)
      {
        varInds.push_back(i);
      }
    }

    ExprVector& getVars()
    {
      return vars;
    }
    
    int getVar(int ind)
    {
      return varInds[ind];
    }

    Expr toExpr (Bterm& s)
    {
      Expr var = vars [s.var];
      if (s.neg) return mk<NEG>(var);
        else return var;
    }

    Expr toExpr (Bdisj& curCandCode)
    {
      int ar = curCandCode.arity;

      ExprSet dsj;
      for (int i = 0; i < ar; i++)
      {
        dsj.insert(toExpr (curCandCode.dstate[i]));
      }
      return disjoin(dsj, m_efac);
    }

    void exprToBdisj(Expr ex, Bdisj& sample)
    {
      if (isOpX<OR>(ex))
      {
        for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
          exprToBdisj(*it, sample);
      }
      else if (isOpX<NEG>(ex))
      {
        Bterm s;
        s.neg = true;
        s.var = getVarIndex(ex->arg(0), vars);
        if (s.var >= 0) addDisjFilter(s, sample);
      }
      else if (bind::isBoolConst(ex))
      {
        Bterm s;
        s.neg = false;
        s.var = getVarIndex(ex, vars);
        if (s.var >= 0) addDisjFilter(s, sample);
      }
    }

    bool addDisjFilter(Bterm& s, Bdisj& d)
    {
      int skip = false;
      for (int j = 0; j < d.arity; j++)
      {
        Bterm& t = d.dstate[j];
        if (t.var == s.var)
        {
          skip = true;
          break;
        }
      }
      if (!skip)
      {
        d.addDisj(s);
      }
      return true;
    }

    bool guessTerm (Bdisj& curTerm)
    {
      int arity = chooseByWeight(orAritiesDensity);

      vector<Bterm> terms;

      int c = chooseByWeight(varDensity[arity]);
      if (isEmpty(negDensity[arity][c]))
      {
        negDensity[arity][c] = negDensityTmp[arity][c];      // simple reinitialization
        return guessTerm(curTerm);
      }

      // guess a combination of variables:
      vector<set<int>>& varCombination = varCombinations[arity];
      set<int>& comb = varCombination[c];

      int n = chooseByWeight(negDensity[arity][c]);
      for (int i : comb)
      {
        terms.push_back(Bterm());
        Bterm& b = terms.back();
        b.var = i;
        if (n > 0)
        {
          b.neg = n & 1;
          n = n >> 1;
        }
        else
        {
          b.neg = 0;
        }

        curTerm.addDisj(b);
      }
      return true;
    }

    void initDensities()
    {
      // preparing var combinations;
      varCombinations.push_back(vector<set<int>>());     // empty ones; not used
      for (int ar = 1; ar <= vars.size(); ar++)
      {
        varCombinations.push_back(vector<set<int>>());
        getCombinations(varInds, 0, ar, varCombinations.back());

        orAritiesDensity[ar] = 0;
        int all = pow(2, ar);

        for (int i = 0; i < varCombinations.back().size(); i++)
        {
          for (int j = 0; j < all; j++)
          {
            negDensity[ar][i][j] = 0;
          }
        }

        for (int j = 0; j < varCombinations[ar].size(); j++)
        {
          varDensity[ar][j] = 0;
        }
      }
    }

    int getEpsilon(int min_freq, int num_zeros)
    {
      if (num_zeros == 0) return 1;

      // somewhat naive function; could be made dependent on other parameters,
      // not only on the minimum frequency and number of zero-frequencies...
      return 1 +
        ((min_freq == INT_MAX) ? 0 :
          guessUniformly(min_freq) / num_zeros / 10);
    }

    void stabilizeDensities(bool addEpsilon, bool freqs)
    {
      int freqCoef = freqs ? 15 : 1;
      int min_freq = INT_MAX;
      int num_zeros = 0;
      int eps = 0;

      for (auto & o : orAritiesDensity)
      {
        if (o.second == 0) num_zeros++;
        else
        {
          o.second *= freqCoef;
          min_freq = min(min_freq, o.second);
        }
      }

      if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
        else if (num_zeros == orAritiesDensity.size()) eps = 1;
          else eps = 0;

      for (auto & o : orAritiesDensity)
      {
        if (o.second == 0) o.second = eps;
      }

      for (auto & o : orAritiesDensity)
      {
        min_freq = INT_MAX;
        num_zeros = 0;
        for (auto &b : varDensity[o.first])
        {
          if (b.second == 0) num_zeros++;
          else
          {
            b.second *= freqCoef;
            min_freq = min(min_freq, b.second);
          }
        }

        if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
          else if (num_zeros == varDensity[o.first].size()) eps = 1;
            else eps = 0;

        for (auto &b : varDensity[o.first])
        {
          if (b.second == 0) b.second = eps;
        }

        int all = pow(2, o.first);

        for (int k = 0; k < varCombinations[o.first].size(); k++)
        {
          min_freq = INT_MAX;
          num_zeros = 0;

          for (int j = 0; j < all; j++)
          {
            if (negDensity[o.first][k][j] == 0) num_zeros++;
            else
            {
              negDensity[o.first][k][j] *= freqCoef;
              min_freq = min(min_freq, negDensity[o.first][k][j]);
            }
          }

          if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
            else if (num_zeros == all) eps = 1;
              else eps = 0;

          for (int j = 0; j < all; j++)
          {
            if (negDensity[o.first][k][j] == 0) negDensity[o.first][k][j] = eps;
          }
        }
      }

      negDensityTmp = negDensity;
    }

    void calculateStatistics(Bdisj& bcs, bool freqs)
    {
      int ar = bcs.arity;
      if (freqs)
      {
        orAritiesDensity[ar] ++;
        set<int> varComb;
        int negSet = 0;

        for (int i = 0; i < bcs.dstate.size(); i++)
        {
          auto & b = bcs.dstate[i];
          varComb.insert(b.var);
          if (b.neg) negSet |= 1 << i;
        }

        for (int j = 0; j < varCombinations[ar].size(); j++)
        {
          if (varCombinations[ar][j] == varComb)
          {
            varDensity[ar][j]++;
            negDensity[ar][j][negSet] ++;

            break;
          }
        }
      }
      else
      {
        orAritiesDensity[ar] = 1;
        set<int> varComb;

        int negSet = 0;

        for (int i = 0; i < bcs.dstate.size(); i++)
        {
          auto & b = bcs.dstate[i];
          varComb.insert(b.var);
          if (b.neg) negSet |= 1 << i;
        }

        for (int j = 0; j < varCombinations[ar].size(); j++)
        {
          if (varCombinations[ar][j] == varComb)
          {
            varDensity[ar][j] = 1;
            negDensity[ar][j][negSet] = 1;

            break;
          }
        }
      }
    }

    void assignPrioritiesForBlocked(Bdisj& bcs)
    {
      int ar = bcs.arity;
      set<int> varComb;
      int negSet = 0;

      for (int i = 0; i < bcs.dstate.size(); i++)
      {
        auto & b = bcs.dstate[i];
        varComb.insert(b.var);
        if (b.neg) negSet |= 1 << i;
      }

      for (int j = 0; j < varCombinations[ar].size(); j++)
      {
        if (varCombinations[ar][j] == varComb)
        {
          negDensity[ar][j][negSet] = 0;
          break;
        }
      }
    }

    void printCodeStatistics()
    {
      for (auto & a : orAritiesDensity)
      {
        int ar = a.first;
        outs() << "Bool-Or arity density: " << ar << " |--> " << a.second << "\n";

        for (auto &b : varDensity[ar])
        {
          outs() << " Var Combination density: ";

          for (int j : varCombinations[ar][b.first])
          {
            outs() << *vars[j] << ", ";
          }

          outs() << "\b\b  |--> " << b.second << "\n";

          for (auto & n : negDensity[ar][b.first])
          {
            outs() << "   Var Negation density: ";
            int c = n.first;
            for (int j : varCombinations[ar][b.first])
            {
              int i;
              if (c > 0)
              {
                i = c & 1;
                c = c >> 1;
              }
              else
              {
                i = 0;
              }
              outs() << (i ? "! " : "  ") << *vars[j] << " || ";
            }

            outs() << "\b\b\b  |--> " << n.second << "\n";
          }
        }
      }
    }
  };
}


#endif
