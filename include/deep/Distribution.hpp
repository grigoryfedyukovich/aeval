#ifndef DISTRIBUTION__HPP__
#define DISTRIBUTION__HPP__

#define MAXDISTR 1000

using namespace std;
using namespace boost;

namespace ufo
{
  typedef vector<int> distribution;
  typedef vector<int> weights;
  typedef map<int, int> density;

  class Distr
  {
    public:

    distribution distr;

    Distr() {}

    void setupUniformDistr(int range)
    {
      for (int i = 1; i < range; i++)
      {
        int num = i * MAXDISTR / range;
        distr.push_back(num);
      }
      distr.push_back(MAXDISTR);
    }

    int guessFromDistr()
    {
      int rnd = 0;
      int range = distr.size();
      int maxd = distr[range-1];

      int i = std::rand() % maxd;
      while (i >= distr[rnd]) rnd ++;

      return rnd;
    }
  };

  inline static int chooseByWeight(weights& wg)
  {
    Distr d;
    int w = 0;
    for (int i = 0; i < wg.size(); i++)
    {
      w += wg[i];
      d.distr.push_back(w);
    }
    return d.guessFromDistr();
  }

  inline static int chooseByWeight(density& den)
  {
    Distr d;
    int w = 0;
    map<int, int> indeces;
    for (auto &a : den) // assume the smallest "a.first" comes first
    {
      w += a.second;
      indeces[d.distr.size()] = a.first;
      d.distr.push_back(w);
    }
    int ind = d.guessFromDistr();
    return indeces[ind];
  }

  inline static int guessUniformly(int range)
  {
    assert(range > 0);
    return std::rand() % range;
  }

  inline static void initDistrs(vector<weights>& distrs, int sz1, int sz2, int defaultValue = 1000)
  {
    if (distrs.size() == 0)
    {
      for (int i = 0; i < sz1; i++)
      {
        distrs.push_back(weights());
        for (int j = 0; j < sz2; j++)
        {
          distrs.back().push_back(defaultValue);      // should be something greater than zero
        }
      }
    }
  }

  inline static bool isDefault(weights& d, int defaultValue = 1000)
  {
    for (int i = 0; i < d.size(); i++)
    {
      if (d[i] != defaultValue) return false;
    }
    return true;
  }

  inline static bool isEmpty(density& d)
  {
    for (int i = 0; i < d.size(); i++)
    {
      if (d[i] > 0) return false;
    }
    return true;
  }

  inline static void printDistr(weights& distr, string msg)
  {
    if (msg != "" ) outs () << msg << ": ";
    outs () << "[";
    for (int j = 0; j < distr.size(); j++)
    {
      outs() << distr[j] << ", ";
    }
    outs () << "]\n";
  }

  static inline void getCombinations(vector<int>& data, int start, int rem, vector< set<int> >& res)
  {
    if (start >= data.size()) return;
    if (rem > data.size() - start) return;

    if (rem == 1)
    {
      for (int i = start; i < data.size(); i++)
      {
        set<int> res0;
        res0.insert(data[i]);
        res.push_back(res0);
      }
    }
    else
    {
      // if include data[start]
      vector< set<int>> res1;
      getCombinations(data, start + 1, rem - 1, res1);

      for (int i = 0; i < res1.size(); i++)
      {
        res1[i].insert(data[start]);
        res.push_back(res1[i]);
      }

      // if skip data[start]
      vector< set<int>> res2;
      getCombinations(data, start + 1, rem, res2);

      for (int i = 0; i < res2.size(); i++)
      {
        res.push_back(res2[i]);
      }
    }
  }
}


#endif
