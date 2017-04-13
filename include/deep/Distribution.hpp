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
    for (auto &a : den) // assume the smallest "a.first" comes first
    {
      w += a.second;
      while (d.distr.size() < a.first) d.distr.push_back(0);
      d.distr.push_back(w);
    }
    return d.guessFromDistr();
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
}


#endif