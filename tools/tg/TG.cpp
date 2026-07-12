#include "deep/TGRndLearnerV3.hpp"
#include <cstdlib>

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

char * getStrValue(const char * opt, char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      char* p;
      int num = strtol(argv[i+1], &p, 10);
      if (*p) return 1;      // if used w/o arg, return boolean
      else return num;
    }
  }
  return defValue;
}
static inline void getNums(set<int>& nums, char * str)
{
  if (str == NULL) return;
  string vals(str);
  size_t pos = 0;
  while (pos <= vals.size())
  {
    size_t comma = vals.find(',', pos);
    string val = vals.substr(pos, comma == string::npos ? string::npos : comma - pos);
    if (!val.empty()) nums.insert(atoi(val.c_str()));
    if (comma == string::npos) break;
    pos = comma + 1;
  }
}

const char *OPT_HELP = "--help";
const char *OPT_MAX_ATTEMPTS = "--attempts";
const char *OPT_TO = "--to";
const char *OPT_LB = "--lb";
const char *OPT_LMAX = "--max";
const char *OPT_ELIM = "--skip-elim";
const char *OPT_ARITHM = "--skip-arithm";
const char *OPT_SEED = "--inv-mode";
const char *OPT_GET_FREQS = "--freqs";
const char *OPT_AGG_PRUNING = "--aggp";
const char *OPT_DATA_LEARNING = "--data";
const char *OPT_PROP = "--prop";
const char *OPT_DISJ = "--disj";
const char *OPT_D1 = "--all-mbp";
const char *OPT_D2 = "--phase-prop";
const char *OPT_D3 = "--phase-data";
const char *OPT_D4 = "--stren-mbp";
const char *OPT_MBP = "--eqs-mbp";
const char *OPT_DEBUG = "--debug";

int main (int argc, char ** argv)
{
  if (getBoolValue(OPT_HELP, false, argc, argv) || argc == 1)
  {
    outs () << "Usage: tg [options] --keys <k1,k2,...> <file.smt2>\n"
            << "Options: --lb --max --inv-mode <N> --lookahead <N> --all-to <N> "
            << "--attempts <N> --to <N> --skip-elim --skip-arithm --no-term "
            << "--prio --prune --eqs-mbp <N> --debug <N>\n";
    return 0;
  }

  set<int> nums;
  getNums(nums, getStrValue("--keys", NULL, argc, argv));
  bool to_skip = getBoolValue("--no-term", false, argc, argv);
  int lookahead = getIntValue("--lookahead", 3, argc, argv);
  bool prio = getBoolValue("--prio", false, argc, argv);
  bool prune = getBoolValue("--prune", false, argc, argv);
  int all_to = getIntValue("--all-to", 900, argc, argv);
  bool lb = getBoolValue(OPT_LB, false, argc, argv);
  bool lmax = getBoolValue(OPT_LMAX, false, argc, argv);

  // All other attrs are inherited from FreqHorn:
  int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 10, argc, argv);
  int to = getIntValue(OPT_TO, 1000, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  bool do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
  bool do_arithm = !getBoolValue(OPT_ARITHM, false, argc, argv);
  int invMode = getIntValue(OPT_SEED, 0, argc, argv);
  int do_prop = getIntValue(OPT_PROP, 0, argc, argv);
  int do_disj = getBoolValue(OPT_DISJ, false, argc, argv);
  bool do_dl = getBoolValue(OPT_DATA_LEARNING, false, argc, argv);
  int mbp_eqs = getIntValue(OPT_MBP, 0, argc, argv);
  bool d_m = getBoolValue(OPT_D1, false, argc, argv);
  bool d_p = getBoolValue(OPT_D2, false, argc, argv);
  bool d_d = getBoolValue(OPT_D3, false, argc, argv);
  bool d_s = getBoolValue(OPT_D4, false, argc, argv);
  int debug = getIntValue(OPT_DEBUG, 0, argc, argv);

  if (do_disj && (!d_p && !d_d))
  {
    errs() << "WARNING: either \"" << OPT_D2 << "\" or \"" << OPT_D3 << "\" should be enabled\n"
           << "enabling \"" << OPT_D3 << "\"\n";
    d_d = true;
  }

  if (d_m || d_p || d_d || d_s) do_disj = true;
  if (do_disj) do_dl = true;

  testgen(string(argv[argc-1]), nums, max_attempts, to, all_to, densecode, aggressivepruning,
                     do_dl, do_elim, do_disj, do_prop, d_m, d_p, d_d, d_s,
                     mbp_eqs, to_skip, invMode, lookahead, lb, lmax, prio, prune, debug);
  return 0;
}
