#include "ae/AeValSolver.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace ufo;

/** An AE-VAL wrapper for cmd
 *
 * Usage: specify 2 smt2-files that describe the formula \foral x. S(x) => \exists y . T (x, y)
 *   <s_part.smt2> = S-part (over x)
 *   <t_part.smt2> = T-part (over x, y)
 *   --skol = to print skolem function
 *   --debug = to print more info and perform sanity checks
 *
 * Notably, the tool automatically recognizes x and y based on their appearances in S or T.
 *
 * Example:
 *
 * ./tools/aeval/aeval
 *   ../test/ae/example1_s_part.smt2
 *   ../test/ae/example1_t_part.smt2
 *
 */

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

char * getSmtFileName(int num, int argc, char ** argv)
{
  int num1 = 1;
  for (int i = 1; i < argc; i++)
  {
    int len = strlen(argv[i]);
    if (len >= 5 && strcmp(argv[i] + len - 5, ".smt2") == 0)
    {
      if (num1 == num) return argv[i];
      else num1++;
    }
  }
  return NULL;
}

void printUsage()
{
  outs() << "Usage: aeval <file1.smt2> [file2.smt2] [options]\n";
  outs() << "  Options:\n";
  outs() << "    --skol\n";
  outs() << "    --all-inclusive\n";
  outs() << "    --compact\n";
  outs() << "    --split\n";
}

int main (int argc, char ** argv)
{

  if(getBoolValue("--help", false, argc, argv) || argc == 1)
  {
    printUsage();
    return 0;
  }

  ExprFactory efac;
  EZ3 z3(efac);

  bool skol = getBoolValue("--skol", false, argc, argv);
  bool allincl = getBoolValue("--all-inclusive", false, argc, argv);
  bool compact = getBoolValue("--compact", false, argc, argv);
  bool debug = getBoolValue("--debug", false, argc, argv);
  bool split = getBoolValue("--split", false, argc, argv);

  Expr s = z3_from_smtlib_file (z3, getSmtFileName(1, argc, argv));
  Expr t = z3_from_smtlib_file (z3, getSmtFileName(2, argc, argv));

  if (allincl)
    getAllInclusiveSkolem(s, t, debug, compact);
  else
    aeSolveAndSkolemize(s, t, skol, debug, compact, split);

  return 0;
}
