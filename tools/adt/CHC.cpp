#include "adt/CHCSolver.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace ufo;

char * getStrValue(const char * opt, const char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return (char *)defValue;
}

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

int main (int argc, char ** argv)
{
  char *infile = getSmtFileName(1, argc, argv);
  bool givePriorityNonAdt = getBoolValue("--give-nonadt-priority", false, argc, argv);
  bool ignoreBaseVar = getBoolValue("--ignore-base", false, argc, argv);
  chcSolve(infile, givePriorityNonAdt, ignoreBaseVar);
  return 0;
}
