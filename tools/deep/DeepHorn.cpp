#include <boost/mpi/environment.hpp>
#include <boost/mpi/communicator.hpp>
#include "deep/RndLearner.hpp"

using namespace ufo;
using namespace std;
namespace mpi = boost::mpi;

#define MSG_TAG_COMPLETE 1

int main (int argc, char **argv)
{
  // Initialize MPI
  mpi::environment env(argc, argv);
  mpi::communicator world;

  // Parse command-line arguments
  if (argc == 1) {
    cerr << "At least an input file should be given\n";
    return 1;
  }

  if (world.rank() != 1) {
    sleep(10);
  }

  int maxAttempts = 2000000;       //default
  if (argc > 2) maxAttempts = atoi(argv[1]);

  bool densecode = true;           //default
  if (argc > 3) densecode = atoi(argv[2]);

  bool shrink = true;              //default
  if (argc > 4) shrink = atoi(argv[3]);

  bool aggressivepruning = true;   //default
  if (argc > 5) aggressivepruning = atoi(argv[4]);

  // Call the workhorse
  auto shouldStop = [&world]() -> bool {
    return (bool)world.iprobe(mpi::any_source, MSG_TAG_COMPLETE);
  };
  const SynthResult r = learnInvariants(shouldStop, string(argv[argc-1]),
                                        maxAttempts, densecode, shrink,
                                        aggressivepruning);

  // Found something? Let everybody know so we can shut down.
  if (r.foundInvariants) {
    vector<mpi::request> completionReqs(world.size() - 1);
    for (size_t i = 0; i < world.size(); i++) {
      if (i != world.rank()) {
        mpi::request r = world.isend(i, MSG_TAG_COMPLETE, "success");
        completionReqs.push_back(r);
      }
    }
    mpi::wait_all(completionReqs.begin(), completionReqs.end());
  }

  return 0;
}
