#include <boost/mpi/environment.hpp>
#include <boost/mpi/communicator.hpp>
#include <boost/serialization/vector.hpp>
#include "deep/RndLearner.hpp"
#include "deep/Distributed.hpp"

using namespace ufo;
using namespace std;

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

  int maxAttempts = 2000000;       //default
  if (argc > 2) maxAttempts = atoi(argv[1]);

  bool densecode = true;           //default
  if (argc > 3) densecode = atoi(argv[2]);

  bool shrink = true;              //default
  if (argc > 4) shrink = atoi(argv[3]);

  bool aggressivepruning = true;   //default
  if (argc > 5) aggressivepruning = atoi(argv[4]);

  // A silly way to keep workers out of sync
  // TODO: Just wait for previous in chain
  sleep(world.rank());

  // Callbacks for `learnInvariants`
  const auto shouldStop = [&world]() -> bool {
    return (bool)world.iprobe(mpi::any_source, MSG_TAG_COMPLETE);
  };
  const auto accumulateNewLemmas = [&world]() -> vector<PeerResult> {
    auto lemmas = vector<PeerResult>();
    if (world.iprobe(mpi::any_source, MSG_RESULT)) {
      PeerResult result;
      world.recv(mpi::any_source, MSG_RESULT, result);
      lemmas.push_back(result);
    }
    return lemmas;
  };
  const auto learnedLemma = [&world](unsigned declIdx, LAdisj& disj) {
    PeerResult result { PeerResultKindLemma, declIdx, disj };
    sendToOthers(world, MSG_RESULT, result);
  };
  const auto gotFailure = [&world](unsigned declIdx, LAdisj& disj) {
    PeerResult result { PeerResultKindFailure, declIdx, disj };
    sendToOthers(world, MSG_RESULT, result);
  };
  const auto gotGarbage = [&world](unsigned declIdx, LAdisj& disj) {
    PeerResult result { PeerResultKindGarbage, declIdx, disj };
    sendToOthers(world, MSG_RESULT, result);
  };


  // Call the workhorse
  const SynthResult r = learnInvariants(string(argv[argc-1]), maxAttempts,
                                        densecode, shrink, aggressivepruning,
                                        shouldStop, accumulateNewLemmas,
                                        learnedLemma, gotFailure, gotGarbage);

  // Found something? Let everybody know so we can shut down.
  if (r.foundInvariants) {
    sendToOthers(world, MSG_TAG_COMPLETE, "success");
  }

  return 0;
}
