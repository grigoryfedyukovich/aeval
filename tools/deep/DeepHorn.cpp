#include <boost/mpi/environment.hpp>
#include <boost/mpi/communicator.hpp>
#include <boost/serialization/vector.hpp>
#include "deep/RndLearner.hpp"

using namespace ufo;
using namespace std;
namespace mpi = boost::mpi;

#define MSG_TAG_COMPLETE 1
#define MSG_LEMMA_FOUND 2

// point-to-point MPI send to all other workers; blocks for send completions
template<typename T>
void sendToOthers(mpi::communicator world, int tag, const T &t)
{
  vector<mpi::request> completionReqs(world.size() - 1);
  for (size_t i = 0; i < world.size(); i++) {
    if (i != world.rank()) {
      mpi::request r = world.isend(i, tag, t);
      completionReqs.push_back(r);
    }
  }
  mpi::wait_all(completionReqs.begin(), completionReqs.end());
}

struct PortableLAdisj {
  unsigned declIdx;
  LAdisj inner;
};

template<class Archive>
void serialize(Archive& ar, PortableLAdisj& plad, const unsigned int version)
{
  ar & plad.declIdx;
  ar & plad.inner;
}

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

  // Callbacks for `learnInvariants`
  const auto shouldStop = [&world]() -> bool {
    return (bool)world.iprobe(mpi::any_source, MSG_TAG_COMPLETE);
  };
  const auto accumulateNewLemmas = [&world]() -> vector<pair<unsigned, LAdisj>> {
    auto lemmas = vector<pair<unsigned, LAdisj>>();
    if (world.iprobe(mpi::any_source, MSG_LEMMA_FOUND)) {
      PortableLAdisj portable;
      world.recv(mpi::any_source, MSG_LEMMA_FOUND, portable);
      lemmas.push_back(pair<unsigned, LAdisj>(portable.declIdx, portable.inner));
    }
    return lemmas;
  };
  const auto learnedLemma = [&world](unsigned declIdx, LAdisj& disj) {
    PortableLAdisj portable { declIdx, disj };
    sendToOthers(world, MSG_LEMMA_FOUND, portable);
  };

  // Call the workhorse
  const SynthResult r = learnInvariants(string(argv[argc-1]), maxAttempts,
                                        densecode, shrink, aggressivepruning,
                                        shouldStop, accumulateNewLemmas,
                                        learnedLemma);

  // Found something? Let everybody know so we can shut down.
  if (r.foundInvariants) {
    sendToOthers(world, MSG_TAG_COMPLETE, "success");
  }

  return 0;
}
