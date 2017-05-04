#ifndef DISTRIBUTED_HPP__
#define DISTRIBUTED_HPP__

#include <boost/mpi.hpp>
#include "LinCom.hpp"

using namespace ufo;
using namespace std;

#define MSG_TAG_COMPLETE 1
#define MSG_RESULT 2

enum PeerResultKind: int {
  PeerResultKindGarbage,
  PeerResultKindFailure,
  PeerResultKindLemma
};

struct PeerResult {
  PeerResultKind kind;
  unsigned declIdx;  // index of `disj` home LAfactory
  LAdisj disj;
};

template<class Archive>
void serialize(Archive& ar, PeerResult& pr, const unsigned int version)
{
  ar & pr.kind;
  ar & pr.declIdx;
  ar & pr.disj;
}


// point-to-point MPI send to all other workers; blocks for send completions
template<typename T>
void sendToOthers(boost::mpi::communicator world, int tag, const T &t)
{
  vector<boost::mpi::request> completionReqs(world.size() - 1);
  for (size_t i = 0; i < world.size(); i++) {
    if (i != world.rank()) {
      boost::mpi::request r = world.isend(i, tag, t);
      completionReqs.push_back(r);
    }
  }
  boost::mpi::wait_all(completionReqs.begin(), completionReqs.end());
}

#endif
