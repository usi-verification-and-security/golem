#ifndef GOLEM_COMMON_H
#define GOLEM_COMMON_H

#include "Witnesses.h"
#include "graph/ChcGraph.h"

namespace golem {

VerificationResult solveTrivial(ChcDirectedGraph const & graph);

} // namespace golem

#endif // GOLEM_COMMON_H
