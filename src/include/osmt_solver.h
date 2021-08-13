//
// Created by Martin Blicha on 13.08.21.
//

#ifndef GOLEM_OSMT_LOGICS_H
#define GOLEM_OSMT_LOGICS_H

#ifdef OPENSMT_LOCAL_BUILD
#include "MainSolver.h"
#include "Model.h"
#include "ModelBuilder.h"
#else
#include "opensmt/MainSolver.h"
#include "opensmt/Model.h"
#include "opensmt/ModelBuilder.h"
#endif // OPENSMT_LOCAL_BUILD

#endif //GOLEM_OSMT_LOGICS_H
