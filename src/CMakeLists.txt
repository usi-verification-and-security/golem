include(FetchContent)

# Find OpenSMT2
SET(OPENSMT_HOME CACHE STRING "OpenSMT installation directory")
find_package(OpenSMT 2.9.1 EXACT CONFIG PATHS ${OPENSMT_HOME} NO_DEFAULT_PATH)

if (OpenSMT_FOUND)
else(OpenSMT_FOUND)
    FetchContent_Declare(
        OpenSMT
        GIT_REPOSITORY https://github.com/usi-verification-and-security/opensmt.git
        GIT_TAG 3a90e58a43e8fa90a7500f7f0ccd5af8bc692268 # v2.9.1
        GIT_SHALLOW true
        GIT_PROGRESS true
    )
    #set(FETCHCONTENT_QUIET OFF)
    set(BUILD_EXECUTABLES OFF CACHE INTERNAL "")
    set(BUILD_SHARED_LIBS OFF CACHE INTERNAL "")
    set(BUILD_STATIC_LIBS ON CACHE INTERNAL "")
    set(PACKAGE_TESTS OFF CACHE INTERNAL "")
    message("Getting OpenSMT...")
    FetchContent_MakeAvailable(OpenSMT)
    message("OpenSMT downloaded")
    add_library(OpenSMT::OpenSMT ALIAS OpenSMT-static)
endif(OpenSMT_FOUND)

add_library(golem_lib OBJECT "")

target_link_libraries(golem_lib PUBLIC OpenSMT::OpenSMT)

target_sources(golem_lib
    PRIVATE ChcSystem.cc
    PRIVATE ChcInterpreter.cc
    PRIVATE engine/ArgBasedEngine.cc
    PRIVATE engine/Bmc.cc
    PRIVATE engine/Common.cc
    PRIVATE engine/DAR.cc
    PRIVATE engine/EngineFactory.cc
    PRIVATE engine/IMC.cc
    PRIVATE engine/Kind.cc
    PRIVATE engine/Lawi.cc
    PRIVATE engine/PDKind.cc
    PRIVATE engine/Spacer.cc
    PRIVATE engine/SymbolicExecution.cc
    PRIVATE engine/TPA.cc
    PRIVATE engine/TransitionSystemEngine.cc
    PRIVATE TransitionSystem.cc
    PRIVATE Options.cc
    PRIVATE TermUtils.cc
    PRIVATE TransformationUtils.cc
    PRIVATE Validator.cc
    PRIVATE Normalizer.cc
    PRIVATE Witnesses.cc
    PRIVATE proofs/Term.h
    PRIVATE proofs/Term.cc
    PRIVATE proofs/ProofSteps.h
    PRIVATE proofs/ProofSteps.cc
    PRIVATE ModelBasedProjection.cc
    PRIVATE QuantifierElimination.cc
    PRIVATE graph/ChcGraph.cc
    PRIVATE graph/ChcGraphBuilder.cc
    PRIVATE termination/Frontend.cc
    PRIVATE termination/LassoDetector.cc
    PRIVATE termination/ReachabilityTerm.cc
    PRIVATE transformers/BasicTransformationPipelines.cc
    PRIVATE transformers/CommonUtils.cc
    PRIVATE transformers/ConstraintSimplifier.cc
    PRIVATE transformers/EdgeInliner.cc
    PRIVATE transformers/SimpleChainSummarizer.cc
    PRIVATE transformers/NodeEliminator.cc
    PRIVATE transformers/MultiEdgeMerger.cc
    PRIVATE transformers/FalseClauseRemoval.cc
    PRIVATE transformers/RemoveUnreachableNodes.cc
    PRIVATE transformers/NestedLoopTransformation.cc
    PRIVATE transformers/SingleLoopTransformation.cc
    PRIVATE transformers/TransformationPipeline.cc
    PRIVATE transformers/TrivialEdgePruner.cc
    PRIVATE utils/SmtSolver.cc
    PRIVATE utils/SExpressions.cc
    PRIVATE vmt/FrontEnd.cc
    )

target_include_directories(golem_lib PUBLIC ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/src/include)



if (NOT OpenSMT_FOUND)
    target_compile_definitions(golem_lib PUBLIC OPENSMT_LOCAL_BUILD)
    #message("Directories:${opensmt_SOURCE_DIR}; ${opensmt_BINARY_DIR}")
    target_include_directories(golem_lib PUBLIC "${opensmt_SOURCE_DIR}/src")
    #message("GMP dirs:${GMP_INCLUDE_DIR}")
    target_include_directories(golem_lib PUBLIC ${GMP_INCLUDE_DIR})
endif()


add_subdirectory(bin)
