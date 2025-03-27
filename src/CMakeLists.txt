include(FetchContent)

# Find OpenSMT2
SET(OPENSMT_HOME CACHE STRING "OpenSMT installation directory")
find_package(OpenSMT 2.7.0 EXACT CONFIG PATHS ${OPENSMT_HOME} NO_DEFAULT_PATH)

if (OpenSMT_FOUND)
else(OpenSMT_FOUND)
    FetchContent_Declare(
        OpenSMT
        GIT_REPOSITORY https://github.com/usi-verification-and-security/opensmt.git
        GIT_TAG e4e6a65d437bf4f0c3501b258dec4b10d0c4189a # v2.7.0
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
    )

target_include_directories(golem_lib PUBLIC ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/src/include)



if (NOT OpenSMT_FOUND)
    target_compile_definitions(golem_lib PUBLIC OPENSMT_LOCAL_BUILD)
    #message("Directories:${opensmt_SOURCE_DIR}; ${opensmt_BINARY_DIR}")
    target_include_directories(golem_lib PUBLIC 
        "${opensmt_SOURCE_DIR}/src/symbols"
        "${opensmt_SOURCE_DIR}/src/minisat/mtl"
    ${opensmt_SOURCE_DIR}/src/minisat/core
    ${opensmt_SOURCE_DIR}/src/common
    ${opensmt_SOURCE_DIR}/src/sorts
    ${opensmt_SOURCE_DIR}/src/symbols
    ${opensmt_SOURCE_DIR}/src/options
    ${opensmt_SOURCE_DIR}/src/api
    ${opensmt_SOURCE_DIR}/src/tsolvers
    ${opensmt_SOURCE_DIR}/src/tsolvers/egraph
    ${opensmt_SOURCE_DIR}/src/tsolvers/lasolver
    ${opensmt_SOURCE_DIR}/src/tsolvers/lrasolver
    ${opensmt_SOURCE_DIR}/src/tsolvers/liasolver
    ${opensmt_SOURCE_DIR}/src/cnfizers
    ${opensmt_SOURCE_DIR}/src/pterms
    ${opensmt_SOURCE_DIR}/src/logics
    ${opensmt_SOURCE_DIR}/src/smtsolvers
    ${opensmt_SOURCE_DIR}/src/parsers/smt2new
    ${opensmt_SOURCE_DIR}/src/simplifiers
    ${opensmt_SOURCE_DIR}/src/rewriters
    ${opensmt_SOURCE_DIR}/src/proof
    ${opensmt_SOURCE_DIR}/src/models
    ${opensmt_SOURCE_DIR}/src/itehandler
    ${opensmt_SOURCE_DIR}/src/interpolation
    )
    #message("GMP dirs:${GMP_INCLUDE_DIR}")
    target_include_directories(golem_lib PUBLIC ${GMP_INCLUDE_DIR})
endif()


add_subdirectory(bin)
