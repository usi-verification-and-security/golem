include(FetchContent)

FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.15.0
)

FetchContent_MakeAvailable(googletest)

include(GoogleTest)
add_executable(GolemTest)

target_sources(GolemTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_BMC.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_KIND.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LAWI.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_MBP.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_NNF.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Normalizer.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_QE.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Spacer.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_TermUtils.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_TPA.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_TransformationUtils.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Transformers.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_IMC.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_PDKIND.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_PredicateAbstraction.cc"
    )

target_link_libraries(GolemTest PUBLIC golem_lib gtest gtest_main)
gtest_add_tests(TARGET GolemTest)
