include(FetchContent)

FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG release-1.11.0
)

FetchContent_MakeAvailable(googletest)

include(GoogleTest)
add_executable(GolemTest)

target_sources(GolemTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LAWI.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_MBP.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_NNF.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_QE.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_TermUtils.cc"
    )

target_link_libraries(GolemTest PUBLIC golem_lib gtest gtest_main)
gtest_add_tests(TARGET GolemTest)