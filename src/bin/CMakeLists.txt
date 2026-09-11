add_executable(Golem "golem.cpp")

target_link_libraries(Golem PRIVATE golem_lib)

set_target_properties(Golem PROPERTIES
    OUTPUT_NAME golem
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")

add_executable(GolemQE "golem-qe.cc")

target_link_libraries(GolemQE PRIVATE golem_lib)

set_target_properties(GolemQE PROPERTIES
    OUTPUT_NAME golem-qe
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
