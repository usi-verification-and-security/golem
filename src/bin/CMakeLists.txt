add_executable(Golem "golem.cpp")

target_link_libraries(Golem PRIVATE golem_lib)

set_target_properties(Golem PROPERTIES
    OUTPUT_NAME golem
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")

add_executable(par "parallel_wrapper.cc")
set_target_properties(par PROPERTIES
        OUTPUT_NAME portfolio
        RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")