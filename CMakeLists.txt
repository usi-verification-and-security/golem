cmake_minimum_required(VERSION 3.14)

set(GOLEM_VERSION_MAJOR 0)
set(GOLEM_VERSION_MINOR 6)
set(GOLEM_VERSION_PATCH 2)
set(GOLEM_VERSION ${GOLEM_VERSION_MAJOR}.${GOLEM_VERSION_MINOR}.${GOLEM_VERSION_PATCH})
project(Golem VERSION ${GOLEM_VERSION} LANGUAGES CXX)

add_definitions(-DGOLEM_VERSION="${GOLEM_VERSION}")

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_SOURCE_DIR "src")

set(VALID_BUILD_TYPES "Debug" "Release" "RelWithDebInfo" "MinSizeRel")

#Set the default build type if this is the first time cmake is run and nothing has been set
if (NOT EXISTS ${CMAKE_BINARY_DIR}/CMakeCache.txt)
  if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Choose the type of build, options are: Debug Release RelWithDebInfo MinSizeRel." FORCE)
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${VALID_BUILD_TYPES})
  endif()
endif()

list(FIND VALID_BUILD_TYPES "${CMAKE_BUILD_TYPE}" _build_type_index)
if(_build_type_index EQUAL -1)
  message(FATAL_ERROR "Invalid build type: ${CMAKE_BUILD_TYPE}. Valid options are: ${VALID_BUILD_TYPES}")
endif()

option(GOLEM_BUILD_TEST "Build the tests" ON)

add_subdirectory(${CMAKE_SOURCE_DIR})

################# TESTING #############################################
if(GOLEM_BUILD_TEST)
    enable_testing()
    add_subdirectory(${PROJECT_SOURCE_DIR}/test)
endif()
#########################################################################
