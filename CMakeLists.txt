cmake_minimum_required(VERSION 3.14)

set(GOLEM_VERSION_MAJOR 0)
set(GOLEM_VERSION_MINOR 1)
set(GOLEM_VERSION_PATCH 0)
set(GOLEM_VERSION ${GOLEM_VERSION_MAJOR}.${GOLEM_VERSION_MINOR}.${GOLEM_VERSION_PATCH})
project(Golem VERSION ${GOLEM_VERSION} LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_SOURCE_DIR "src")

#Set the default build type if this is the first time cmake is run and nothing has been set
if (NOT EXISTS ${CMAKE_BINARY_DIR}/CMakeCache.txt)
  if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
  endif()
endif()

option(GOLEM_BUILD_TEST "Build the tests" ON)

add_subdirectory(${CMAKE_SOURCE_DIR})

################# TESTING #############################################
if(GOLEM_BUILD_TEST)
    enable_testing()
    add_subdirectory(${PROJECT_SOURCE_DIR}/test)
endif()
#########################################################################
