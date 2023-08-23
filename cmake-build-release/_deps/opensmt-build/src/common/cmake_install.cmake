# Install script for directory: /home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Release")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "Unspecified" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/opensmt" TYPE FILE FILES
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/Integer.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/Number.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/FastRational.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/XAlloc.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/Alloc.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/StringMap.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/Timer.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/osmtinttypes.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/TreeOps.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/Real.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/FlaPartitionMap.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/PartitionInfo.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/OsmtApiException.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/TypeUtils.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/NumberUtils.h"
    "/home/mambo/golem/cmake-build-release/_deps/opensmt-src/src/common/NatSet.h"
    )
endif()

