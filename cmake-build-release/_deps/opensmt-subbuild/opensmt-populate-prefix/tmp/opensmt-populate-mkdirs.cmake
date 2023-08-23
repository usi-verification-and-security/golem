# Distributed under the OSI-approved BSD 3-Clause License.  See accompanying
# file Copyright.txt or https://cmake.org/licensing for details.

cmake_minimum_required(VERSION 3.5)

file(MAKE_DIRECTORY
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-src"
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-build"
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix"
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/tmp"
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp"
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src"
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp"
)

set(configSubDirs )
foreach(subDir IN LISTS configSubDirs)
    file(MAKE_DIRECTORY "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/${subDir}")
endforeach()
if(cfgdir)
  file(MAKE_DIRECTORY "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp${cfgdir}") # cfgdir has leading slash
endif()
