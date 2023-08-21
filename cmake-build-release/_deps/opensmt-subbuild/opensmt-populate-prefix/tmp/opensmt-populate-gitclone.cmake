# Distributed under the OSI-approved BSD 3-Clause License.  See accompanying
# file Copyright.txt or https://cmake.org/licensing for details.

cmake_minimum_required(VERSION 3.5)

if(EXISTS "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitclone-lastrun.txt" AND EXISTS "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitinfo.txt" AND
  "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitclone-lastrun.txt" IS_NEWER_THAN "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitinfo.txt")
  message(STATUS
    "Avoiding repeated git clone, stamp file is up to date: "
    "'/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitclone-lastrun.txt'"
  )
  return()
endif()

execute_process(
  COMMAND ${CMAKE_COMMAND} -E rm -rf "/home/mambo/golem/cmake-build-release/_deps/opensmt-src"
  RESULT_VARIABLE error_code
)
if(error_code)
  message(FATAL_ERROR "Failed to remove directory: '/home/mambo/golem/cmake-build-release/_deps/opensmt-src'")
endif()

# try the clone 3 times in case there is an odd git clone issue
set(error_code 1)
set(number_of_tries 0)
while(error_code AND number_of_tries LESS 3)
  execute_process(
    COMMAND "/usr/bin/git" 
            clone --no-checkout --depth 1 --no-single-branch --progress --config "advice.detachedHead=false" "https://github.com/usi-verification-and-security/opensmt.git" "opensmt-src"
    WORKING_DIRECTORY "/home/mambo/golem/cmake-build-release/_deps"
    RESULT_VARIABLE error_code
  )
  math(EXPR number_of_tries "${number_of_tries} + 1")
endwhile()
if(number_of_tries GREATER 1)
  message(STATUS "Had to git clone more than once: ${number_of_tries} times.")
endif()
if(error_code)
  message(FATAL_ERROR "Failed to clone repository: 'https://github.com/usi-verification-and-security/opensmt.git'")
endif()

execute_process(
  COMMAND "/usr/bin/git" 
          checkout "596501bab9008a69ea20f499911e7c751fe0f29e" --
  WORKING_DIRECTORY "/home/mambo/golem/cmake-build-release/_deps/opensmt-src"
  RESULT_VARIABLE error_code
)
if(error_code)
  message(FATAL_ERROR "Failed to checkout tag: '596501bab9008a69ea20f499911e7c751fe0f29e'")
endif()

set(init_submodules TRUE)
if(init_submodules)
  execute_process(
    COMMAND "/usr/bin/git" 
            submodule update --recursive --init 
    WORKING_DIRECTORY "/home/mambo/golem/cmake-build-release/_deps/opensmt-src"
    RESULT_VARIABLE error_code
  )
endif()
if(error_code)
  message(FATAL_ERROR "Failed to update submodules in: '/home/mambo/golem/cmake-build-release/_deps/opensmt-src'")
endif()

# Complete success, update the script-last-run stamp file:
#
execute_process(
  COMMAND ${CMAKE_COMMAND} -E copy "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitinfo.txt" "/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitclone-lastrun.txt"
  RESULT_VARIABLE error_code
)
if(error_code)
  message(FATAL_ERROR "Failed to copy script-last-run stamp file: '/home/mambo/golem/cmake-build-release/_deps/opensmt-subbuild/opensmt-populate-prefix/src/opensmt-populate-stamp/opensmt-populate-gitclone-lastrun.txt'")
endif()
