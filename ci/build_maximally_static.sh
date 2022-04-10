#!/bin/bash

set -e
build_folder="build-static"
if [ -d ${build_folder} ]; then rm -rf ${build_folder}; fi
mkdir -p ${build_folder}
cd ${build_folder}

if [ ! -z ${CMAKE_CXX_COMPILER} ]; then
    COMPILER_OPTION="-DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}"
fi

if [[ $OSTYPE != "darwin"* ]]; then
    LINKER_OPTIONS="-DCMAKE_EXE_LINKER_FLAGS=-static"
fi

cmake -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} \
      -DCMAKE_CXX_FLAGS="${FLAGS}" \
      -DCMAKE_INSTALL_PREFIX=${OSMT_INSTALL} \
      -DMAXIMALLY_STATIC_BINARY=YES\
      ${COMPILER_OPTION} \
      ${LINKER_OPTIONS} \
      ..

cmake --build . -j 4

strip golem

tar jcf golem.tar.bz2 golem

echo "Placed stripped, maximally static binary in $(pwd)/golem.tar.bz2"
