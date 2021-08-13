//
// Created by Martin Blicha on 02.09.20.
//

#include "ReverseWrapper.h"

InvalidityWitness ReverseWrapper::reverse(InvalidityWitness const & witness, ChcGraphContext & ctx) {
    InvalidityWitness reversed;
    auto originalPath = witness.getErrorPath().getEdges();
    InvalidityWitness::ErrorPath reversedPath;
    std::reverse(originalPath.begin(), originalPath.end());
    reversedPath.setPath(std::move(originalPath));
    reversed.setErrorPath(std::move(reversedPath));
    return reversed;
}
