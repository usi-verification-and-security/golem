//
// Created by Martin Blicha on 14.08.20.
//

#ifndef OPENSMT_REVERSEWRAPPER_H
#define OPENSMT_REVERSEWRAPPER_H

#include "Engine.h"
#include <memory>

class ReverseWrapper : public Engine {
    std::unique_ptr<Engine> wrapped;
    Logic & logic;
public:
    explicit ReverseWrapper(std::unique_ptr<Engine> wrapped, Logic & logic) : wrapped(std::move(wrapped)), logic(logic) {}

    GraphVerificationResult solve(const ChcDirectedGraph& graph) {
        auto reversedGraph = graph.reverse(logic);
        auto res = wrapped->solve(reversedGraph);
        ChcGraphContext ctx(reversedGraph, logic);
        return reverse(std::move(res), ctx);
    }

private:
    GraphVerificationResult reverse(GraphVerificationResult res, ChcGraphContext & ctx) {
        switch(res.getAnswer()) {
            case VerificationResult::SAFE:
                return GraphVerificationResult(VerificationResult::SAFE, reverse(res.getValidityWitness()));
            case VerificationResult::UNSAFE:
                return GraphVerificationResult(VerificationResult::UNSAFE, reverse(res.getInvalidityWitness(), ctx));
            case VerificationResult::UNKNOWN:
                return res;
        }
	throw std::logic_error("Unreachable!");
    }

    ValidityWitness reverse(ValidityWitness const & witness) {
        Logic & logic = this->logic;
        ValidityWitness::definitions_type newDefinitions;
        witness.run([&logic, &newDefinitions](ValidityWitness::entry_type const & entry) {
            newDefinitions.insert({entry.first, logic.mkNot(entry.second)});
        });
        return ValidityWitness(std::move(newDefinitions));
    }

    InvalidityWitness reverse(InvalidityWitness const & witness, ChcGraphContext & ctx);
};

#endif //OPENSMT_REVERSEWRAPPER_H
