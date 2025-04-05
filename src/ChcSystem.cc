/*
 * Copyright (c) 2020-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ChcSystem.h"

#include <iostream>

namespace golem {
void ChcPrinter::print(const ChcSystem & system, std::ostream & out) const {
    auto const & clauses = system.getClauses();
    for (auto const& clause : clauses) {
        print(clause, out);
    }
}

void ChcPrinter::print(const ChClause & clause, std::ostream & out) const {
    auto const & head = clause.head;
    std::string headStr = logic.printTerm(head.predicate.predicate);
    out << headStr << " :- " << '\n';
    auto const & body = clause.body;
    for (auto const& predicate : body.uninterpretedPart) {
        out << '\t' << logic.printTerm(predicate.predicate) << ",\n";
    }
    out << '\t' << logic.printTerm(body.interpretedPart.fla) << std::endl;
}
} // namespace golem
