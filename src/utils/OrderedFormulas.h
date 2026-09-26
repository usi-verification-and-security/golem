/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_ORDEREDFORMULAS_H
#define GOLEM_ORDEREDFORMULAS_H

#include "pterms/PTRef.h"

#include <cstddef>
#include <deque>
#include <unordered_set>

namespace golem {
/// Formulas collected for one node, without duplicates, in insertion order so the oldest can be
/// evicted first.
class OrderedFormulas {
public:
    std::size_t size() const { return order.size(); }
    auto begin() const { return order.begin(); }
    auto end() const { return order.end(); }
    /// Adds `formula` unless already present (a duplicate keeps its original position); then, if
    /// `maxSize` > 0, evicts the oldest formulas until at most `maxSize` remain.
    void insert(PTRef formula, std::size_t maxSize) {
        if (not members.insert(formula).second) { return; }
        order.push_back(formula);
        while (maxSize > 0 and order.size() > maxSize) {
            members.erase(order.front());
            order.pop_front();
        }
    }
    /// Drops every formula but the most recently added one.
    void keepOnlyNewest() {
        if (order.size() > 1) { replaceWith(order.back()); }
    }
    /// Replaces every formula by `formula`.
    void replaceWith(PTRef formula) {
        order.assign(1, formula);
        members = {formula};
    }

private:
    std::deque<PTRef> order;
    std::unordered_set<PTRef, PTRefHash> members;
};
} // namespace golem

#endif // GOLEM_ORDEREDFORMULAS_H
