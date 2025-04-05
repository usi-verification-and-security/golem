/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef SCOPEGUARD_H
#define SCOPEGUARD_H

#include <utility>

namespace golem {
template <typename Func>
class ScopeGuard {
public:
    explicit ScopeGuard(Func&& func) : func(std::forward<Func>(func)) {}

    ~ScopeGuard() { func(); }

    ScopeGuard(const ScopeGuard&) = delete;
    ScopeGuard& operator=(const ScopeGuard&) = delete;

private:
    Func func;
};
} // namespace golem

#endif //SCOPEGUARD_H
