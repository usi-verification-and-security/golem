/*
 * Copyright (c) 2024-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_TIMER_H
#define GOLEM_TIMER_H

#include <chrono>

namespace golem {
struct Timer {
    Timer() : start(std::chrono::high_resolution_clock::now()) {}
    [[nodiscard]] auto elapsedMilliseconds() const {
        return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::high_resolution_clock::now() - start)
            .count();
    }

private:
    std::chrono::high_resolution_clock::time_point start;
};
} // namespace golem

#define MEASURE(statement)                                                                                             \
    Timer timer;                                                                                                       \
    statement;                                                                                                         \
    auto elapsedMs = timer.elapsedMilliseconds();

#define MEASURE_AND_REPORT(statement)                                                                                  \
    MEASURE(statement)                                                                                                 \
    std::cout << "Execution of \"" << #statement << "\" took " << elapsedMs << " ms\n";

#endif // GOLEM_TIMER_H
