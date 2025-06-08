/*
 * Copyright (c) 2024-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef GOLEM_STDUTILS_H
#define GOLEM_STDUTILS_H

#include <algorithm>
#include <optional>

namespace golem {
template<typename MapT>
std::optional<typename MapT::mapped_type> tryGetValue(MapT const & map, typename MapT::key_type const & key) {
    auto it = map.find(key);
    return it == map.end() ? std::nullopt : std::optional<typename MapT::mapped_type>{it->second};
}

bool isSubsetOf(auto const & subset, auto const & superset) {
    return std::ranges::all_of(subset, [&](PTRef elem) { return std::ranges::find(superset, elem) != end(superset); });
}

} // namespace golem

#endif // GOLEM_STDUTILS_H
