#ifndef ENTT_CONTAINER_FWD_HPP
#define ENTT_CONTAINER_FWD_HPP

// IWYU pragma: begin_exports
#include <functional>
#include <memory>
// IWYU pragma: end_exports

namespace entt {

template<
    typename Key,
    typename Type,
    typename = std::hash<Key>,
    typename = std::equal_to<Key>,
    typename = std::allocator<std::pair<const Key, Type>>>
class dense_map;

template<
    typename Type,
    typename = std::hash<Type>,
    typename = std::equal_to<Type>,
    typename = std::allocator<Type>>
class dense_set;

} // namespace entt

#endif
