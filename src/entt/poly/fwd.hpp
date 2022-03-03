#ifndef ENTT_POLY_FWD_HPP
#define ENTT_POLY_FWD_HPP

// IWYU pragma: begin_exports
#include <cstdint>
#include <type_traits>
// IWYU pragma: end_exports

namespace entt {

template<typename, std::size_t Len = sizeof(double[2]), std::size_t = alignof(typename std::aligned_storage_t<Len + !Len>)>
class basic_poly;

/**
 * @brief Alias declaration for the most common use case.
 * @tparam Concept Concept descriptor.
 */
template<typename Concept>
using poly = basic_poly<Concept>;

} // namespace entt

#endif
