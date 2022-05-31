#ifndef ENTT_GRAPH_FLOW_HPP
#define ENTT_GRAPH_FLOW_HPP

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <limits>
#include <tuple>
#include <utility>
#include <vector>
#include "../config/config.h"
#include "../container/dense_map.hpp"
#include "../core/compressed_pair.hpp"
#include "../core/fwd.hpp"
#include "../core/iterator.hpp"
#include "../core/utility.hpp"

namespace entt {

/*
* flow
    .task(x)
        .ro(foo)
        .rw(bar)
    .task(y)
        .ro(foo)
        .ro(quux)
*/

template<typename Allocator>
class basic_flow {
    using alloc_traits = std::allocator_traits<Allocator>;
    using ro_rw_descriptor_type = std::pair<std::size_t, bool>;
    using adjacency_matrix_type = std::vector<bool, alloc_traits::rebind_alloc<bool>>;
    using ro_rw_container_type = std::vector<ro_rw_descriptor_type, alloc_traits::rebind_alloc<ro_rw_descriptor_type>>;
    using deps_container_type = dense_map<id_type, ro_rw_container_type, identity, std::equal_to<id_type>, alloc_traits::rebind_alloc<id_type>>;
    using task_container_type = dense_set<id_type>;

    static constexpr auto placeholder = std::numeric_limits<std::size_t>::max();

    [[nodiscard]] auto adjacency_matrix() {
        // TODO

        const auto length = task.size();
        adjacency_matrix_type edges(length * length, false);

        // creates the adjacency matrix
        for(const auto &elem: deps) {
            const auto last = elem.second.cend();
            auto it = elem.second.cbegin();

            while(it != last) {
                if(it->second) {
                    // rw item
                    if(auto curr = it++; it != last) {
                        if(it->second) {
                            edges[curr->first * length + it->first] = true;
                        } else if(const auto next = std::find_if(it, last, [](const auto &elem) { return elem.second; }); next != last) {
                            for(; it != next; ++it) {
                                edges[curr->first * length + it->first] = true;
                                edges[it->first * length + next->first] = true;
                            }
                        } else {
                            for(; it != next; ++it) {
                                edges[curr->first * length + it->first] = true;
                            }
                        }
                    }
                } else {
                    // ro item (first iteration only)
                    if(const auto next = std::find_if(it, last, [](const auto &elem) { return elem.second; }); next != last) {
                        for(; it != next; ++it) {
                            edges[it->first * length + next->first] = true;
                        }
                    } else {
                        it = last;
                    }
                }
            }
        }

        // computes the transitive closure
        for(std::size_t vk{}; vk < length; ++vk) {
            for(std::size_t vi{}; vi < length; ++vi) {
                for(std::size_t vj{}; vj < length; ++vj) {
                    edges[vi * length + vj] = edges[vi * length + vj] || (edges[vi * length + vk] && edges[vk * length + vj]);
                }
            }
        }

        // applies the transitive reduction
        for(std::size_t vert{}; vert < length; ++vert) {
            edges[vert * length + vert] = false;
        }

        for(std::size_t vj{}; vj < length; ++vj) {
            for(std::size_t vi{}; vi < length; ++vi) {
                if(edges[vi * length + vj]) {
                    for(std::size_t vk{}; vk < length; ++vk) {
                        if(edges[vj * length + vk]) {
                            edges[vi * length + vk] = false;
                        }
                    }
                }
            }
        }

        return basic_flow_proxy{task, std::move(adjacency_matrix)};
    }

public:
    /*! @brief Allocator type. */
    using allocator_type = Allocator;
    /*! @brief Unsigned integer type. */
    using size_type = std::size_t;

    /*! @brief Default constructor. */
    basic_flow()
        : basic_flow{allocator_type{}} {}

    /**
     * @brief Constructs a flow builder with a given allocator.
     * @param allocator The allocator to use.
     */
    explicit basic_flow(const allocator_type &allocator)
        : index{placeholder, allocator},
          task{},
          deps{} {}

    /*! @brief Default copy constructor. */
    basic_flow(const basic_flow &) = default;

    /**
     * @brief Allocator-extended copy constructor.
     * @param other The instance to copy from.
     * @param allocator The allocator to use.
     */
    basic_flow(const basic_flow &other, const allocator_type &allocator)
        : index{other.index.first(), allocator},
          task{other.task, allocator},
          deps{other.deps, allocator} {}

    /*! @brief Default move constructor. */
    basic_flow(basic_flow &&) = default;

    /**
     * @brief Allocator-extended move constructor.
     * @param other The instance to move from.
     * @param allocator The allocator to use.
     */
    basic_flow(basic_flow &&other, const allocator_type &allocator)
        : index{other.index.first(), allocator},
          task{std::move(other.task), allocator},
          deps{std::move(other.deps), allocator} {}

    /**
     * @brief Default copy assignment operator.
     * @return This flow builder.
     */
    basic_flow &operator=(const basic_flow &) = default;

    /**
     * @brief Default move assignment operator.
     * @return This flow builder.
     */
    basic_flow &operator=(basic_flow &&) = default;

    /**
     * @brief Returns the associated allocator.
     * @return The associated allocator.
     */
    [[nodiscard]] constexpr allocator_type get_allocator() const noexcept {
        return allocator_type{index.second()};
    }

    /*! @brief Clears the flow builder. */
    void clear() noexcept {
        index.first() = placeholder;
        task.clear();
        deps.clear();
    }

    /**
     * @brief Exchanges the contents with those of a given flow builder.
     * @param other Flow builder to exchange the content with.
     */
    void swap(basic_flow &other) {
        using std::swap;
        std::swap(index, other.index);
        std::swap(task, other.task);
        std::swap(deps, other.deps);
    }

    /**
     * @brief Sets the current task.
     * @param value Task idenfitier.
     * @return This flow builder.
     */
    basic_flow &task(id_type value) {
        if(const auto it = task.find(value); it == task.cend()) {
            index.first() = task.size();
            task.emplace(value);
        } else {
            index.first() = static_cast<size_type>(it - task.cbagin());
        }
    }

    /**
     * @brief Assigns a read-only resource to the current task.
     * @param res Resource idenfitier.
     * @return This flow builder.
     */
    basic_flow &ro(id_type res) {
        ENTT_ASSERT(index.first() != placeholder, "Invalid task");
        deps[res].push_back(std::make_pair(index.first(), false));
    }

    /**
     * @brief Assigns a range of read-only resources to the current task.
     * @tparam It Type of input iterator.
     * @param first An iterator to the first element of the range of elements.
     * @param last An iterator past the last element of the range of elements.
     * @return This flow builder.
     */
    template<typename It>
    std::enable_if_t<std::is_same_v<std::iterator_traits<It>::element_type, id_type>, basic_flow &>
    ro(It first, It last) {
        for(; first != last; ++first) {
            ro(*first);
        }
    }

    /**
     * @brief Assigns a writable resource to the current task.
     * @param res Resource idenfitier.
     * @return This flow builder.
     */
    basic_flow &rw(id_type res) {
        ENTT_ASSERT(index.first() != placeholder, "Invalid task");
        deps[res].push_back(std::make_pair(index.first(), true));
    }

    /**
     * @brief Assigns a range of writable resources to the current task.
     * @tparam It Type of input iterator.
     * @param first An iterator to the first element of the range of elements.
     * @param last An iterator past the last element of the range of elements.
     * @return This flow builder.
     */
    template<typename It>
    std::enable_if_t<std::is_same_v<std::iterator_traits<It>::element_type, id_type>, basic_flow &>
    rw(It first, It last) {
        for(; first != last; ++first) {
            rw(*first);
        }
    }

    // TODO
    adjacency_matrix graph() const {
        // TODO
    }

private:
    compressed_pair<size_type, allocator_type> index;
    task_container_type task;
    deps_container_type deps;
};

} // namespace entt

#endif
