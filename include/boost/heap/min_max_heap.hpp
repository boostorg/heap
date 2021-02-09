// // boost heap: min-max heap
//
// The majority of this file comes from d_ary_heap.hpp
// Copyright (C) 2010 Tim Blechmann
//
// The parts related to the implementation of the min-max heap
// are however new.
// Copyright (C) 2019 Grégoire Scano
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

/* Implementation of
   @article{Atkinson:1986:MHG:6617.6621,
   author = {Atkinson, M. D. and Sack, J.-R. and Santoro, N. and Strothotte, T.},
   title = {Min-max Heaps and Generalized Priority Queues},
   journal = {Commun. ACM},
   issue_date = {Oct. 1986},
   volume = {29},
   number = {10},
   month = {oct},
   year = {1986},
   issn = {0001-0782},
   pages = {996--1000},
   numpages = {5},
   url = {http://doi.acm.org/10.1145/6617.6621},
   doi = {http://dx.doi.org/10.1145/6617.6621},
   acmid = {6621},
   publisher = {ACM},
   address = {New York, NY, USA}
   }
*/

#ifndef BOOST_HEAP_MIN_MAX_HEAP_HPP
#define BOOST_HEAP_MIN_MAX_HEAP_HPP

#include <vector>
#include <cstring> // memset

#include <boost/assert.hpp>
#include <boost/config.hpp>

#include <boost/heap/policies.hpp>
#include <boost/heap/detail/heap_comparison.hpp>
#include <boost/heap/detail/ilog2.hpp>
#include <boost/heap/detail/mutable_heap.hpp>
#include <boost/heap/detail/ordered_adaptor_iterator.hpp>
#include <boost/heap/detail/stable_heap.hpp>

#ifdef BOOST_HAS_PRAGMA_ONCE
#pragma once
#endif

#ifndef BOOST_DOXYGEN_INVOKED
#ifdef BOOST_HEAP_SANITYCHECKS
#define BOOST_HEAP_ASSERT BOOST_ASSERT
#else
#define BOOST_HEAP_ASSERT(expression)
#endif
#endif

namespace boost  {
namespace heap   {
namespace detail {

template <unsigned int Base, typename IntType>
struct tree_depth;

template <unsigned int Base, typename IntType>
struct min_max_ordered_iterator_status;

typedef parameter::parameters<boost::parameter::optional<tag::arity>,
                              boost::parameter::optional<tag::allocator>,
                              boost::parameter::optional<tag::compare>,
                              boost::parameter::optional<tag::stable>,
                              boost::parameter::optional<tag::stability_counter_type>
                              > min_max_heap_signature;

/* base class for min-max heap */
template <typename T,
          class BoundArgs,
          class IndexUpdater>
class min_max_heap:
    private make_heap_base<T, BoundArgs, false>::type
{
    typedef make_heap_base<T, BoundArgs, false> heap_base_maker;

    typedef typename heap_base_maker::type super_t;
    typedef typename super_t::internal_type internal_type;

	typedef typename boost::allocator_rebind<typename heap_base_maker::allocator_argument, internal_type>::type internal_type_allocator;
    typedef std::vector<internal_type, internal_type_allocator> container_type;

    typedef IndexUpdater index_updater;
  
    container_type q_;

    static const unsigned int D = parameter::binding<BoundArgs, tag::arity, mpl::int_<2> >::type::value;

    template <typename Heap1, typename Heap2>
    friend struct heap_merge_emulate;

public:
    typedef T value_type;

    struct implementation_defined: extract_allocator_types<typename heap_base_maker::allocator_argument>
    {};

    typedef typename implementation_defined::size_type size_type;
    typedef typename implementation_defined::difference_type difference_type;
    typedef typename implementation_defined::reference reference;
    typedef typename implementation_defined::const_reference const_reference;
    typedef typename implementation_defined::pointer pointer;
    typedef typename implementation_defined::const_pointer const_pointer;

    typedef typename heap_base_maker::compare_argument value_compare;
    typedef typename heap_base_maker::allocator_argument allocator_type;

    typedef void * handle_type;

    static const bool is_stable = extract_stable<BoundArgs>::value;

    /* xtors */
public:
    explicit min_max_heap(const value_compare & cmp = value_compare()) :
        super_t(cmp)
    {}

    min_max_heap(const min_max_heap & rhs) :
        super_t(rhs), q_(rhs.q_)
    {}

#ifndef BOOST_NO_CXX11_RVALUE_REFERENCES
    min_max_heap(min_max_heap && rhs) :
        super_t(std::move(rhs)), q_(std::move(rhs.q_))
    {}

    min_max_heap & operator = (min_max_heap && rhs)
    {
        super_t::operator = (std::move(rhs));
        q_ = std::move(rhs.q_);
        return *this;
    }
#endif

    min_max_heap & operator = (min_max_heap const & rhs)
    {
        static_cast<super_t &>(*this) = static_cast<super_t const &>(rhs);
        q_ = rhs.q_;
        return *this;
    }

    void swap(min_max_heap & rhs)
    {
        super_t::swap(rhs);
        std::swap(q_, rhs.q_);
    }
    /* xtors */

    /* allocator */
    allocator_type get_allocator(void) const
    {
        return q_.get_allocator();
    }
    /* allocator */

    /* compare */
    value_compare const & value_comp(void) const
    {
        return super_t::value_comp();
    }

    template <bool Regular>
    bool compare(size_type i, size_type j) const
    {
        BOOST_ASSERT(i < this->size());
        BOOST_ASSERT(j < this->size());
        
        if (Regular)
            return super_t::operator () (q_[i], q_[j]);
        else
            return super_t::operator () (q_[j], q_[i]);
    }
    /* compare */

    /* container */
    bool empty(void) const
    {
        return q_.empty();
    }

    size_type size(void) const
    {
        return q_.size();
    }

    size_type max_size(void) const
    {
        return q_.max_size();
    }

    void reserve(size_t size)
    {
        q_.reserve(size);
    }

    void clear(void)
    {
        q_.clear();
    }
    /* container */

    /* indexes */
    void reset_index(size_type index, size_type new_index)
    {
        BOOST_HEAP_ASSERT(index < q_.size());
        index_updater::run(q_[index], new_index);
    }

    bool is_on_compare_level(size_type index) const
    {
        tree_depth<D, size_type> depth;
        return !(depth(index) % 2);
    }

    size_type root(void) const
    {
        return 0;
    }

    size_type first_child(size_type index) const
    {
        return D * index + 1;
    }

    size_type last_child(size_type index) const
    {
        return D * (index + 1);
    }

    std::pair<size_type, size_type> children(size_type index) const
    {
        const size_type child = first_child(index);
        return std::make_pair(child, child + D - 1);
    }

    size_type first_grandchild(size_type index) const
    {
        return D * D * index + D + 1;
    }

    size_type last_grandchild(size_type index) const
    {
        return D * D * index + D * (D + 1);
    }

    std::pair<size_type, size_type> grandchildren(size_type index) const
    {
        const size_type grandchild = first_grandchild(index);
        return std::make_pair(grandchild, grandchild + D * D - 1);
    }

    size_type last(void) const
    {
        return q_.size() - 1;
    }

    size_type npos(void) const
    {
        return -1;
    }

    bool is_leaf(size_type index) const
    {
        return q_.size() <= first_child(index);
    }

    bool has_parent(size_type index) const
    {
        return index != root();
    }

    size_type parent(size_type index) const
    {
        if (index == root() || index == npos())
            return npos();
        else
            return (index - 1) / D;
    }

    size_type grandparent(size_type index) const
    {
        return parent(parent(index));
    }

    template <bool Regular>
    bool best_between(size_type & best, size_type current, size_type theorical_last) const
    {
        bool found = false;

        for (const size_type last = std::min(theorical_last, this->last()); current <= last; ++current)
            if (compare<Regular>(current, best)) {
                best = current;
                found = true;
            }

        return found;
    }

    template <bool Regular>
    size_type best_child_or_grandchild(size_type index, bool & is_grandchild) const
    {
        const std::pair<size_type, size_type> children = this->children(index);

        if(last() < children.first) return npos();

        const std::pair<size_type, size_type> grandchildren = this->grandchildren(index);

        size_type best = children.first;

        best_between<Regular>(best, children.first + 1, children.second);
        is_grandchild = best_between<Regular>(best, grandchildren.first, grandchildren.second);

        return best;
    }
    /* indexes */

    /* moves */
    void trickle_down(size_type i)
    {
        if (is_on_compare_level(i))
            trickle_down_impl<false>(i);
        else
            trickle_down_impl<true>(i);
    }

    template <bool Regular>
    void trickle_down_impl(size_type i)
    {
        bool is_grandchild;
        const size_type m = best_child_or_grandchild<Regular>(i, is_grandchild);

        if (m < npos()) {
            if (is_grandchild) {
                if (compare<Regular>(m, i)) {
                    swap(i, m);

                    const size_type parent = this->parent(m);

                    if (compare<Regular>(parent, m))
                        swap(m, parent);

                    trickle_down_impl<Regular>(m);
                }
            }
            else if (compare<Regular>(m, i))
                swap(i, m);
        }
    }

    void bubble_up(size_type i)
    {
        if (is_on_compare_level(i))
            bubble_up_impl<false>(i);
        else
            bubble_up_impl<true>(i);
    }

    template <bool Regular>
    void bubble_up_impl(size_type i)
    {
        const size_type parent = this->parent(i);

        if (parent != npos()) {
            if (compare<Regular>(parent, i)) {
                swap(i, parent);
                bubble_up_impl_<!Regular>(parent);
            }
            else
                bubble_up_impl_<Regular>(i);
        }
    }

    template <bool Regular>
    void bubble_up_impl_(size_type i)
    {
        const size_type grandparent = this->grandparent(i);

        if (grandparent != npos() && compare<Regular>(i, grandparent)) {
            swap(i, grandparent);
            bubble_up_impl_<Regular>(grandparent);
        }
    }
    /* moves */

    /* operations */
    void swap(size_type i, size_type j)
    {
        BOOST_ASSERT(i < size());
        BOOST_ASSERT(j < size());

        reset_index(i, j);
        reset_index(j, i);

        std::swap(q_[i], q_[j]);
    }

protected:
    size_type index_of_max(void) const
    {
        return root();
    }

    size_type index_of_min(void) const
    {
        size_type best = root();

        best_between<true>(best, 1, D);

        return best;
    }
    /* operations */

    /* interface */
    void push(const value_type & v)
    {
        q_.push_back(super_t::make_node(v));

        const size_type index = last();
        reset_index(index, index);

        bubble_up(index);
    }

#if !defined(BOOST_NO_CXX11_RVALUE_REFERENCES) && !defined(BOOST_NO_CXX11_VARIADIC_TEMPLATES)
    template <class... Args>
    void emplace(Args&&... args)
    {
        q_.emplace_back(super_t::make_node(std::forward<Args>(args)...));
        reset_index(last(), last());
        bubble_up(last());
    }
#endif

    value_type const & top(void) const
    {
        return max();
    }
    
    value_type const & min(void) const
    {
        BOOST_ASSERT(!empty());

        return super_t::get_value(q_[index_of_min()]);
    }

    value_type const & max(void) const
    {
        BOOST_ASSERT(!empty());

        return super_t::get_value(q_[index_of_max()]);
    }

    void pop(void)
    {
        pop_max();
    }       

    void pop_min(void)
    {
        erase(index_of_min());
    }

    void pop_max(void)
    {
        erase(index_of_max());
    }

public:
    template<typename U,
             typename V,
             typename W,
             typename X>
    struct rebind {
        typedef min_max_heap<U, typename min_max_heap_signature::bind<boost::heap::stable<heap_base_maker::is_stable>,
                                                                  boost::heap::stability_counter_type<typename heap_base_maker::stability_counter_type>,
                                                                  boost::heap::arity<D>,
                                                                  boost::heap::compare<V>,
                                                                  boost::heap::allocator<W>
                                                                  >::type,
                           X
                           > other;
    };

    template <class U> friend class priority_queue_mutable_wrapper;
    template <class U> friend class double_ended_priority_queue_mutable_wrapper;
  
    void update(size_type index)
    {
        bubble_up(index);
        trickle_down(index);
    }

    void increase(size_type index)
    {
        update(index);
    }

    void decrease(size_type index)
    {
        update(index);
    }

    void erase(size_type index)
    {
        BOOST_ASSERT(!empty());
        BOOST_ASSERT(index < size());

        swap(index, last());
        q_.pop_back();

        if (!empty() && index != size())
            update(index);
    }
    /* interface */

    /* iterators */
public:
    typedef detail::stable_heap_iterator<const value_type, typename container_type::const_iterator, super_t> iterator;
    typedef iterator const_iterator;

public:
    iterator begin(void)
    {
      return iterator(q_.begin());
    }

    iterator end(void)
    {
      return iterator(q_.end());
    }

    const_iterator begin(void) const
    {
        return const_iterator(q_.begin());
    }

    const_iterator end(void) const
    {
      return const_iterator(q_.end());
    }

public:
    template<bool Forward>
    struct iterator_dispatcher
    {
        iterator_dispatcher(size_type max_index = 0) :
            status(max_index)
        {}

        min_max_ordered_iterator_status<D, size_type> status;

        static size_type max_index(const min_max_heap * heap)
        {
            return heap->last();
        }

        std::pair<size_type, size_type> get_child_nodes(const min_max_heap * heap, size_type index, std::pair<size_type, size_type> & extra_child_nodes)
        {
            /* As stated in the article, the Hasse diagram is divided in two parts.
             * The first one consists of even levels and can be explored like a
             * regular binary tree except that the number of children of a node
             * is D^2 instead of D because odd levels are skipped.
             * The second part consists of odd levels and is a bit more complicated
             * to explore. The search has to go back up in the tree from the leaves
             * but since a node on an odd level is being pointed to by D^2 grandchildren
             * in the Hasse diagram, it cannot be visited until all of its heirs have
             * previously been visited.
             *
             * The 'min_max_ordered_iterator_status' structure is used to keep track
             * of this. It indicates for each node on an odd level whether its heirs
             * have been visited. When the last heir is being visited, it adds the
             * node to the potential candidates to be visited next. Furthermore, when
             * this happens, the markers for its heirs are reset and will then be
             * reused to indicate to its own grandfather that it has been visited while
             * its siblings may not have yet been visited.
             *
             * This method requires $O(\frac{(D - 1) * (size() - 1) + 1}{D})$ bytes.
             *
             * The following specific cases must be addressed (D = 3):
             *         0        1) when 0 is visited, it must add nodes 4-8 to the list
             *        /|\          of potential candidates to be visited next, as well
             *       / | \         as node 3. This explains the 'extra_child_nodes' as
             *      /  |  \        node denoted 4-8 and 3 might not be consecutive in a
             *     /   |   \       larger tree where the example would be a subtree.
             *    /    |    \   2) when 8 is visited, it must set its indicator and
             *   1     2     3     set the indicator for the non existing node 9 (in
             *  /|\   /|           general for all its right non existing siblings) and
             * 4 5 6 7 8           then add 2 if 7 has already been visited.
            */
            const size_type last = heap->last();
            const bool on_compare_level = !(Forward ^ heap->is_on_compare_level(index));

            if (on_compare_level) {
                std::pair<size_type, size_type> children = heap->children(index);

                if (children.first <= last) {
                    std::pair<size_type, size_type> grandchildren = heap->grandchildren(index);

                    if (grandchildren.first <= last) {
                        if (last < grandchildren.second) {
                            grandchildren.second = last;

                            extra_child_nodes.first = heap->parent(grandchildren.second) + 1;
                            extra_child_nodes.second = children.second;
                        }

                        return grandchildren;
                    }

                    children.second = std::min(children.second, last);

                    return children;
                }
            }// else is leaf or not on compare level

            status.set(index);
            const size_type parent = heap->parent(index);

            if (BOOST_LIKELY(parent != heap->npos())) {
                const size_type rightmost_sibling = heap->last_child(parent);

                // if (last < rightmost_sibling)
                for(size_type i = last + 1; i <= rightmost_sibling; ++i)
                    status.set(i);

                if (on_compare_level) {
                    if(status.is_complete(parent)) {
                        status.reset(parent);
                        return std::make_pair(parent, parent);
                    }
                }
                else {
                    const size_type grandparent = heap->parent(parent);

                    if (BOOST_LIKELY(grandparent != heap->npos())
                        && status.is_complete(grandparent)) {
                        status.reset(grandparent);
                        return std::make_pair(grandparent, grandparent);
                    }
                }
            }

            return std::make_pair(1, 0);
        }

        static internal_type const & get_internal_value(const min_max_heap * heap, size_type index)
        {
            return heap->q_[index];
        }

        static value_type const & get_value(internal_type const & arg)
        {
            return super_t::get_value(arg);
        }
    };

public:
    struct ordered_iterator_dispatcher : iterator_dispatcher<true>
    {
        ordered_iterator_dispatcher(size_type max):
            iterator_dispatcher<true>(max)
        {}

        static bool is_leaf(const min_max_heap * heap, size_type index)
        {
            return (heap->root() < index && index <= D) || index == heap->last() + 1;
        }
    };

public:
    typedef detail::extended_ordered_adaptor_iterator<const value_type,
                                                      internal_type,
                                                      min_max_heap,
                                                      allocator_type,
                                                      typename super_t::internal_compare,
                                                      ordered_iterator_dispatcher>
    ordered_iterator;

public:
    ordered_iterator ordered_begin(void) const
    {
        return ordered_iterator(root(), this, super_t::get_internal_cmp(), ordered_iterator_dispatcher(size()));
    }

    ordered_iterator ordered_end(void) const
    {
        return ordered_iterator(size(), this, super_t::get_internal_cmp(), ordered_iterator_dispatcher(root()));
    }

public:
    struct reverse_ordered_iterator_dispatcher : iterator_dispatcher<false>
    {
        reverse_ordered_iterator_dispatcher(size_type max) :
            iterator_dispatcher<false>(max)
        {}

        static bool is_leaf(const min_max_heap * heap, size_type index)
        {
            return index == heap->root() || index == heap->last() + 1;
        }
    };

public:
    struct reverse_internal_compare : super_t::internal_compare
    {
        reverse_internal_compare(value_compare const & cmp = value_compare()) :
            super_t::internal_compare(cmp)
        {}

        bool operator () (typename super_t::internal_type const & lhs, typename super_t::internal_type const & rhs) const
        {
            return super_t::internal_compare::operator () (rhs, lhs);
        }
      };
    
public:
    typedef detail::extended_ordered_adaptor_iterator<const value_type,
                                                      internal_type,
                                                      min_max_heap,
                                                      allocator_type,
                                                      reverse_internal_compare,
                                                      reverse_ordered_iterator_dispatcher>
    reverse_ordered_iterator;

public:
    reverse_ordered_iterator reverse_ordered_begin(void) const
    {
        size_type index_of_min = root();
        std::pair<size_type, size_type> initial_indexes = std::make_pair(1, 0);

        if (1 < size()) {
            index_of_min = this->index_of_min();
            // The initial_indexes range will contain index_of_min and this is fine
            // as long as the adaptor is storing upcoming indexes in a set.
            initial_indexes.first = 1;
            initial_indexes.second = std::min<size_type>(D, last());
        }

        return reverse_ordered_iterator(index_of_min, initial_indexes, this, reverse_internal_compare(super_t::get_internal_cmp()), reverse_ordered_iterator_dispatcher(size()));
    }

    reverse_ordered_iterator reverse_ordered_end(void) const
    {
        return reverse_ordered_iterator(size(), this, reverse_internal_compare(super_t::get_internal_cmp()), reverse_ordered_iterator_dispatcher(0));
    }
    /* iterators */
};

template <unsigned int Base, typename IntType>
struct tree_depth
{
    IntType operator () (IntType index) const
    {
        IntType power = Base;
        IntType count = 1;
        IntType depth = 0;

        while (count <= index) {
            count += power;
            power *= Base;
            ++depth;
        }

        return depth;
    }

    /* Alternatively, let f be a function mapping an index n to its corresponding
     * depth (or row) r in a D tree, f_D(n)=r and 1 < D. If n is on row r, then
     * $\sum_{i=0}^{r} D^{i} <= n < \sum_{i=0}^{r+1} D^{i}$, hence
     * $D^{r+1} <= (D-1) * n + 1 < D^{r+2}$ and since log_D is strictly increasing
     * $r + 1 <= log_D((D-1) * n + 1) < r + 2$ and then
     * because an array index is an integer starting at 0 (r:=r-1);
     * $r = log_D((D - 1) * index + 1)$
     * which is slower than the above iterative method for indexes up to 10^10.
     */
};

template <typename IntType>
struct tree_depth<2, IntType>
{
    IntType operator () (IntType index) const
    {
        return ::boost::heap::log2(index + 1);
    }
};

template <unsigned int Base, typename IntType>
struct ipower
{
    ipower(IntType max)
    {
        if (1 <= max) {
            power.resize(max + 1);
            power[0] = 1;

            for (IntType exp = 1; exp <= max; ++exp) {
                power[exp] = power[exp-1] * Base;
            }
        }
    }

    std::vector<IntType> power;

    IntType operator () (IntType exp) const
    {
        return power[exp];
    }

    static IntType pow(IntType exp, IntType res = 1)
    {
        return exp == 0 ? res : pow(exp - 1, res * Base);
    }
};

template <typename IntType>
struct ipower<2, IntType>
{
    ipower(IntType) {}

    IntType operator () (IntType exp) const
    {
        return 1 << exp;
    }

    static IntType pow(IntType exp)
    {
        return 1 << exp;
    }
};

template <unsigned int Base, typename IntType>
struct min_max_ordered_iterator_status_base
{
    min_max_ordered_iterator_status_base(IntType max_index = 0) :
        max_depth(boost::heap::detail::tree_depth<Base, IntType>()(max_index)),
        power(max_depth)
    {
      candidates.resize(1 + (power.pow(max_depth) + 1) / 8, 0);
    }

    const IntType max_depth;
    const ipower<Base, IntType> power;
    std::vector<uint8_t> candidates;

    IntType number_of_final_heirs_for(IntType current_depth) const
    {
        return power(max_depth - current_depth);
    }

    void positions(IntType index, IntType & chunk, IntType & offset, IntType & heirs)
    {
        IntType depth = boost::heap::detail::tree_depth<Base, IntType>()(index);

        const IntType local_index = index - (power(depth) - 1)/(Base - 1);

        heirs = number_of_final_heirs_for(depth);

        const IntType candidate_index = local_index * heirs;

        chunk  = candidate_index / 8;
        offset = candidate_index % 8;
    }

    void positions_by_8(IntType index, IntType & chunk, IntType & offset, IntType & heirs_oct, IntType & heirs_left)
    {
        IntType heirs;
        positions(index, chunk, offset, heirs);

        heirs_oct = heirs / 8;
        heirs_left = heirs % 8;
    }
};

template <unsigned int Base, typename IntType>
struct min_max_ordered_iterator_status : min_max_ordered_iterator_status_base<Base, IntType>
{
    typedef min_max_ordered_iterator_status_base<Base, IntType> base;

    min_max_ordered_iterator_status(IntType max_index = 0) :
        base(max_index)
    {}

    void set(IntType index)
    {
        IntType chunk, offset, heirs;
        base::positions(index, chunk, offset, heirs);

        const IntType first_heirs = std::min(heirs, 8 - offset);
        if (first_heirs < 8) {
            base::candidates[chunk] |= (0xFF >> (offset + (8 - offset - first_heirs))) << (8 - offset - first_heirs);
            ++chunk;
            heirs -= first_heirs;
        }

        const IntType heirs_octuple = heirs / 8;
        const IntType last_heirs = heirs % 8;

        std::memset(base::candidates.data() + chunk, 0xFF, heirs_octuple);
        chunk += heirs_octuple;

        base::candidates[chunk] |= 0xFF << (8 - last_heirs);
    }

    void reset(IntType index)
    {
        IntType chunk, offset, heirs;
        base::positions(index, chunk, offset, heirs);

        const IntType first_heirs = std::min(heirs, 8 - offset);
        if (first_heirs < 8) {
            base::candidates[chunk] &= ~((0xFF >> (offset + (8 - offset - first_heirs))) << (8 - offset - first_heirs));
            ++chunk;
            heirs -= first_heirs;
        }

        const IntType heirs_octuple = heirs / 8;
        const IntType last_heirs = heirs % 8;

        std::memset(base::candidates.data() + chunk, 0, heirs_octuple);
        chunk += heirs_octuple;

        base::candidates[chunk] &= ~(0xFF << (8 - last_heirs));
    }

    bool is_complete(IntType index)
    {
        IntType chunk, offset, heirs;
        base::positions(index, chunk, offset, heirs);

        const IntType first_heirs = std::min(heirs, 8 - offset);
        if (first_heirs < 8) {
            IntType mask = (0xFF >> (offset + (8 - offset - first_heirs))) << (8 - offset - first_heirs);
            if((base::candidates[chunk] & mask) != mask) return false;
            ++chunk;
            heirs -= first_heirs;
        }

        while (8 <= heirs) {
            if (base::candidates[chunk] != 0xFF)
                return false;
            ++chunk;
            heirs -= 8;
        }

        uint8_t mask = 0xFF << (8 - heirs);
        return (heirs && (base::candidates[chunk] & mask) == mask) || !heirs;
    }
};

template <typename IntType>
struct min_max_ordered_iterator_status<2, IntType> : min_max_ordered_iterator_status_base<2, IntType>
{
    typedef min_max_ordered_iterator_status_base<2, IntType> base;

    min_max_ordered_iterator_status(IntType max_index = 0) :
        base(max_index)
#ifndef BOOST_NO_CXX11_UNIFIED_INITIALIZATION_SYNTAX
        ,masks{0, 0x01, 0x03, 0, 0x0F, 0, 0, 0} {}
    const
#else
    {
        std::memset(masks, 0, 8);
        masks[1] = 0x01;
        masks[2] = 0x03;
        masks[4] = 0x0F;
    }
#endif

    uint8_t masks[8];

    void set(IntType index)
    {
        IntType chunk, offset, heirs_octuple, heirs_left;
        base::positions_by_8(index, chunk, offset, heirs_octuple, heirs_left);

        if (0 < heirs_octuple)
          std::memset(base::candidates.data() + chunk, 0xFF, heirs_octuple);
        else
          base::candidates[chunk] |= masks[heirs_left] << (8 - heirs_left - offset);
    }

    void reset(IntType index)
    {
        IntType chunk, offset, heirs_octuple, heirs_left;
        base::positions_by_8(index, chunk, offset, heirs_octuple, heirs_left);

        if (0 < heirs_octuple)
          std::memset(base::candidates.data() + chunk, 0, heirs_octuple);
        else
          base::candidates[chunk] &= ~(masks[heirs_left] << (8 - heirs_left - offset));
    }

    bool is_complete(IntType index)
    {
        IntType chunk, offset, heirs;
        base::positions(index, chunk, offset, heirs);

        if (8 <= heirs) {
          do {
            if (base::candidates[chunk] != 0xFF)
                return false;
            ++chunk;
            heirs -= 8;
          }
          while (8 <= heirs);

          return true;
        }
        else {
          const uint8_t mask = masks[heirs] << (8 - heirs - offset);
          return (mask && (base::candidates[chunk] & mask) == mask) || !mask;
        }
    }
};

template <typename T, typename BoundArgs>
struct select_minmax_heap
{
    static const bool is_mutable = extract_mutable<BoundArgs>::value;

    typedef typename mpl::if_c<is_mutable,
                               double_ended_priority_queue_mutable_wrapper<min_max_heap<T, BoundArgs, nop_index_updater> >,
                               min_max_heap<T, BoundArgs, nop_index_updater>
                               >::type type;
};

} /* namespace detail */

/**
 * \class min_max_heap
 * \brief min-max heap class
 *
 * This class implements a double-ended priority queue. Internally, the min-max heap is represented
 * as a dynamically sized array (std::vector), that directly stores the values.
 *
 * The template parameter T is the type to be managed by the container.
 * The user can specify additional options and if no options are provided default options are used.
 *
 * The container supports the following options:
 * - \c boost::heap::arity<>, defaults to \c arity<2>
 * - \c boost::heap::compare<>, defaults to \c compare<std::less<T> >
 * - \c boost::heap::stable<>, defaults to \c stable<false>
 * - \c boost::heap::stability_counter_type<>, defaults to \c stability_counter_type<boost::uintmax_t>
 * - \c boost::heap::allocator<>, defaults to \c allocator<std::allocator<T> >
 * - \c boost::heap::mutable_<>, defaults to \c mutable_<false>
 */
#ifdef BOOST_DOXYGEN_INVOKED
template<class T, class ...Options>
#else
template <typename T,
          class A0 = boost::parameter::void_,
          class A1 = boost::parameter::void_,
          class A2 = boost::parameter::void_,
          class A3 = boost::parameter::void_,
          class A4 = boost::parameter::void_,
          class A5 = boost::parameter::void_
          >
#endif
class min_max_heap:
    public detail::select_minmax_heap<T, typename detail::min_max_heap_signature::bind<A0, A1, A2, A3, A4, A5>::type>::type
{
    typedef typename detail::min_max_heap_signature::bind<A0, A1, A2, A3, A4, A5>::type bound_args;
    typedef typename detail::select_minmax_heap<T, bound_args>::type super_t;

    template <typename Heap1, typename Heap2>
    friend struct heap_merge_emulate;

#ifndef BOOST_DOXYGEN_INVOKED
    static const bool is_mutable = detail::extract_mutable<bound_args>::value;

#define BOOST_HEAP_TYPEDEF_FROM_SUPER_T(NAME)   \
    typedef typename super_t::NAME NAME;

    struct implementation_defined
    {
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(size_type)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(difference_type)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(value_compare)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(allocator_type)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(reference)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(const_reference)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(pointer)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(const_pointer)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(iterator)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(const_iterator)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(ordered_iterator)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(reverse_ordered_iterator)
        BOOST_HEAP_TYPEDEF_FROM_SUPER_T(handle_type)
    };
#undef BOOST_HEAP_TYPEDEF_FROM_SUPER_T

#endif
public:
    static const bool constant_time_size = true;
    static const bool has_ordered_iterators = true;
    static const bool is_mergable = false;
    static const bool has_reserve = true;
    static const bool is_stable = super_t::is_stable;

    typedef T value_type;
    typedef typename implementation_defined::size_type size_type;
    typedef typename implementation_defined::difference_type difference_type;
    typedef typename implementation_defined::value_compare value_compare;
    typedef typename implementation_defined::allocator_type allocator_type;
    typedef typename implementation_defined::reference reference;
    typedef typename implementation_defined::const_reference const_reference;
    typedef typename implementation_defined::pointer pointer;
    typedef typename implementation_defined::const_pointer const_pointer;
    /// \copydoc boost::heap::priority_queue::iterator
    typedef typename implementation_defined::iterator iterator;
    typedef typename implementation_defined::const_iterator const_iterator;
    typedef typename implementation_defined::ordered_iterator ordered_iterator;
    typedef typename implementation_defined::reverse_ordered_iterator reverse_ordered_iterator;
    typedef typename implementation_defined::handle_type handle_type;

public:
    /// \copydoc boost::heap::priority_queue::priority_queue(value_compare const &)
    explicit min_max_heap(value_compare const & cmp = value_compare()):
        super_t(cmp)
    {}

    /// \copydoc boost::heap::priority_queue::priority_queue(priority_queue const &)
    min_max_heap(min_max_heap const & rhs):
        super_t(rhs)
    {}

#ifndef BOOST_NO_CXX11_RVALUE_REFERENCES
    /// \copydoc boost::heap::priority_queue::priority_queue(priority_queue &&)
    min_max_heap(min_max_heap && rhs):
        super_t(std::move(rhs))
    {}

    /// \copydoc boost::heap::priority_queue::operator=(priority_queue &&)
    min_max_heap & operator=(min_max_heap && rhs)
    {
        super_t::operator=(std::move(rhs));
        return *this;
    }
#endif

    /// \copydoc boost::heap::priority_queue::operator=(priority_queue const &)
    min_max_heap & operator=(min_max_heap const & rhs)
    {
        super_t::operator=(rhs);
        return *this;
    }

public:
    /// \copydoc boost::heap::priority_queue::empty
    bool empty(void) const
    {
        return super_t::empty();
    }

    /// \copydoc boost::heap::priority_queue::size
    size_type size(void) const
    {
        return super_t::size();
    }

    /// \copydoc boost::heap::priority_queue::max_size
    size_type max_size(void) const
    {
        return super_t::max_size();
    }

    /// \copydoc boost::heap::priority_queue::clear
    void clear(void)
    {
        super_t::clear();
    }

public:
    /// \copydoc boost::heap::priority_queue::get_allocator
    allocator_type get_allocator(void) const
    {
        return super_t::get_allocator();
    }

public:
    /// \copydoc boost::heap::priority_queue::top
    value_type const & top(void) const
    {
        return super_t::max();
    }

    /**
     * \b Effects: Returns a const_reference to the max element.
     *
     * \b Complexity: Constant.
     *
     * */
    value_type const & max(void) const
    {
      return super_t::max();
    }
    
    /**
     * \b Effects: Returns a const_reference to the min element.
     *
     * \b Complexity: Constant.
     *
     * */
    value_type const & min(void) const
    {
      return super_t::min();
    }

    /**
     * \b Effects: Returns a const_reference to the max element.
     *
     * \b Complexity: Constant.
     *
     * */
    value_type const & best(void) const
    {
      return super_t::max();
    }

    /**
     * \b Effects: Returns a const_reference to the min element.
     *
     * \b Complexity: Constant.
     *
     * */
    value_type const & worst(void) const
    {
      return super_t::min();
    }
    
    /**
     * \b Effects: Adds a new element to the priority queue. Returns handle to element
     *
     * \b Complexity: Logarithmic.
     *
     * */
    typename boost::conditional<is_mutable, handle_type, void>::type push(value_type const & v)
    {
        return super_t::push(v);
    }

#if !defined(BOOST_NO_CXX11_RVALUE_REFERENCES) && !defined(BOOST_NO_CXX11_VARIADIC_TEMPLATES)
    /**
     * \b Effects: Adds a new element to the priority queue. The element is directly constructed in-place. Returns handle to element.
     *
     * \b Complexity: Logarithmic.
     *
     * */
    template <class... Args>
    typename boost::conditional<is_mutable, handle_type, void>::type emplace(Args&&... args)
    {
        return super_t::emplace(std::forward<Args>(args)...);
    }
#endif

    /// \copydoc boost::heap::priority_queue::operator<(HeapType const & rhs) const
    template <typename HeapType>
    bool operator<(HeapType const & rhs) const
    {
        return detail::heap_compare(*this, rhs);
    }

    /// \copydoc boost::heap::priority_queue::operator>(HeapType const & rhs) const
    template <typename HeapType>
    bool operator>(HeapType const & rhs) const
    {
        return detail::heap_compare(rhs, *this);
    }

    /// \copydoc boost::heap::priority_queue::operator>=(HeapType const & rhs) const
    template <typename HeapType>
    bool operator>=(HeapType const & rhs) const
    {
        return !operator<(rhs);
    }

    /// \copydoc boost::heap::priority_queue::operator<=(HeapType const & rhs) const
    template <typename HeapType>
    bool operator<=(HeapType const & rhs) const
    {
        return !operator>(rhs);
    }

    /// \copydoc boost::heap::priority_queue::operator==(HeapType const & rhs) const
    template <typename HeapType>
    bool operator==(HeapType const & rhs) const
    {
        return detail::heap_equality(*this, rhs);
    }

    /// \copydoc boost::heap::priority_queue::operator!=(HeapType const & rhs) const
    template <typename HeapType>
    bool operator!=(HeapType const & rhs) const
    {
        return !(*this == rhs);
    }

    /**
     * \b Effects: Assigns \c v to the element handled by \c handle & updates the priority queue.
     *
     * \b Complexity: Logarithmic.
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    void update(handle_type handle, const_reference v)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        super_t::update(handle, v);
    }

    /**
     * \b Effects: Updates the heap after the element handled by \c handle has been changed.
     *
     * \b Complexity: Logarithmic.
     *
     * \b Note: If this is not called, after a handle has been updated, the behavior of the data structure is undefined!
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    void update(handle_type handle)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        super_t::update(handle);
    }

     /**
     * \b Effects: Assigns \c v to the element handled by \c handle & updates the priority queue.
     *
     * \b Complexity: Logarithmic.
     *
     * \b Note: The new value is expected to be greater than the current one
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    void increase(handle_type handle, const_reference v)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        super_t::increase(handle, v);
    }

    /**
     * \b Effects: Updates the heap after the element handled by \c handle has been changed.
     *
     * \b Complexity: Logarithmic.
     *
     * \b Note: The new value is expected to be greater than the current one. If this is not called, after a handle has been updated, the behavior of the data structure is undefined!
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    void increase(handle_type handle)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        super_t::increase(handle);
    }

     /**
     * \b Effects: Assigns \c v to the element handled by \c handle & updates the priority queue.
     *
     * \b Complexity: Logarithmic.
     *
     * \b Note: The new value is expected to be less than the current one
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    void decrease(handle_type handle, const_reference v)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        super_t::decrease(handle, v);
    }

    /**
     * \b Effects: Updates the heap after the element handled by \c handle has been changed.
     *
     * \b Complexity: Logarithmic.
     *
     * \b Note: The new value is expected to be less than the current one. If this is not called, after a handle has been updated, the behavior of the data structure is undefined!
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    void decrease(handle_type handle)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        super_t::decrease(handle);
    }

    /**
     * \b Effects: Removes the element handled by \c handle from the priority_queue.
     *
     * \b Complexity: Logarithmic.
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    void erase(handle_type handle)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        super_t::erase(handle);
    }

    /**
     * \b Effects: Casts an iterator to a node handle.
     *
     * \b Complexity: Constant.
     *
     * \b Requirement: data structure must be configured as mutable
     * */
    static handle_type s_handle_from_iterator(iterator const & it)
    {
        BOOST_STATIC_ASSERT(is_mutable);
        return super_t::s_handle_from_iterator(it);
    }

    /**
     * \b Effects: Removes the top element from the priority queue.
     *
     * \b Complexity: Logarithmic.
     *
     * */
    void pop(void)
    {
        super_t::pop_max();
    }

    /**
     * \b Effects: Removes the element with the highest priority from the priority queue.
     *
     * \b Complexity: Logarithmic.
     *
     * */
    void pop_max(void)
    {
      super_t::pop_max();
    }
    
    /**
     * \b Effects: Removes the element with the lowest priority from the priority queue.
     *
     * \b Complexity: Logarithmic.
     *
     * */
    void pop_min(void)
    {
      super_t::pop_min();
    }

    /// \copydoc boost::heap::priority_queue::swap
    void swap(min_max_heap & rhs)
    {
        super_t::swap(rhs);
    }

    /// \copydoc boost::heap::priority_queue::begin
    const_iterator begin(void) const
    {
        return super_t::begin();
    }

    /// \copydoc boost::heap::priority_queue::begin
    iterator begin(void)
    {
        return super_t::begin();
    }

    /// \copydoc boost::heap::priority_queue::end
    iterator end(void)
    {
        return super_t::end();
    }

    /// \copydoc boost::heap::priority_queue::end
    const_iterator end(void) const
    {
        return super_t::end();
    }

    /**
     * \b Effects: Returns an ordered iterator to the first element contained in the priority queue.
     *
     * \b Spatial complexity: Requires an additional ((D - 1) * (size() - 1) + 1/(8*D) bytes.
     *
     * \b Note: Ordered iterators traverse the priority queue in heap order.
     * */
    ordered_iterator ordered_begin(void) const
    {
        return super_t::ordered_begin();
    }

    /// \copydoc boost::heap::fibonacci_heap::ordered_end
    ordered_iterator ordered_end(void) const
    {
        return super_t::ordered_end();
    }

    /**
     * \b Effects: Returns a reverse ordered iterator to the last element contained in the priority queue.
     *
     * \b Spatial complexity: Requires an additional ((D - 1) * (size() - 1) + 1/(8*D) bytes.
     *
     * \b Note: Reverse ordered iterators traverse the priority queue in heap reverse order.
     * */
    reverse_ordered_iterator reverse_ordered_begin(void) const
    {
        return super_t::reverse_ordered_begin();
    }

    /**
     * \b Effects: Returns a reverse ordered iterator to the beginning of the priority queue.
     *
     * \b Note: Reverse ordered iterators traverse the priority queue in heap reverse order.
     * */
    reverse_ordered_iterator reverse_ordered_end(void) const
    {
        return super_t::reverse_ordered_end();
    }

    /// \copydoc boost::heap::priority_queue::reserve
    void reserve (size_type element_count)
    {
        super_t::reserve(element_count);
    }

    /// \copydoc boost::heap::priority_queue::value_comp
    value_compare const & value_comp(void) const
    {
        return super_t::value_comp();
    }
};

} /* namespace heap */
} /* namespace boost */

#undef BOOST_HEAP_ASSERT

#endif /* BOOST_HEAP_MIN_MAX_HEAP_HPP */
