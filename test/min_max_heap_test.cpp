// boost heap: min-max heap
//
// Copyright (C) 2019 Grégoire Scano
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#define BOOST_TEST_MAIN

#define BOOST_HEAP_SANITYCHECKS

#include <boost/test/unit_test.hpp>

#include <boost/heap/min_max_heap.hpp>

#include "common_heap_tests.hpp"
#include "stable_heap_tests.hpp"
#include "mutable_heap_tests.hpp"
#include "merge_heap_tests.hpp"

#include <bitset>
#include <set>
#include <cmath>

template <unsigned int D>
void run_tree_depth_test(void)
{
    boost::heap::detail::tree_depth<D, unsigned int> depth;

    BOOST_REQUIRE(depth(0) == 0);

    unsigned int index = 1;
    for (unsigned int i = 1, count = D; i < 32/D; ++i, count *= D)
        for (unsigned int j = 0; j < count; ++j, ++index)
            BOOST_REQUIRE(depth(index) == i);
}

BOOST_AUTO_TEST_CASE( tree_depth_test )
{
  BOOST_REQUIRE(boost::heap::log2<unsigned long>(1) == 0);
  BOOST_REQUIRE(boost::heap::log2<unsigned long>(2) == 1);

  run_tree_depth_test<1>();
  run_tree_depth_test<2>();
  run_tree_depth_test<3>();
  run_tree_depth_test<4>();
  run_tree_depth_test<5>();
}

unsigned int last_line_index(unsigned int base, unsigned int max, unsigned int & depth)
{
    depth = 0;
    unsigned int first = 0;
    unsigned int local = 1;
    unsigned int count = 1;
    while (count <= max) {
        first = count;
        local *= base;
        count += local;
        ++depth;
    }

    return first;
}

void masks(unsigned int base, unsigned int max, unsigned int index, std::set<unsigned int> & mask, std::set<unsigned int> & umask)
{
    BOOST_REQUIRE(max != 0);

    unsigned int depth;
    const unsigned int last_line_left_index = last_line_index(base, max, depth);
    mask.clear();

    std::queue<unsigned int> queue;
    queue.push(index);

    while (!queue.empty()) {
        const unsigned int child = queue.front();
        queue.pop();

        if (last_line_left_index <= child)
            mask.insert(child);
        else {
            unsigned int current = base * child + 1;
            const unsigned int right = base * (child + 1);

            while (current <= right) {
                if (current <= max)
                    queue.push(current);
                else
                    mask.insert(current);

                ++current;
            }
        }
    }

    umask.clear();

    const unsigned int last_line_right_index = last_line_left_index + std::pow(base, depth) - 1;

    for (unsigned int i = last_line_left_index; i <= last_line_right_index; ++i)
        if (mask.find(i) == mask.end())
            umask.insert(i);
}

BOOST_AUTO_TEST_CASE( min_max_heap_expected_mask_test )
{
    std::set<unsigned int> mask;
    std::set<unsigned int> umask;

#define LOCALTEST(base, max, index, ...)                                \
    masks(base, max, index, mask, umask);                               \
    BOOST_REQUIRE(mask == std::set<unsigned int>(__VA_ARGS__));

    LOCALTEST(2, 1, 0, {1,2});
    LOCALTEST(2, 1, 1, {1});
    LOCALTEST(2, 2, 0, {1,2});
    LOCALTEST(2, 2, 1, {1});
    LOCALTEST(2, 2, 2, {2});
    LOCALTEST(2, 3, 0, {3,4,5,6});
    LOCALTEST(2, 3, 1, {3,4});
    LOCALTEST(2, 3, 2, {5,6});
    LOCALTEST(2, 3, 3, {3});
    LOCALTEST(2, 4, 0, {3,4,5,6});
    LOCALTEST(2, 4, 1, {3,4});
    LOCALTEST(2, 4, 2, {5,6});
    LOCALTEST(2, 4, 3, {3});
    LOCALTEST(2, 4, 4, {4});

    LOCALTEST(3, 1, 0, {1,2,3});
    LOCALTEST(3, 1, 1, {1});
    LOCALTEST(3, 2, 0, {1,2,3});
    LOCALTEST(3, 2, 1, {1});
    LOCALTEST(3, 2, 2, {2});
    LOCALTEST(3, 3, 0, {1,2,3});
    LOCALTEST(3, 3, 1, {1});
    LOCALTEST(3, 3, 2, {2});
    LOCALTEST(3, 3, 3, {3});
    LOCALTEST(3, 4, 0, {4,5,6,7,8,9,10,11,12});
    LOCALTEST(3, 4, 1, {4,5,6});
    LOCALTEST(3, 4, 2, {7,8,9});
    LOCALTEST(3, 4, 3, {10,11,12});
    LOCALTEST(3, 4, 4, {4});
    LOCALTEST(3, 5, 0, {4,5,6,7,8,9,10,11,12});
    LOCALTEST(3, 5, 1, {4,5,6});
    LOCALTEST(3, 5, 2, {7,8,9});
    LOCALTEST(3, 5, 3, {10,11,12});
    LOCALTEST(3, 5, 4, {4});
    LOCALTEST(3, 5, 5, {5});
#undef LOCALTEST
}

template <unsigned int D>
void run_min_max_heap_ordered_iterator_status_test(unsigned int max)
{
    std::set<unsigned int> mask;
    std::set<unsigned int> umask;

    for (unsigned int max_index = 1; max_index <= std::pow(D, max) + 1; ++max_index) {
        for (unsigned int index = 0; index <= max_index; ++index) {
            masks(D, max_index, index, mask, umask);

            {
                boost::heap::detail::min_max_ordered_iterator_status<D, unsigned int> status(max_index);

                for (std::set<unsigned int>::const_iterator it = mask.begin(); it != mask.end(); ++it) {
                    BOOST_REQUIRE(!status.is_complete(index));
                    status.set(*it);
                    BOOST_REQUIRE(status.is_complete(*it));
                }

                BOOST_REQUIRE(status.is_complete(index));

                for (std::set<unsigned int>::const_iterator it = umask.begin(); it != umask.end(); ++it)
                    BOOST_REQUIRE(!status.is_complete(*it));

                for (std::set<unsigned int>::const_iterator it = mask.begin(); it != mask.end(); ++it) {
                    status.reset(*it);
                    BOOST_REQUIRE(!status.is_complete(*it));
                }

                BOOST_REQUIRE(!status.is_complete(index));
            }

            {
                boost::heap::detail::min_max_ordered_iterator_status<D, unsigned int> status(max_index);

                status.set(index);
                BOOST_REQUIRE(status.is_complete(index));

                for (std::set<unsigned int>::const_iterator it = mask.begin(); it != mask.end(); ++it)
                    BOOST_REQUIRE(status.is_complete(*it));

                for (std::set<unsigned int>::const_iterator it = umask.begin(); it != umask.end(); ++it)
                    BOOST_REQUIRE(!status.is_complete(*it));

                status.reset(index);
                BOOST_REQUIRE(!status.is_complete(index));

                for (std::set<unsigned int>::const_iterator it = mask.begin(); it != mask.end(); ++it)
                    BOOST_REQUIRE(!status.is_complete(*it));
            }
        }
    }
}

BOOST_AUTO_TEST_CASE( min_max_heap_ordered_iterator_status_test )
{
    run_min_max_heap_ordered_iterator_status_test<2>(7);
    run_min_max_heap_ordered_iterator_status_test<3>(3);
    run_min_max_heap_ordered_iterator_status_test<4>(2);
    run_min_max_heap_ordered_iterator_status_test<5>(2);
}

template <typename T,
          class BoundArgs,
          class IndexUpdater>
struct dispatcher_queue : boost::heap::detail::min_max_heap<T, BoundArgs, IndexUpdater>
{
    typedef boost::heap::detail::min_max_heap<T, BoundArgs, IndexUpdater> base;

    void clear()
    {
        base::clear();
    }

    void set(unsigned int i)
    {
        base::clear();

        while (0 < i) {
            base::push(i);
            --i;
        }
    }
};

/*
 * Testing the iterator dispatcher for ordered iterator only
 * (true template parameter) because the reverse iterator
 * dispatcher merely switches the result of is_on_compare_level
 * while the tree examination remains the same.
*/
template <unsigned int D>
void run_min_max_heap_iterator_dispatcher_upward_test()
{
    typedef typename boost::heap::detail::min_max_heap_signature::bind<
        boost::heap::arity<D>,
        boost::parameter::void_,
        boost::parameter::void_,
        boost::parameter::void_,
        boost::parameter::void_,
        boost::parameter::void_>::type signature;
    typedef dispatcher_queue<int, signature, boost::heap::detail::nop_index_updater> pri_queue;
    typedef typename pri_queue::template iterator_dispatcher<true> iterator_dispatcher;

    pri_queue q;
    std::pair<long unsigned int, long unsigned int> regular;
    std::pair<long unsigned int, long unsigned int> extra;

    {
        q.set(D * D + 2); extra.first = 1; extra.second = 0;
        iterator_dispatcher dispatcher = iterator_dispatcher(q.size() - 1);

        regular = dispatcher.get_child_nodes(&q, D * D + 1, extra);
        BOOST_REQUIRE(regular.first == D && regular.second == D);
        BOOST_REQUIRE(extra.first == 1 && extra.second == 0);
    }

    q.clear();

    {
        q.set(D * (D * D + 1) + 2); extra.first = 1; extra.second = 0;
        iterator_dispatcher dispatcher = iterator_dispatcher(q.size() - 1);

        for (unsigned int i = 1; i <= D; ++i) {
            regular = dispatcher.get_child_nodes(&q, D * D + 1 + i, extra);
            BOOST_REQUIRE(regular.first == 1 && regular.second == 0);
            BOOST_REQUIRE(extra.first == 1 && extra.second == 0);
        }

        regular = dispatcher.get_child_nodes(&q, D * (D * D + 1) + 1, extra);
        BOOST_REQUIRE(regular.first == D && regular.second == D);
        BOOST_REQUIRE(extra.first == 1 && extra.second == 0);
    }
}

BOOST_AUTO_TEST_CASE( min_max_heap_iterator_dispatcher_test )
{
    typedef typename boost::heap::detail::min_max_heap_signature::bind<
        boost::parameter::void_,
        boost::parameter::void_,
        boost::parameter::void_,
        boost::parameter::void_,
        boost::parameter::void_,
        boost::parameter::void_>::type signature;
    typedef dispatcher_queue<int, signature, boost::heap::detail::nop_index_updater> pri_queue;
    typedef typename pri_queue::template iterator_dispatcher<true> iterator_dispatcher;

    pri_queue q;
    std::pair<long unsigned int, long unsigned int> regular;
    std::pair<long unsigned int, long unsigned int> extra;

#define CHECK(size_, index, xr,yr,xe,ye) {                              \
        q.set(size_); extra.first = 1; extra.second = 0;                \
        iterator_dispatcher dispatcher = iterator_dispatcher(q.size()-1); \
        regular = dispatcher.get_child_nodes(&q, index, extra);         \
        BOOST_REQUIRE(regular.first == xr);                             \
        BOOST_REQUIRE(regular.second == yr);                            \
        BOOST_REQUIRE((!(xe < ye) || (extra.first == xe && extra.second == ye)) \
                      || (!(ye < xe) || extra.second < extra.first));   \
    }

    CHECK(1,0,1,0,1,0);
    CHECK(2,0,1,1,1,0);
    CHECK(3,0,1,2,1,0);
    CHECK(4,0,3,3,2,2);
    CHECK(5,0,3,4,2,2);
    CHECK(6,0,3,5,1,0);
    CHECK(7,0,3,6,1,0);

    CHECK(8,3,7,7,1,0);
    CHECK(9,3,7,8,1,0);
    CHECK(10,3,7,8,1,0);
    CHECK(10,4,9,9,1,0);

    CHECK(13,5,11,12,1,0);

#undef CHECK

    run_min_max_heap_iterator_dispatcher_upward_test<2>();
    run_min_max_heap_iterator_dispatcher_upward_test<3>();
    run_min_max_heap_iterator_dispatcher_upward_test<4>();
    run_min_max_heap_iterator_dispatcher_upward_test<5>();
}

template <int D, bool stable>
void run_min_max_heap_test(void)
{
    typedef boost::heap::min_max_heap<int,
                                      boost::heap::arity<D>,
                                      boost::heap::stable<stable>,
                                      boost::heap::compare<std::less<int> >,
                                      boost::heap::allocator<std::allocator<int> > > pri_queue;

    BOOST_CONCEPT_ASSERT((boost::heap::PriorityQueue<pri_queue>));

    run_concept_check<pri_queue>();
    run_common_heap_tests<pri_queue>();

    run_iterator_heap_tests<pri_queue>();
    run_copyable_heap_tests<pri_queue>();
    run_moveable_heap_tests<pri_queue>();
    run_reserve_heap_tests<pri_queue>();
    run_merge_tests<pri_queue>();

    run_ordered_iterator_tests<pri_queue>();
    run_reverse_ordered_iterator_tests<pri_queue>();

    if (stable) {
        typedef boost::heap::min_max_heap<q_tester, boost::heap::arity<D>,
                                          boost::heap::stable<stable>
                                          > stable_pri_queue;

        run_stable_heap_tests<stable_pri_queue>();
    }

#if !defined(BOOST_NO_CXX11_RVALUE_REFERENCES) && !defined(BOOST_NO_CXX11_VARIADIC_TEMPLATES)
    cmpthings ord;
    boost::heap::min_max_heap<thing, boost::heap::arity<D>, boost::heap::compare<cmpthings>, boost::heap::stable<stable> > vpq(ord);
    vpq.emplace(5, 6, 7);
#endif
}

BOOST_AUTO_TEST_CASE( min_max_heap_test )
{
    run_min_max_heap_test<2, false>();
    run_min_max_heap_test<3, false>();
    run_min_max_heap_test<4, false>();
    run_min_max_heap_test<5, false>();
}

BOOST_AUTO_TEST_CASE( min_max_heap_stable_test )
{
    run_min_max_heap_test<2, true>();
    run_min_max_heap_test<3, true>();
    run_min_max_heap_test<4, true>();
    run_min_max_heap_test<5, true>();
}
