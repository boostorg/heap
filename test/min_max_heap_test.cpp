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

template<unsigned int D>
void run_tree_depth_test(void)
{
    boost::heap::detail::tree_depth<D, unsigned int> depth;

    BOOST_REQUIRE(depth(0) == 0);

    unsigned int index = 1;
    for (unsigned int i = 1, count = D; i < 32/D; ++i, count *= D) {
        for (unsigned int j = 0; j < count; ++j, ++index) {
            BOOST_REQUIRE(depth(index) == i);
        }
    }
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

void print(const std::vector<uint8_t> & v)
{
    for (std::vector<uint8_t>::const_iterator it = v.begin(); it != v.end(); ++it) {
        std::cerr << std::bitset<8>(*it) << " ";
    }
    std::cerr << std::endl;
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

BOOST_AUTO_TEST_CASE( run_expected_mask_test )
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

template<unsigned int D>
void run_min_max_ordered_iterator_status(unsigned int max)
{
    std::set<unsigned int> mask;
    std::set<unsigned int> umask;

    for (unsigned int max_index = 1; max_index <= std::pow(D, max) + 1; ++max_index) {
        for (unsigned int index = 0; index <= max_index; ++index) {
            masks(D, max_index, index, mask, umask);

            {
                boost::heap::detail::min_max_ordered_iterator_status<D, unsigned int> status(max_index);

                for (std::set<unsigned int>::const_iterator it = mask.begin(); it != mask.end(); ++it) {
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

BOOST_AUTO_TEST_CASE( run_min_max_ordered_iterator_status_test )
{
    run_min_max_ordered_iterator_status<2>(7);
    run_min_max_ordered_iterator_status<3>(3);
    run_min_max_ordered_iterator_status<4>(2);
    run_min_max_ordered_iterator_status<5>(2);
}

BOOST_AUTO_TEST_CASE( min_max_heap_paper_test )
{
    //int buffer[] = {5, 65, 80, 25, 37, 8, 15, 57, 36, 45, 59, 20, 14, 32, 18, 28, 30, 34, 27, 39, 38, 45, 50, 15, 12, 13, 10, 30, 31, 16, 17};

    typedef boost::heap::min_max_heap<int,
                                      boost::heap::arity<2>,
                                      boost::heap::stable<false>,
                                      boost::heap::compare<std::less<int> >,
                                      boost::heap::allocator<std::allocator<int> > > pri_queue;

    pri_queue q;

    q.push(31);
    q.push(17);
    q.push(24);
    q.push(25);
    q.push(37);
    q.push(8);
    q.push(5);
}

template<int D, bool stable>
void run_min_max_heap_test(void)
{
    typedef boost::heap::min_max_heap<int,
                                      boost::heap::arity<D>,
                                      boost::heap::stable<stable>,
                                      boost::heap::compare<std::less<int> >,
                                      boost::heap::allocator<std::allocator<int> > > pri_queue;

    BOOST_CONCEPT_ASSERT((boost::heap::PriorityQueue<pri_queue>));

    run_concept_check<pri_queue>();
    //run_common_heap_tests<pri_queue>();
    pri_queue_test_sequential_push<pri_queue>();
    pri_queue_test_sequential_reverse_push<pri_queue>();
    pri_queue_test_random_push<pri_queue>();
    pri_queue_test_equality<pri_queue>();
    pri_queue_test_inequality<pri_queue>();
    pri_queue_test_less<pri_queue>();
    pri_queue_test_clear<pri_queue>();

    pri_queue_test_emplace<pri_queue>();
    //
    //run_iterator_heap_tests<pri_queue>();
    //run_copyable_heap_tests<pri_queue>();
    //run_moveable_heap_tests<pri_queue>();
    //run_reserve_heap_tests<pri_queue>();
    //run_merge_tests<pri_queue>();

    //run_ordered_iterator_tests<pri_queue>();
#if 0
    if (stable) {
        typedef boost::heap::min_max_heap<q_tester, boost::heap::arity<D>,
                                          boost::heap::stable<stable>
                                          > stable_pri_queue;

        run_stable_heap_tests<stable_pri_queue>();
    }
#endif
#if !defined(BOOST_NO_CXX11_RVALUE_REFERENCES) && !defined(BOOST_NO_CXX11_VARIADIC_TEMPLATES)
    cmpthings ord;
    boost::heap::min_max_heap<thing, boost::heap::arity<D>, boost::heap::compare<cmpthings>, boost::heap::stable<stable> > vpq(ord);
    vpq.emplace(5, 6, 7);
#endif
}

BOOST_AUTO_TEST_CASE( min_max_heap_test )
{
    run_min_max_heap_test<2, false>();
    //run_min_max_heap_test<3, false>();
    //run_min_max_heap_test<4, false>();
    //run_min_max_heap_test<5, false>();
}
