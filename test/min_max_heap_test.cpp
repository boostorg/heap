// boost heap: min-max heap
//
// Copyright (C) 2019 Grégoire Scano
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#define BOOST_TEST_MAIN
#include <boost/test/unit_test.hpp>

#include <boost/heap/min_max_heap.hpp>

#include "common_heap_tests.hpp"
#include "stable_heap_tests.hpp"
#include "mutable_heap_tests.hpp"
#include "merge_heap_tests.hpp"

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
    run_common_heap_tests<pri_queue>();

    run_iterator_heap_tests<pri_queue>();
    run_copyable_heap_tests<pri_queue>();
    run_moveable_heap_tests<pri_queue>();
    run_reserve_heap_tests<pri_queue>();
    run_merge_tests<pri_queue>();

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
    run_min_max_heap_test<3, false>();
    run_min_max_heap_test<4, false>();
    run_min_max_heap_test<5, false>();
}
