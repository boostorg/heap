if(NOT TARGET boost_heap_all_tests)
    add_custom_target(boost_heap_all_tests)
endif()

add_library(boost_heap_test_common INTERFACE)

if (CMAKE_VERSION VERSION_GREATER_EQUAL 3.23)
  target_sources(boost_heap_test_common PUBLIC FILE_SET HEADERS FILES
      common_heap_tests.hpp
      merge_heap_tests.hpp
      mutable_heap_tests.hpp
      stable_heap_tests.hpp
  )
  source_group( TREE "${CMAKE_CURRENT_SOURCE_DIR}" FILES
      common_heap_tests.hpp
      merge_heap_tests.hpp
      mutable_heap_tests.hpp
      stable_heap_tests.hpp)
endif()

set(Tests
    binomial_heap_test
    d_ary_heap_test
    fibonacci_heap_test
    pairing_heap_tests
    priority_queue_test
    skew_heap_test
    mutable_heap_test
)

foreach(Test ${Tests})
    # Test target
    add_executable(boost_heap_${Test} ${Test}.cpp )
    source_group( TREE "${CMAKE_CURRENT_SOURCE_DIR}" FILES ${Test}.cpp)

    target_include_directories(boost_heap_${Test} PRIVATE . )
    target_link_libraries(boost_heap_${Test} PRIVATE
        Boost::heap
        Boost::unit_test_framework
    )


    # CTest Target
    add_test(NAME boost_heap_${Test} COMMAND boost_heap_${Test})
    add_dependencies(boost_heap_all_tests boost_heap_${Test} )
endforeach()
