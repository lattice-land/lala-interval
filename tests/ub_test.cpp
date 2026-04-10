// Copyright 2026 Yi-Nung Tsao 

#include <gtest/gtest.h>
#include "lala/ub.hpp"
#include "generic_lattice_test.hpp"

using zub = lala::UB<int, battery::local_memory>;
using azub = lala::UB<int, battery::atomic_memory<>>;
using fub = lala::UB<float, battery::local_memory>;
using afub = lala::UB<float, battery::atomic_memory<>>;
using unzub = lala::UB<unsigned int, battery::local_memory>;
using aunzub = lala::UB<unsigned int, battery::atomic_memory<>>;

template <class UB>
void generic_UB_test() {
  bot_top_test(UB(5));
  EXPECT_TRUE(UB(10).lt(UB::top()));
  EXPECT_TRUE(UB(0).lt(UB(10)));
  EXPECT_TRUE(UB::bot().lt(UB(10)));
  join_meet_generic_test(UB::bot(), UB::top());
  join_meet_generic_test(UB(0), UB(0));
  join_meet_generic_test(UB(0), UB(5));
  join_meet_generic_test(UB(-10), UB(-5));
  // join_meet_generic_test(UB(-3), UB(3)); // for `unsigned int`, it doesn't work.
}

TEST(UBTest, LatticeOperation) {
  generic_UB_test<zub>();
  generic_UB_test<azub>();
  generic_UB_test<fub>();
  generic_UB_test<afub>();
  generic_UB_test<unzub>();
  generic_UB_test<aunzub>();
}
