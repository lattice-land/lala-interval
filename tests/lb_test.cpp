// Copyright 2026 Pierre Talbot

#include <gtest/gtest.h>
#include "lala/lb.hpp"
#include "generic_lattice_test.hpp"

using zlb = lala::LB<int, battery::local_memory>;
using azlb = lala::LB<int, battery::atomic_memory<>>;
using flb = lala::LB<float, battery::local_memory>;
using aflb = lala::LB<float, battery::atomic_memory<>>;
using unzlb = lala::LB<unsigned int, battery::local_memory>;
using aunzlb = lala::LB<unsigned int, battery::atomic_memory<>>;

template <class LB>
void generic_LB_test() {
  bot_top_test(LB(5));
  EXPECT_TRUE(LB(10).lt(LB::top()));
  EXPECT_TRUE(LB(10).lt(LB(0)));
  EXPECT_TRUE(LB::bot().lt(LB(10)));
  join_meet_generic_test(LB::bot(), LB::top());
  join_meet_generic_test(LB(0), LB(0));
  join_meet_generic_test(LB(5), LB(0));
  join_meet_generic_test(LB(-5), LB(-10));
  // join_meet_generic_test(LB(-3), LB(3)); // for `unsigned int`, it doesn't work
}

TEST(LBTest, LatticeOperation) {
  generic_LB_test<zlb>();
  generic_LB_test<azlb>();
  generic_LB_test<flb>();
  generic_LB_test<aflb>();
  generic_LB_test<unzlb>();
  generic_LB_test<aunzlb>();
}
