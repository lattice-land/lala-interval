// Copyright 2026 Pierre Talbot

#include <gtest/gtest.h>
#include "lala/zinterval.hpp"
#include "generic_lattice_test.hpp"

using zitv = lala::ZInterval<int, battery::local_memory>;
using azitv = lala::ZInterval<int, battery::atomic_memory<>>;
using zitv_f = lala::ZInterval<float, battery::local_memory>;
using azitv_f = lala::ZInterval<float, battery::atomic_memory<>>;
using zitv_d = lala::ZInterval<double, battery::local_memory>;
using azitv_d = lala::ZInterval<double, battery::atomic_memory<>>;

template <class ITV>
void generic_ZITV_test() {
  bot_top_test(ITV(5));
  EXPECT_TRUE(ITV(10).lt(ITV::top()));
  EXPECT_FALSE(ITV(0).lt(ITV(10)));
  EXPECT_FALSE(ITV(0).leq(ITV(10)));
  EXPECT_TRUE(ITV::bot().lt(ITV(10)));
  join_meet_generic_test(ITV::bot(), ITV::top());
  join_meet_generic_test(ITV(0), ITV(0));
  join_meet_generic_test(ITV(0), ITV(0, 5));
  join_meet_generic_test(ITV(0), ITV(-5, 5));
  join_meet_generic_test(ITV(-1, 1), ITV(-5, 5));
  join_meet_generic_test(ITV(-1, 1), ITV::top());
  join_meet_generic_test(ITV::bot(), ITV(-5, 5));
}

TEST(ZITVTest, LatticeOperation) {
  generic_ZITV_test<zitv>();
  generic_ZITV_test<azitv>();
  generic_ZITV_test<zitv_f>();
  generic_ZITV_test<azitv_f>();
  generic_ZITV_test<zitv_d>();
  generic_ZITV_test<azitv_d>();
}


