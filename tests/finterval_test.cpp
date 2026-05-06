// Copyright 2026 Yi-Nung Tsao

#include "../include/lala/finterval.hpp"

#include <gtest/gtest.h>
#include "generic_lattice_test.hpp"
#include "lala/finterval.hpp"

using fitv_f = lala::FInterval<float, battery::local_memory>;
using afitv_f = lala::FInterval<float, battery::atomic_memory<>>;
using fitv_d = lala::FInterval<double, battery::local_memory>;
using afitv_d = lala::FInterval<double, battery::atomic_memory<>>;
//using fitv_ld = lala::FInterval<long double, battery::local_memory>;
//using afitv_ld = lala::FInterval<long double, battery::atomic_memory<>>;

template <class ITV>
void generic_FITV_test() {
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

TEST(FITVTest, LatticeOperation) {
  generic_FITV_test<fitv_f>();
  generic_FITV_test<afitv_f>();
  generic_FITV_test<fitv_d>();
  generic_FITV_test<afitv_d>();
  // generic_FITV_test<fitv_ld>();
  // generic_FITV_test<afitv_ld>();
}


