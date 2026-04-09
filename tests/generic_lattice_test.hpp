// Copyright 2026 Pierre Talbot

#ifndef LALA_INTERVAL_GENERIC_LATTICE_TEST_HPP
#define LALA_INTERVAL_GENERIC_LATTICE_TEST_HPP

/** We must have `A::bot() < mid < A::top()`. */
template <class A>
void bot_top_test(const A& mid) {
  A bot = A::bot();
  A top = A::top();
  EXPECT_TRUE(bot.is_bot());
  EXPECT_TRUE(top.is_top());
  EXPECT_FALSE(top.is_bot());
  EXPECT_FALSE(bot.is_top());
  EXPECT_TRUE(bot.leq(top));
  EXPECT_TRUE(bot.lt(top));
  EXPECT_FALSE(top.leq(bot));
  EXPECT_FALSE(top.lt(bot));

  EXPECT_FALSE(mid.is_bot());
  EXPECT_FALSE(mid.is_top());
  EXPECT_TRUE(bot.lt(mid)) << bot << " " << mid;
  EXPECT_TRUE(mid.lt(top)) << mid << " " << top;
}

template <class A>
void join_one_test(const A& a, const A& b, const A& expect, bool has_changed_expect) {
  EXPECT_EQ(join(a, b), expect)  << "join(" << a << ", " << b << ")";
  A c(a);
  EXPECT_EQ(c.join(b), has_changed_expect) << a << ".join(" << b << ") == " << expect;
  EXPECT_EQ(c, expect) << a << ".join(" << b << ")";
}

template <class A>
void meet_one_test(const A& a, const A& b, const A& expect, bool has_changed_expect) {
  EXPECT_EQ(meet(a, b), expect) << "meet(" << a << ", " << b << ")";
  A c(a);
  EXPECT_EQ(c.meet(b), has_changed_expect) << c << ".meet(" << b << ")";
  EXPECT_EQ(c, expect) << c << ".meet(" << b << ")";
}

// `a` and `b` are supposed ordered and `a <= b`.
template <class A>
void join_meet_generic_test(const A& a, const A& b) {
  // Reflexivity
  join_one_test(a, a, a, false);
  meet_one_test(a, a, a, false);
  join_one_test(b, b, b, false);
  meet_one_test(b, b, b, false);
  // Coherency of join/meet w.r.t. ordering
  join_one_test(a, b, b, a != b);
  join_one_test(b, a, b, false);
  // Commutativity
  meet_one_test(a, b, a, false);
  meet_one_test(b, a, a, a != b);
  // Absorbing
  meet_one_test(a, A::top(), a, false);
  meet_one_test(b, A::top(), b, false);
  join_one_test(a, A::top(), A::top(), !a.is_top());
  join_one_test(b, A::top(), A::top(), !b.is_top());
  meet_one_test(a, A::bot(), A::bot(), !a.is_bot());
  meet_one_test(b, A::bot(), A::bot(), !b.is_bot());
  join_one_test(a, A::bot(), a, false);
  join_one_test(b, A::bot(), b, false);
}

#endif
