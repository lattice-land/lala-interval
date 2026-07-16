// Copyright 2026 Pierre Talbot

#ifndef LALA_INTERVAL_ZINTERVAL_HPP
#define LALA_INTERVAL_ZINTERVAL_HPP

#include "lala/lb.hpp"
#include "lala/ub.hpp"

namespace lala {

template <class VT, class Mem>
class ZInterval;

template <class VT, class Mem>
CUDA INLINE constexpr ZInterval<VT, Mem> join(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b);
template <class VT, class Mem>
CUDA INLINE constexpr ZInterval<VT, Mem> join_nobot(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b);

namespace tell {
template<class VT>
CUDA INLINE constexpr void zfdiv_fast2(ZInterval<VT,battery::local_memory>& x, ZInterval<VT,battery::local_memory>& y, ZInterval<VT,battery::local_memory>& z);

template<class VT>
CUDA INLINE constexpr void zfdiv_fast3(ZInterval<VT,battery::local_memory>& x, ZInterval<VT,battery::local_memory>& y, ZInterval<VT,battery::local_memory>& z);

template<class VT>
CUDA INLINE constexpr void zfdiv2(ZInterval<VT, battery::local_memory>& x, ZInterval<VT, battery::local_memory>& y, ZInterval<VT, battery::local_memory>& z);

template<class VT>
CUDA INLINE constexpr void zfdiv3(ZInterval<VT, battery::local_memory>& x, ZInterval<VT, battery::local_memory>& y, ZInterval<VT, battery::local_memory>& z);
}
template <class VT, class Mem = battery::local_memory>
class ZInterval {
public:
  using value_type = VT;
  using memory_type = Mem;
  using lb_type = LB<value_type, memory_type>;
  using ub_type = UB<value_type, memory_type>;
  using this_type = ZInterval<value_type, memory_type>;
  using basic_type = ZInterval<value_type>;

  template <class VT2, class Mem2>
  friend class ZInterval;

  template<class VT2>
  friend CUDA INLINE constexpr void tell::zfdiv_fast2(ZInterval<VT2>& x, ZInterval<VT2>& y, ZInterval<VT2>& z);

  template<class VT2>
  friend CUDA INLINE constexpr void tell::zfdiv_fast3(ZInterval<VT2>& x, ZInterval<VT2>& y, ZInterval<VT2>& z);

  template<class VT2>
  friend CUDA INLINE constexpr void tell::zfdiv2(ZInterval<VT2>& x, ZInterval<VT2>& y, ZInterval<VT2>& z);

  template<class VT2>
  friend CUDA INLINE constexpr void tell::zfdiv3(ZInterval<VT2>& x, ZInterval<VT2>& y, ZInterval<VT2>& z);


  constexpr static const bool is_totally_ordered = false;
  constexpr static const char* name = "ZInterval";

private:
  using LB2 = typename lb_type::basic_type;
  using UB2 = typename ub_type::basic_type;
  lb_type l;
  ub_type u;

public:
  CUDA INLINE static constexpr this_type bot() { return this_type(lb_type::bot(), ub_type::bot()); }
  CUDA INLINE static constexpr this_type top() { return this_type(lb_type::top(), ub_type::top()); }

  constexpr ZInterval() = default;
  constexpr ZInterval(const this_type&) = default;
  CUDA constexpr ZInterval(value_type x): l(x), u(x) {}
  CUDA constexpr ZInterval(value_type l, value_type u): l(l), u(u) {}

  template <class Mem2>
  CUDA constexpr ZInterval(const ZInterval<value_type, Mem2>& other)
   : l(other.l)
   , u(other.u)
  {}

  constexpr this_type& operator=(const this_type&) = default;
  template <class Mem2>
  CUDA INLINE constexpr this_type& operator=(const ZInterval<value_type, Mem2>& other) {
    l = other.l;
    u = other.u;
    return *this;
  }

  CUDA INLINE constexpr lb_type& lb() { return l; }
  CUDA INLINE constexpr ub_type& ub() { return u; }
  CUDA INLINE constexpr const lb_type& lb() const { return l; }
  CUDA INLINE constexpr const ub_type& ub() const { return u; }

  CUDA INLINE constexpr bool is_singleton() const {
    return l == u && !l.is_bot() && !u.is_bot();
  }

  CUDA INLINE constexpr bool is_singleton(value_type v) const {
    return l == v && u == v;
  }

  CUDA INLINE constexpr bool is_bot() const {
    return l > u || l.is_bot() || u.is_bot();
  }

  CUDA INLINE constexpr bool join(basic_type other) {
    if(other.is_bot()) { return false; }
    if(is_bot()) {
      l = other.l;
      u = other.u;
      return true;
    }
    return join_nobot(other);
  }

  CUDA INLINE constexpr bool eq(basic_type other) const {
    return (is_bot() && other.is_bot()) || eq_nobot(other);
  }

  CUDA INLINE constexpr bool leq(basic_type other) const {
    return is_bot() || leq_nobot(other);
  }

  CUDA INLINE constexpr bool lt(basic_type other) const {
    return leq(other) && !eq(other);
  }

  CUDA INLINE constexpr bool is_top() const {
    return l.is_top() && u.is_top();
  }

  CUDA INLINE constexpr this_type& join_top() {
    l.join_top();
    u.join_top();
    return *this;
  }

  CUDA INLINE constexpr this_type& meet_bot() {
    l.meet_bot();
    u.meet_bot();
    return *this;
  }

  CUDA INLINE constexpr bool meet(basic_type other) {
    if(is_bot()) { return false; }
    return meet_nobot(other);
  }

  /** The _nobot versions suppose `this` and `other` are not bot, hence providing more optimized operations.
      It coincides with the join operation in the lattice of intervals without considering all empty intervals in the same equivalence class. */

  CUDA INLINE constexpr bool join_nobot(basic_type other) {
    bool r = l.join(other.l);
    r |= u.join(other.u);
    return r;
  }

  CUDA INLINE constexpr bool meet_nobot(basic_type other) {
    bool r = l.meet(other.l);
    r |= u.meet(other.u);
    return r;
  }


  CUDA INLINE constexpr bool eq_nobot(basic_type other) const {
    return l == other.l && u == other.u;
  }

  CUDA INLINE constexpr bool leq_nobot(basic_type other) const {
    return l >= other.l && u <= other.u;
  }

  CUDA INLINE constexpr bool lt_nobot(basic_type other) const {
    return leq_nobot(other) && (l != other.l || u != other.u);
  }

  CUDA NI void print() const {
    printf("[");
    lb().print();
    printf(",");
    ub().print();
    printf("]");
  }

  /** precondition: `!is_bot()` */
  CUDA constexpr value_type midpoint() const {
    if(l.is_top() && u.is_top()) return 0;
    if(l.is_top()) return l + VT{1}; // the largest negative number representable.
    if(u.is_top()) return u - VT{1}; // the largest positive number representable.
    return battery::midpoint(l, u);
  }

  /** Abstract functions. */

  CUDA INLINE UB<size_t> count() const {
    if(is_bot()) { return 0; }
    if(l.is_top() || u.is_top()) { return UB<size_t>::top(); }
    return u - l + size_t{1};
  }

  CUDA INLINE constexpr bool contains(value_type v) {
    return l <= v && v <= u;
  }

  CUDA INLINE constexpr bool contains(basic_type a) {
    return a.leq(*this);
  }

  // Remove 0 from the interval when possible.
  CUDA INLINE constexpr this_type& neq_zero() {
    if(l == 0) { l.meet(VT{1}); }
    if(u == 0) { u.meet(VT{-1}); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], -a)`.
  CUDA INLINE constexpr this_type& neg(basic_type a) {
    if(a.is_bot()) { return meet_bot(); }
    if(!a.u.is_top()) { l.meet(-a.u); }
    if(!a.l.is_top()) { u.meet(-a.l); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a + b)`.
  CUDA INLINE constexpr this_type& add(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(!a.l.is_top() && !b.l.is_top()) { l.meet(a.l + b.l); }
    if(!a.u.is_top() && !b.u.is_top()) { u.meet(a.u + b.u); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a - b)`.
  CUDA INLINE constexpr this_type& sub(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(!a.l.is_top() && !b.l.is_top()) { l.meet(a.l - b.u); }
    if(!a.u.is_top() && !b.u.is_top()) { u.meet(a.u - b.l); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a * b)`.
  CUDA INLINE constexpr this_type& mul(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(!a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      l.meet(min(min(a.l * b.l, a.l * b.u), min(a.u * b.l, a.u * b.u)));
      u.meet(max(max(a.l * b.l, a.l * b.u), max(a.u * b.l, a.u * b.u)));
    }
    return *this;
  }

  // Let a = _ * x where _ can be anything, then `mul_back_zero` removes 0 from x (if possible) whenever 0 is not in a.
  CUDA INLINE constexpr this_type& mul_back_zero(basic_type a) {
    if(a.l > 0 || a.u < 0) { neq_zero(); }
    return *this;
  }

  // Let a = b * x, `mul_back_nz` computes the interval of `x` given a and b, without caring about the case where `0 notin a` (taken care of by `mul_back_zero`).
  // Why exposing `mul_back_zero` and `mul_back_nz` when we already have `mulb`?
  //   When implementing a propagator for `x = y * z`, it results in faster convergence to compute `z.mul_back_zero(x) ; y.mul_back_nz(x,z) ; y.mul_back_zero(x); z.mul_back_nz(x,y); ` instead of `y.mul_back(x,z); z.mul_back(x,y);` (if both were merged).
  CUDA INLINE constexpr this_type& mul_back_nz(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    using battery::cdiv;
    using battery::fdiv;
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(!a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      if(b.l > 0 || b.u < 0) {
        l.meet(min(min(cdiv<VT>(a.l, b.l), cdiv<VT>(a.l, b.u)), min(cdiv<VT>(a.u, b.l), cdiv<VT>(a.u, b.u))));
        u.meet(max(max(fdiv<VT>(a.l, b.l), fdiv<VT>(a.l, b.u)), max(fdiv<VT>(a.u, b.l), fdiv<VT>(a.u, b.u))));
      }
      else if(b.l < 0 && b.u > 0 && (a.l > 0 || a.u < 0)) {
        l.meet(min<VT>(a.l, -a.u));
        u.meet(max<VT>(-a.l, a.u));
      }
    }
    return *this;
  }

  // Let a = b * x, `mul_back` computes the interval of `x` given a and b.
  CUDA INLINE constexpr this_type& mul_back(basic_type a, basic_type b) {
    mul_back_zero(a);
    mul_back_nz(a, b);
    return *this;
  }

  CUDA INLINE constexpr this_type& min(basic_type a, basic_type b) {
    using battery::min;
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    l.meet(min(a.l, b.l));
    u.meet(min(a.u, b.u));
    return *this;
  }

  // Let a = min(b, x), we update x according to a and b.
  CUDA INLINE constexpr this_type& min_back(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    l.meet(a.l);
    if(a.u < b.l) { u.meet(a.u); }
    return *this;
  }

  CUDA INLINE constexpr this_type& max(basic_type a, basic_type b) {
    using battery::max;
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    l.meet(max(a.l, b.l));
    u.meet(max(a.u, b.u));
    return *this;
  }

  CUDA INLINE constexpr this_type& max_back(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(a.l > b.u) { l.meet(a.l); }
    u.meet(a.u);
    return *this;
  }

  // Let x = (a = b), we update x according to a and b.
  // precondition: x <= [0,1]
  CUDA INLINE constexpr this_type& req(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(a.l == b.u && a.u == b.l) {
      l.meet(VT{1});
    }
    else if(a.lb() > b.ub() || a.ub() < b.lb()) {
      u.meet(VT{0});
    }
    return *this;
  }

  // Let a = (b = x), we update x according to a and b.
  // precondition: a <= [0,1]
  CUDA INLINE constexpr this_type& req_back(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(a.l == VT{1}) {
      l.meet(b.l);
      u.meet(b.u);
    }
    else if(a.u == VT{0} && b.l == b.u) {
      if(l == b.l) { l.meet(l + VT{1}); }
      if(u == b.u) { u.meet(u - VT{1}); }
    }
    return *this;
  }

  // Let x = (a <= b), we update x according to a and b.
  // precondition: x <= [0,1]
  CUDA INLINE constexpr this_type& rleq(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(a.u <= b.l) {
      l.meet(VT{1});
    }
    else if(a.l > b.u) {
      u.meet(VT{0});
    }
    return *this;
  }

  // Let a = (x <= b), we update x according to a and b.
  // precondition: a <= [0,1]
  CUDA INLINE constexpr this_type& rleq_lback(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(a.l == VT{1}) {
      u.meet(b.u);
    }
    else if(a.u == VT{0}) {
      l.meet(b.l + VT{1});
    }
    return *this;
  }

  // Let a = (b <= x), we update x according to a and b.
  // precondition: a <= [0,1]
  CUDA INLINE constexpr this_type& rleq_rback(basic_type a, basic_type b) {
    if(a.is_bot() || b.is_bot()) { return meet_bot(); }
    if(a.l == VT{1}) {
      l.meet(b.l);
    }
    else if(a.u == VT{0}) {
      u.meet(b.u - VT{1});
    }
    return *this;
  }

private:
  // precondition: b.lb() != 0 && b.ub() != 0.
  template <class F>
  CUDA INLINE constexpr this_type& div_(basic_type a, basic_type b, F divz) {
    using battery::min;
    using battery::max;
    assert(b.l != 0 && b.u != 0);
    if(a.is_bot() || b.is_bot()) { meet_bot(); }
    else if(b.l < 0 && b.u > 0) { // With the split on Z, this part becomes useless (as well as the test in else if)
      if(!a.u.is_top()) { l.meet(min<VT>(a.l, -a.u)); }
      if(!a.l.is_top()) { u.meet(max<VT>(-a.l, a.u)); }
    }
    else if(!a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      l.meet(min(min(divz(a.l, b.l), divz(a.l, b.u)), min(divz(a.u, b.l), divz(a.u, b.u))));
      u.meet(max(max(divz(a.l, b.l), divz(a.l, b.u)), max(divz(a.u, b.l), divz(a.u, b.u))));
    }
    return *this;
  }

public:
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& fdiv(basic_type a, basic_type b) {
    return div_(a, b, battery::fdiv<VT>);
  }

  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& cdiv(basic_type a, basic_type b) {
    return div_(a, b, battery::cdiv<VT>);
  }

  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& tdiv(basic_type a, basic_type b) {
    return div_(a, b, battery::tdiv<VT>);
  }

  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& ediv(basic_type a, basic_type b) {
    return div_(a, b, battery::ediv<VT>);
  }

  // Let a = fdiv(x, b), this function updates the numerator x according to a and b.
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& fdiv_num(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    assert(b.l != 0 && b.u != 0);
    if(a.is_bot() || b.is_bot()) { meet_bot(); }
    else if(b.l < 0 && b.u > 0) {   // TO CONFIRM: never useful??
      l.meet(min(min<VT>(a.l, -a.u), min<VT>(a.l * b.u, (a.u + VT{1}) * b.l + VT{1})));
      u.meet(max(max<VT>(-a.l, a.u), max<VT>(a.l * b.l, (a.u + VT{1}) * b.u - VT{1})));
    }
    else {
      l.meet(min(min<VT>(a.l * b.l, a.l * b.u), min<VT>((a.u + VT{1}) * b.l + VT{1}, (a.u + VT{1}) * b.u + VT{1})));
      u.meet(max(max<VT>(a.l * b.l, a.l * b.u), max<VT>((a.u + VT{1}) * b.l - VT{1}, (a.u + VT{1}) * b.u - VT{1})));
    }
    return *this;
  }

  // Let a = cdiv(x, b), this function updates the numerator x according to a and b.
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& cdiv_num(basic_type a, basic_type b) {
    return fdiv_num(basic_type::top().neg(a), basic_type::top().neg(b));
  }

  // Let a = tdiv(x, b), this function updates the numerator x according to a and b.
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& tdiv_num(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    assert(b.l != 0 && b.u != 0);
    if(a.is_bot() || b.is_bot()) { meet_bot(); }
    else if(a.l > 0) { fdiv_num(a, b); }
    else if(a.u < 0) { cdiv_num(a, b); }
    else {
      basic_type r(min<VT>(b.l, VT{-b.u}) + VT{1}, max<VT>(VT{-b.l}, b.u) - VT{1});
      r.join(basic_type::top().cdiv_num(basic_type(a.l, -1), b));
      r.join(basic_type::top().fdiv_num(basic_type(1, a.u), b));
      meet(r);
    }
    return *this;
  }

  // Let a = ediv(x, b), this function updates the numerator x according to a and b.
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& ediv_num(basic_type a, basic_type b) {
    assert(b.l != 0 && b.u != 0);
    if(a.is_bot() || b.is_bot()) { meet_bot(); }
    else if(b.l > 0) { fdiv_num(a, b); }
    else if(b.u < 0) { cdiv_num(a, b); }
    else { // TO CONFIRM: With the split on Z, this part becomes useless
      meet(::lala::join(
            basic_type::top().cdiv_num(a, basic_type(b.l, -1)),
            basic_type::top().fdiv_num(a, basic_type(1, b.u))));
    }
    return *this;
  }

  // Let a = fdiv(b, x), this function updates the denominator x according to a and b.
  CUDA INLINE constexpr this_type& fdiv_den(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    using battery::fdiv;
    using battery::cdiv;
    if(a.is_bot() || b.is_bot()) { meet_bot(); }
    else if(a.l > 0 || a.u + VT{1} < 0) {
      if(b.l > 0) {
        l.meet(min(fdiv<VT>(b.l, a.u + VT{1}), fdiv<VT>(b.u, a.u + VT{1})) + VT{1});
        u.meet(max(fdiv<VT>(b.l, a.l), fdiv<VT>(b.u, a.l)));
      }
      else if(b.u < 0) {
        l.meet(min(cdiv<VT>(b.l, a.l), cdiv<VT>(b.u, a.l)));
        u.meet(max(cdiv<VT>(b.l, a.u + VT{1}), cdiv<VT>(b.u, a.u + VT{1})) - VT{1});
      }
      else {
        meet(::lala::join(
          basic_type::top().fdiv_den(a, basic_type(b.l, -1)),
          basic_type::top().fdiv_den(a, basic_type(1, b.u))));
      }
    }
    else if(a.l == 0 && a.u == 0) {
      if(b.l > 0) { l.meet(b.l + VT{1}); }
      else if(b.u < 0) { u.meet(b.u - VT{1}); }
    }
    else if(a.l == -1 && a.u == -1) {
      if(b.l > 0) { u.meet(-b.l); }
      else if(b.u < 0) { l.meet(-b.u); }
      else {
        // note: join_nobot is fine here as all arguments are normalized (either bot or non-empty).
        meet(::lala::join_nobot(
          b.l != 0 ? basic_type(1, UB2::top()) : basic_type::bot(),
          b.u != 0 ? basic_type(LB2::top(), -1) : basic_type::bot()));
      }
    }
    else {
      basic_type r(basic_type::top().fdiv_den(basic_type(a.l, -2), b));
      r.join(basic_type::top().fdiv_den(basic_type(max<VT>(a.l,-1),-1), b));
      r.join(basic_type::top().fdiv_den(basic_type(0, min<VT>(a.u, 0)), b));
      r.join(basic_type::top().fdiv_den(basic_type(1, a.u), b));
      meet(r);
    }
    return *this;
  }

  // Let a = cdiv(b, x), this function updates the denominator x according to a and b.
  CUDA INLINE constexpr this_type& cdiv_den(basic_type a, basic_type b) {
    return fdiv_den(basic_type::top().neg(a), basic_type::top().neg(b));
  }

  // Let a = tdiv(b, x), this function updates the denominator x according to a and b.
  // precondition: lb() != 0 && ub() != 0
  CUDA INLINE constexpr this_type& tdiv_den(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    assert(l != 0 && u != 0);
    if(a.is_bot() || b.is_bot() || is_bot()) { meet_bot(); }
    else if(a.l > 0) { fdiv_den(a, b); }
    else if(a.u < 0) { cdiv_den(a, b); }
    else if(a.is_singleton(0)) {
      if(l > 0 && (b.l > 0 || b.u < 0)) {
        l.meet(max(b.l + VT{1}, VT{-b.u} + VT{1}));
      }
      else if(u < 0 && (b.l > 0 || b.u < 0)) {
        u.meet(min(VT{-b.l} - VT{1}, b.u - VT{1}));
      }
      // HERE an alternative implementation (unfolding the one above, maybe a bit clearer).
      // if(b.l > 0 && l > 0) { return basic_type(b.l + VT{1}, UB2:top()); }
      // if(b.l > 0 && u < 0) { return basic_type(LB2::top(), -b.l - VT{1}); }
      // if(b.u < 0 && l > 0) { return basic_type(-b.u + VT{1}, UB2:top()); }
      // if(b.u < 0 && u < 0) { return basic_type(LB2::top(), b.u - VT{1}); }
    }
    else {
      basic_type r(*this);
      r.tdiv_den(basic_type(0, 0), b);
      r.join(basic_type::top().cdiv_den(basic_type(a.l, -1), b));
      r.join(basic_type::top().fdiv_den(basic_type(1, a.u), b));
      meet(r);
    }
    return *this;
  }

  // Let a = ediv(b, x), this function updates the denominator x according to a and b.
  // precondition: lb() != 0 && ub() != 0
  CUDA INLINE constexpr this_type& ediv_den(basic_type a, basic_type b) {
    assert(l != 0 && u != 0);
    if(a.is_bot() || b.is_bot() || is_bot()) { meet_bot(); }
    else if(l > 0) { fdiv_den(a, b); }
    else if(u < 0) { cdiv_den(a, b); }
    else {
      meet(::lala::join(
        basic_type::top().fdiv_den(a, b),
        basic_type::top().cdiv_den(a, b)));
    }
    return *this;
  }
};

// Lattice operations

template <class VT, class Mem>
CUDA INLINE constexpr ZInterval<VT, Mem> join(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b) {
  a.join(b);
  return a;
}

template <class VT, class Mem>
CUDA INLINE constexpr ZInterval<VT, Mem> meet(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b) {
  a.meet(b);
  return a;
}

template <class VT, class Mem>
CUDA INLINE constexpr ZInterval<VT, Mem> join_nobot(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b) {
  a.join_nobot(b);
  return a;
}

template<class VT, class Mem1, class Mem2>
CUDA INLINE constexpr bool operator==(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return a.eq(b);
}

template<class VT, class Mem1, class Mem2>
CUDA INLINE constexpr bool operator!=(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return !(a == b);
}

template<class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const ZInterval<VT, Mem> &itv) {
  return s << "[" << itv.lb() << "," << itv.ub() << "]";
}

namespace tell {

template<class VT>
CUDA INLINE constexpr void zadd(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  x.add(y, z);
  y.sub(x, z);
  z.sub(x, y);
}

template<class VT>
CUDA INLINE constexpr void zsub(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  zadd(y, x, z);
}

/** Infinity-aware addition/subtraction (battery::limits sentinel encoding).
    Precondition of use: the two operands never combine opposite infinities
    (guaranteed by the hull corners below: lower corners are never +oo and
    upper corners never -oo on non-empty intervals). */
template<class VT>
CUDA INLINE constexpr VT iadd(VT a, VT b) {
  const VT inf = battery::limits<VT>::inf();
  const VT ninf = battery::limits<VT>::neg_inf();
  if(a == inf || a == ninf) { return a; }
  if(b == inf || b == ninf) { return b; }
  return a + b;
}
template<class VT>
CUDA INLINE constexpr VT isub(VT a, VT b) {
  const VT inf = battery::limits<VT>::inf();
  const VT ninf = battery::limits<VT>::neg_inf();
  if(a == inf || a == ninf) { return a; }
  if(b == inf) { return ninf; }
  if(b == ninf) { return inf; }
  return a - b;
}

/** Infinity-aware arithmetic on VT with the battery::limits sentinel encoding
    (min = -oo, max = +oo).  Each operation returns the LIMIT value of its
    finite counterpart, so the corner formulas of the propagator compute the
    exact bound of their projection even on unbounded intervals. */

// Saturating addition of a small finite shift (the +-1 of the band formulas).
template<class VT>
CUDA INLINE constexpr VT sadd(VT a, VT b) {
  return (a == battery::limits<VT>::inf() || a == battery::limits<VT>::neg_inf()) ? a : a + b;
}

// Multiplication with the sign rule and 0 * oo = 0 (exact for interval hulls).
template<class VT>
CUDA INLINE constexpr VT imul(VT a, VT b) {
  const VT inf = battery::limits<VT>::inf();
  const VT ninf = battery::limits<VT>::neg_inf();
  if(a == VT{0} || b == VT{0}) { return VT{0}; }
  if(a == inf)  { return b > VT{0} ? inf : ninf; }
  if(a == ninf) { return b > VT{0} ? ninf : inf; }
  if(b == inf)  { return a > VT{0} ? inf : ninf; }
  if(b == ninf) { return a > VT{0} ? ninf : inf; }
  return a * b;
}

// floor(n/m) with limit semantics; precondition: m != 0.
// For an infinite divisor the quotient is the eventual value of floor(n/z)
// (0 when the signs agree, -1 otherwise) -- uniformly correct, including for
// infinite n, in every min/max corner expression where it occurs.
template<class VT>
CUDA INLINE constexpr VT idiv_f(VT n, VT m) {
  const VT inf = battery::limits<VT>::inf();
  const VT ninf = battery::limits<VT>::neg_inf();
  if(m == inf)  { return n < VT{0} ? VT{-1} : VT{0}; }
  if(m == ninf) { return n > VT{0} ? VT{-1} : VT{0}; }
  if(n == inf)  { return m > VT{0} ? inf : ninf; }
  if(n == ninf) { return m > VT{0} ? ninf : inf; }
  return battery::fdiv<VT>(n, m);
}

// ceil(n/m) with limit semantics; precondition: m != 0.
template<class VT>
CUDA INLINE constexpr VT idiv_c(VT n, VT m) {
  const VT inf = battery::limits<VT>::inf();
  const VT ninf = battery::limits<VT>::neg_inf();
  if(m == inf)  { return n > VT{0} ? VT{1} : VT{0}; }
  if(m == ninf) { return n < VT{0} ? VT{1} : VT{0}; }
  if(n == inf)  { return m > VT{0} ? inf : ninf; }
  if(n == ninf) { return m > VT{0} ? ninf : inf; }
  return battery::cdiv<VT>(n, m);
}

// trunc(n/m) with limit semantics; precondition: m != 0.
template<class VT>
CUDA INLINE constexpr VT idiv_t(VT n, VT m) {
  const VT inf = battery::limits<VT>::inf();
  const VT ninf = battery::limits<VT>::neg_inf();
  if(m == inf || m == ninf) { return VT{0}; }
  if(n == inf)  { return m > VT{0} ? inf : ninf; }
  if(n == ninf) { return m > VT{0} ? ninf : inf; }
  return battery::tdiv<VT>(n, m);
}

template<class VT>
CUDA INLINE constexpr VT ineg(VT a) {
  const VT inf = battery::limits<VT>::inf();
  const VT ninf = battery::limits<VT>::neg_inf();
  return a == inf ? ninf : (a == ninf ? inf : static_cast<VT>(-a));
}

// x = y * z with PRECISE infinite-bound reasoning. Constant time, no
// recursion: one 4-corner product hull per direction, division-back with
// idiv_c/idiv_f corner hulls when the divisor is sign-definite, and the
// absolute-value bound when it straddles zero (|b| >= 1 on solutions).
template<class VT>
CUDA INLINE constexpr void zmul3(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::min;
  using battery::max;
  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }

  // MUL (x <- x meet y*z)
  x.lb().meet(min(min(imul<VT>(y.lb(), z.lb()), imul<VT>(y.lb(), z.ub())),
                  min(imul<VT>(y.ub(), z.lb()), imul<VT>(y.ub(), z.ub()))));
  x.ub().meet(max(max(imul<VT>(y.lb(), z.lb()), imul<VT>(y.lb(), z.ub())),
                  max(imul<VT>(y.ub(), z.lb()), imul<VT>(y.ub(), z.ub()))));
  if(x.is_bot()) { return; }

  const bool xnz = (x.lb() > VT{0} || x.ub() < VT{0});
  // z.mul_back_zero(x)
  if(xnz) { z.neq_zero(); }
  if(z.is_bot()) { return; }
  // y.mul_back_nz(x, z): on solutions y = x / z exactly, so the cdiv/fdiv
  // corner hull is sound; straddling z with 0 notin x gives |y| <= |x|.
  if(z.lb() > VT{0} || z.ub() < VT{0}) {
    y.lb().meet(min(min(idiv_c<VT>(x.lb(), z.lb()), idiv_c<VT>(x.lb(), z.ub())),
                    min(idiv_c<VT>(x.ub(), z.lb()), idiv_c<VT>(x.ub(), z.ub()))));
    y.ub().meet(max(max(idiv_f<VT>(x.lb(), z.lb()), idiv_f<VT>(x.lb(), z.ub())),
                    max(idiv_f<VT>(x.ub(), z.lb()), idiv_f<VT>(x.ub(), z.ub()))));
  }
  else if(xnz) {
    y.lb().meet(min<VT>(x.lb(), ineg<VT>(x.ub())));
    y.ub().meet(max<VT>(ineg<VT>(x.lb()), x.ub()));
  }
  if(y.is_bot()) { return; }
  // y.mul_back_zero(x)
  if(xnz) { y.neq_zero(); }
  if(y.is_bot()) { return; }
  // z.mul_back_nz(x, y)
  if(y.lb() > VT{0} || y.ub() < VT{0}) {
    z.lb().meet(min(min(idiv_c<VT>(x.lb(), y.lb()), idiv_c<VT>(x.lb(), y.ub())),
                    min(idiv_c<VT>(x.ub(), y.lb()), idiv_c<VT>(x.ub(), y.ub()))));
    z.ub().meet(max(max(idiv_f<VT>(x.lb(), y.lb()), idiv_f<VT>(x.lb(), y.ub())),
                    max(idiv_f<VT>(x.ub(), y.lb()), idiv_f<VT>(x.ub(), y.ub()))));
  }
  else if(xnz) {
    z.lb().meet(min<VT>(x.lb(), ineg<VT>(x.ub())));
    z.ub().meet(max<VT>(ineg<VT>(x.lb()), x.ub()));
  }
  if(z.is_bot()) { return; }

  // MUL (x <- x meet y*z)
  x.lb().meet(min(min(imul<VT>(y.lb(), z.lb()), imul<VT>(y.lb(), z.ub())),
                  min(imul<VT>(y.ub(), z.lb()), imul<VT>(y.ub(), z.ub()))));
  x.ub().meet(max(max(imul<VT>(y.lb(), z.lb()), imul<VT>(y.lb(), z.ub())),
                  max(imul<VT>(y.ub(), z.lb()), imul<VT>(y.ub(), z.ub()))));
}

// x = y + z with PRECISE infinite-bound reasoning: hull meets always run;
// an infinite corner yields an infinite candidate whose meet is a no-op.
template<class VT>
CUDA INLINE constexpr void zadd3(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }
  // x <- x meet (y + z)
  x.lb().meet(iadd<VT>(y.lb(), z.lb()));
  x.ub().meet(iadd<VT>(y.ub(), z.ub()));
  if(x.is_bot()) { return; }
  // y <- y meet (x - z)
  y.lb().meet(isub<VT>(x.lb(), z.ub()));
  y.ub().meet(isub<VT>(x.ub(), z.lb()));
  if(y.is_bot()) { return; }
  // z <- z meet (x - y)
  z.lb().meet(isub<VT>(x.lb(), y.ub()));
  z.ub().meet(isub<VT>(x.ub(), y.lb()));
}

template<class VT>
CUDA INLINE constexpr void zmul(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  x.mul(y, z);
  z.mul_back_zero(x);
  y.mul_back_nz(x, z);
  y.mul_back_zero(x);
  z.mul_back_nz(x, y);
  x.mul(y, z);
}

template<class VT>
CUDA INLINE constexpr void zfdiv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  z.neq_zero();
  x.fdiv(y, z);
  z.fdiv_den(x, y);
  y.fdiv_num(x, z);
  z.neq_zero();
  x.fdiv(y, z);
}

// Must be used in cooperation with split on z.
// precondition: z <= 0 || z >= 0
template<class VT>
CUDA INLINE constexpr void zfdiv_fast2(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::fdiv;
  using battery::cdiv;
  using battery::min;
  using battery::max;
  z.neq_zero();
  // assert(z.ub() < 0 || z.lb() > 0);
  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }
  if(x.l.is_top() || x.u.is_top() || y.l.is_top() || y.u.is_top() || z.l.is_top() || z.u.is_top()) { return; }

  // DIV (x.fdiv(y, z);)
  // When we split on `z`, this part of the code is useless.
  // if(z.l < 0 && z.u > 0) {
  //   if(!y.u.is_top()) { x.l.meet(min<VT>(y.l, -y.u)); }
  //   if(!y.l.is_top()) { x.u.meet(max<VT>(-y.l, y.u)); }
  // }
  // else {
    x.l.meet(min(min(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), min(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
    x.u.meet(max(max(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), max(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
  // }
  if(x.is_bot()) { return; }

  // DEN (z.fdiv_den(x, y);)
  if(y.l <= 0 && y.u >= 0 && x.l <= 0 && x.u >= 0) {
    // skip, there is nothing we can do.
  }
  else {
    if(x.l > 0) {
      // z.l.meet(min<VT>(cdiv<VT>(y.l, x.l), fdiv<VT>(max<VT>(1,y.l), x.u + VT{1}) + VT{1}));
      // z.u.meet(max<VT>(cdiv<VT>(min<VT>(-1, y.u), x.u + VT{1}) - VT{1}, fdiv<VT>(y.u, x.l)));
      if(y.l >= 0 && y.u > 0) {
        z.l.meet(fdiv<VT>(max<VT>(1,y.l), x.u + VT{1}) + VT{1});
        z.u.meet(fdiv<VT>(y.u, x.l));
      }
      else if(y.u < 0 && y.l <= 0) {
        z.l.meet(cdiv<VT>(y.l, x.l));
        z.u.meet(cdiv<VT>(min<VT>(-1, y.u), x.u + VT{1}) - VT{1});
      }
      else {
        z.l.meet(cdiv<VT>(y.l, x.l));
        z.u.meet(fdiv<VT>(y.u, x.l));
      }
    }
    else if(x.u < VT{-1}) {
      // z.l.meet(min<VT>(cdiv<VT>(min<VT>(-1, y.u), x.l), fdiv<VT>(y.u, x.u + VT{1}) + VT{1}));
      // z.u.meet(max<VT>(cdiv<VT>(y.l, x.u + VT{1}) - VT{1}, fdiv<VT>(max<VT>(1, y.l), x.l)));
      if(y.l >= 0 && y.u > 0) {
        z.l.meet(fdiv<VT>(y.u, x.u + VT{1}) + VT{1});
        z.u.meet(fdiv<VT>(y.l, x.l));
      }
      else if(y.l < 0 && y.u <= 0) {
        z.l.meet(cdiv<VT>(y.u, x.l));
        z.u.meet(cdiv<VT>(y.l, x.u + VT{1}) - VT{1});
      }
      else {
        z.l.meet(fdiv<VT>(y.u, x.u + VT{1}) + VT{1});
        z.u.meet(cdiv<VT>(y.l, x.u + VT{1}) - VT{1});
      }
    }
    else if(x.is_singleton(VT{0})) {
      if(y.u < 0) { z.u.meet(y.u - VT{1}); }
      else /* if(y.l > 0) */ { z.l.meet(y.l + VT{1}); }
    }
    else if(x.l <= -1 && x.u == -1) {
      if(y.l < 0 && y.u <= 0) { z.l.meet(cdiv<VT>(min<VT>(-1, y.u), x.l)); }
      else if(y.u > 0 && y.l >= 0) { z.u.meet(fdiv<VT>(max<VT>(1, y.l), x.l)); }
      else if(y.l == 0 && y.u == 0) { z.meet_bot(); }
    }
    else if(x.l == 0 && x.u > 0) {
      if(y.l < 0 && y.u <= 0) { z.u.meet(cdiv<VT>(min<VT>(-1, y.u), x.u + VT{1}) - VT{1}); }
      else if(y.u > 0 && y.l >= 0) { z.l.meet(fdiv<VT>(max<VT>(1, y.l), x.u + VT{1}) + VT{1}); }
    }
    else {
      // assert(false);
      // never reached after `div`.
    }
    if(z.is_bot()) { return; }
  }
  z.neq_zero();
  // NUM (y.fdiv_num(x, z);)
  y.l.meet(min(min<VT>(x.l * z.l, x.l * z.u), min<VT>((x.u + VT{1}) * z.l + VT{1}, (x.u + VT{1}) * z.u + VT{1})));
  y.u.meet(max(max<VT>(x.l * z.l, x.l * z.u), max<VT>((x.u + VT{1}) * z.l - VT{1}, (x.u + VT{1}) * z.u - VT{1})));
  if(y.is_bot()) { return; }

  // DIV (x.fdiv(y, z);)
  // When we split on `z`, this part of the code is useless.
  // if(z.l < 0 && z.u > 0) {
  //   if(!y.u.is_top()) { x.l.meet(min<VT>(y.l, -y.u)); }
  //   if(!y.l.is_top()) { x.u.meet(max<VT>(-y.l, y.u)); }
  // }
  // else {
    x.l.meet(min(min(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), min(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
    x.u.meet(max(max(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), max(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
  // }
}

template<class VT>
CUDA INLINE constexpr void zcdiv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  z.neq_zero();
  x.cdiv(y, z);
  z.cdiv_den(x, y);
  y.cdiv_num(x, z);
  z.neq_zero();
  x.cdiv(y, z);
}

template<class VT>
CUDA INLINE constexpr void ztdiv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  z.neq_zero();
  x.tdiv(y, z);
  z.tdiv_den(x, y);
  y.tdiv_num(x, z);
  z.neq_zero();
  x.tdiv(y, z);
}

template<class VT>
CUDA INLINE constexpr void zediv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  z.neq_zero();
  x.ediv(y, z);
  z.ediv_den(x, y);
  y.ediv_num(x, z);
  z.neq_zero();
  x.ediv(y, z);
}

template <class VT, class Prop>
CUDA void splitjoin(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z, ZInterval<VT>& r, VT a, Prop prop) {
  using battery::min;
  using battery::max;
  if(!r.contains(a) || r.is_singleton()) {
    prop(x, y, z);
  }
  else {
    ZInterval<VT> r2(r);
    r.ub() = min<VT>(r.ub(), a - VT{1});
    ZInterval<VT> x2(x), y2(y), z2(z); // note: must be declared after modifying `r` since `r` is either x, y, or z.
    prop(x2, y2, z2);
    r = r2;
    r.lb() = max<VT>(r.lb(), a);
    prop(x, y, z);
    if(x2.is_bot() || y2.is_bot() || z2.is_bot()) { return; }
    if(x.is_bot() || y.is_bot() || z.is_bot()) { x = x2; y = y2; z = z2; return; }
    x.join(x2);
    y.join(y2);
    z.join(z2);
    // prop(x,y,z);
  }
}

template<class VT>
CUDA INLINE constexpr void zfdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, VT{0}, zfdiv_fast2<VT>);
}

template<class VT>
CUDA INLINE constexpr void zfdiv2(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::fdiv;
  using battery::cdiv;
  using battery::min;
  using battery::max;

  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }
  if(x.l.is_top() || x.u.is_top() || y.l.is_top() || y.u.is_top() || z.l.is_top() || z.u.is_top()) { return; }

  ZInterval<VT> x2(x), z2(z);

  // CASE 1: z is positive.
  z.lb().meet(VT{1});
  if(!z.is_bot()) {
    // DIV (x.fdiv(y, z);)
    x.l.meet(min(min(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), min(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
    x.u.meet(max(max(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), max(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
    if(x.is_bot()) { goto negz; }

    // A: x.l * z <= y.u
    if(x.l > VT{0}) { z.u.meet(fdiv<VT>(y.u, x.l)); }
    else if(x.l != VT{0}) { z.l.meet(cdiv<VT>(y.u, x.l)); }
    else if(y.u < VT{0}) { z.meet_bot(); }
    // B: (x.u + 1) * z >= y.l + 1
    if(x.u > VT{-1}) { z.l.meet(cdiv<VT>(y.l + VT{1}, x.u + VT{1})); }
    else if(x.u != VT{-1}) { z.u.meet(fdiv<VT>(y.l + VT{1}, x.u + VT{1})); }
    else if(y.l >= VT{0}) { z.meet_bot(); }
    if(z.is_bot()) { goto negz; }

    // DIV (x.fdiv(y, z);)
    x.l.meet(min(min(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), min(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
    x.u.meet(max(max(fdiv<VT>(y.l, z.l), fdiv<VT>(y.l, z.u)), max(fdiv<VT>(y.u, z.l), fdiv<VT>(y.u, z.u))));
  }

negz:
  // CASE 2: z is negative.
  z2.ub().meet(VT{-1});
  if(!z2.is_bot()) {
    // DIV (x.fdiv(y, z);)
    x2.l.meet(min(min(fdiv<VT>(y.l, z2.l), fdiv<VT>(y.l, z2.u)), min(fdiv<VT>(y.u, z2.l), fdiv<VT>(y.u, z2.u))));
    x2.u.meet(max(max(fdiv<VT>(y.l, z2.l), fdiv<VT>(y.l, z2.u)), max(fdiv<VT>(y.u, z2.l), fdiv<VT>(y.u, z2.u))));
    if(x2.is_bot()) { goto join; }

    // A: x2.l * z2 >= y.l
    if(x2.l > VT{0}) { z2.l.meet(cdiv<VT>(y.l, x2.l)); }
    else if(x2.l != VT{0}) { z2.u.meet(fdiv<VT>(y.l, x2.l)); }
    else if(y.l > VT{0}) { z2.meet_bot(); }
    // B: (x2.u + 1) * z2 <= y.u - 1
    if(x2.u > VT{-1}) { z2.u.meet(fdiv<VT>(y.u - VT{1}, x2.u + VT{1})); }
    else if(x2.u != VT{-1}) { z2.l.meet(cdiv<VT>(y.u - VT{1}, x2.u + VT{1})); }
    else if(y.u <= VT{0}) { z2.meet_bot(); }
    if(z2.is_bot()) { goto join; }

    // DIV (x2.fdiv(y, z);)
    x2.l.meet(min(min(fdiv<VT>(y.l, z2.l), fdiv<VT>(y.l, z2.u)), min(fdiv<VT>(y.u, z2.l), fdiv<VT>(y.u, z2.u))));
    x2.u.meet(max(max(fdiv<VT>(y.l, z2.l), fdiv<VT>(y.l, z2.u)), max(fdiv<VT>(y.u, z2.l), fdiv<VT>(y.u, z2.u))));
  }

join:
  if(x.is_bot() || z.is_bot()) {
    x = x2;
    z = z2;
  }
  else if(!x2.is_bot() && !z2.is_bot()) {
    x.join(x2);
    z.join(z2);
  }

  // NUM (y.fdiv_num(x, z);)
  y.l.meet(min(min<VT>(x.l * z.l, x.l * z.u), min<VT>((x.u + VT{1}) * z.l + VT{1}, (x.u + VT{1}) * z.u + VT{1})));
  y.u.meet(max(max<VT>(x.l * z.l, x.l * z.u), max<VT>((x.u + VT{1}) * z.l - VT{1}, (x.u + VT{1}) * z.u - VT{1})));
}

// zfdiv2 with PRECISE infinite-bound reasoning: the is_top bail-out is gone;
// every corner operation goes through the infinity-aware helpers, so the
// propagator refines exactly as much as the finite-bound one would in the
// limit.  Structure identical to zfdiv2 (band DEN, per-sign branches, join,
// NUM hull).
template<class VT>
CUDA INLINE constexpr void zfdiv3(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::min;
  using battery::max;

  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }

  ZInterval<VT> x2(x), z2(z);

  // CASE 1: z is positive.
  z.lb().meet(VT{1});
  if(!z.is_bot()) {
    // DIV (x.fdiv(y, z);)
    x.l.meet(min(min(idiv_f<VT>(y.l, z.l), idiv_f<VT>(y.l, z.u)), min(idiv_f<VT>(y.u, z.l), idiv_f<VT>(y.u, z.u))));
    x.u.meet(max(max(idiv_f<VT>(y.l, z.l), idiv_f<VT>(y.l, z.u)), max(idiv_f<VT>(y.u, z.l), idiv_f<VT>(y.u, z.u))));
    if(x.is_bot()) { goto negz; }

    // A: x.l * z <= y.u
    if(x.l > VT{0}) { z.u.meet(idiv_f<VT>(y.u, x.l)); }
    else if(x.l != VT{0}) { z.l.meet(idiv_c<VT>(y.u, x.l)); }
    else if(y.u < VT{0}) { z.meet_bot(); }
    // B: (x.u + 1) * z >= y.l + 1
    if(x.u > VT{-1}) { z.l.meet(idiv_c<VT>(sadd<VT>(y.l, VT{1}), sadd<VT>(x.u, VT{1}))); }
    else if(x.u != VT{-1}) { z.u.meet(idiv_f<VT>(sadd<VT>(y.l, VT{1}), sadd<VT>(x.u, VT{1}))); }
    else if(y.l >= VT{0}) { z.meet_bot(); }
    if(z.is_bot()) { goto negz; }

    // DIV (x.fdiv(y, z);)
    x.l.meet(min(min(idiv_f<VT>(y.l, z.l), idiv_f<VT>(y.l, z.u)), min(idiv_f<VT>(y.u, z.l), idiv_f<VT>(y.u, z.u))));
    x.u.meet(max(max(idiv_f<VT>(y.l, z.l), idiv_f<VT>(y.l, z.u)), max(idiv_f<VT>(y.u, z.l), idiv_f<VT>(y.u, z.u))));
  }

negz:
  // CASE 2: z is negative.
  z2.ub().meet(VT{-1});
  if(!z2.is_bot()) {
    // DIV (x.fdiv(y, z);)
    x2.l.meet(min(min(idiv_f<VT>(y.l, z2.l), idiv_f<VT>(y.l, z2.u)), min(idiv_f<VT>(y.u, z2.l), idiv_f<VT>(y.u, z2.u))));
    x2.u.meet(max(max(idiv_f<VT>(y.l, z2.l), idiv_f<VT>(y.l, z2.u)), max(idiv_f<VT>(y.u, z2.l), idiv_f<VT>(y.u, z2.u))));
    if(x2.is_bot()) { goto join; }

    // A: x2.l * z2 >= y.l
    if(x2.l > VT{0}) { z2.l.meet(idiv_c<VT>(y.l, x2.l)); }
    else if(x2.l != VT{0}) { z2.u.meet(idiv_f<VT>(y.l, x2.l)); }
    else if(y.l > VT{0}) { z2.meet_bot(); }
    // B: (x2.u + 1) * z2 <= y.u - 1
    if(x2.u > VT{-1}) { z2.u.meet(idiv_f<VT>(sadd<VT>(y.u, VT{-1}), sadd<VT>(x2.u, VT{1}))); }
    else if(x2.u != VT{-1}) { z2.l.meet(idiv_c<VT>(sadd<VT>(y.u, VT{-1}), sadd<VT>(x2.u, VT{1}))); }
    else if(y.u <= VT{0}) { z2.meet_bot(); }
    if(z2.is_bot()) { goto join; }

    // DIV (x2.fdiv(y, z);)
    x2.l.meet(min(min(idiv_f<VT>(y.l, z2.l), idiv_f<VT>(y.l, z2.u)), min(idiv_f<VT>(y.u, z2.l), idiv_f<VT>(y.u, z2.u))));
    x2.u.meet(max(max(idiv_f<VT>(y.l, z2.l), idiv_f<VT>(y.l, z2.u)), max(idiv_f<VT>(y.u, z2.l), idiv_f<VT>(y.u, z2.u))));
  }

join:
  if(x.is_bot() || z.is_bot()) {
    x = x2;
    z = z2;
  }
  else if(!x2.is_bot() && !z2.is_bot()) {
    x.join(x2);
    z.join(z2);
  }

  // NUM (y.fdiv_num(x, z);)
  y.l.meet(min(min<VT>(imul<VT>(x.l, z.l), imul<VT>(x.l, z.u)),
               min<VT>(sadd<VT>(imul<VT>(sadd<VT>(x.u, VT{1}), z.l), VT{1}),
                       sadd<VT>(imul<VT>(sadd<VT>(x.u, VT{1}), z.u), VT{1}))));
  y.u.meet(max(max<VT>(imul<VT>(x.l, z.l), imul<VT>(x.l, z.u)),
               max<VT>(sadd<VT>(imul<VT>(sadd<VT>(x.u, VT{1}), z.l), VT{-1}),
                       sadd<VT>(imul<VT>(sadd<VT>(x.u, VT{1}), z.u), VT{-1}))));
}

template<class VT>
CUDA INLINE constexpr void zcdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, VT{0}, zcdiv_fast<VT>);
}

template<class VT>
CUDA INLINE constexpr void ztdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, VT{0}, ztdiv_fast<VT>);
}

template<class VT>
CUDA INLINE constexpr void zediv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, VT{0}, zediv_fast<VT>);
}

template<class VT>
CUDA INLINE constexpr void zmin(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  x.min(y, z);
  y.min_back(x, z);
  z.min_back(x, y);
}

template<class VT>
CUDA INLINE constexpr void zmax(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  x.max(y, z);
  y.max_back(x, z);
  z.max_back(x, y);
}

template<class VT>
CUDA INLINE constexpr void zreq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  x.meet(ZInterval<VT>(VT{0}, VT{1}));
  x.req(y, z);
  y.req_back(x, z);
  z.req_back(x, y);
}

template<class VT>
CUDA INLINE constexpr void zrleq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  x.meet(ZInterval<VT>(VT{0}, VT{1}));
  x.rleq(y, z);
  y.rleq_lback(x, z);
  z.rleq_rback(x, y);
}

} // namespace tell

namespace ask {

template<class VT>
CUDA INLINE constexpr bool zadd(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.is_singleton() && y.is_singleton() && z.is_singleton() && x.lb() == y.lb() + z.lb());
}

template<class VT>
CUDA INLINE constexpr bool zsub(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return zadd(y, x, z);
}

template<class VT>
CUDA INLINE constexpr bool zmul(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.is_singleton() &&
      ((y.is_singleton() && z.is_singleton() && x.lb() == y.lb() * z.lb()) ||
      (x.lb() == VT{0} && (y.is_singleton(0) || z.is_singleton(0)))));
}

template<class VT>
CUDA INLINE constexpr bool zfdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::fdiv<VT>(y.lb(), z.lb())) ||
             (x.lb() ==  VT{0} && y.lb() ==  VT{0}))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool zcdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::cdiv<VT>(y.lb(), z.lb())) ||
             (x.lb() ==  VT{0} && y.lb() ==  VT{0}))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool ztdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::tdiv<VT>(y.lb(), z.lb())) ||
             (x.lb() ==  VT{0} && y.lb() ==  VT{0}))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool zediv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::ediv<VT>(y.lb(), z.lb())) ||
             (x.lb() ==  VT{0} && y.lb() ==  VT{0}))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool zmin(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.lb() == y.ub() && x.ub() == y.lb() && y.ub() <= z.lb()) ||
    (x.lb() == z.ub() && x.ub() == z.lb() && z.ub() <= y.lb());
}

template<class VT>
CUDA INLINE constexpr bool zmax(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.lb() == y.ub() && x.ub() == y.lb() && y.lb() >= z.ub()) ||
    (x.lb() == z.ub() && x.ub() == z.lb() && z.lb() >= y.ub());
}

// precondition: x <= [0,1]
template<class VT>
CUDA INLINE constexpr bool zreq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.lb() == VT{1} && y.ub() == z.lb() && y.lb() == z.ub()) ||
    (x.ub() == VT{0} && (y.ub() < z.lb() || y.lb() > z.ub()));
}

// precondition: x <= [0,1]
template<class VT>
CUDA INLINE constexpr bool zrleq(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.lb() == VT{1} && y.ub() <= z.lb()) ||
    (x.ub() == VT{0} && y.lb() > z.ub());
}

} // namespace ask

namespace tell {

/** Propagators x = y / z (z != 0) for the four integer division roundings,
    with PRECISE infinite-bound reasoning.  One-pass slice decomposition:
    z is split into its positive slice ([1, +oo]) and negative slice
    ([-oo, -1]).  Within a slice, `div(y, z) in [x.lb, x.ub]` is equivalent
    to `y in [ymin(z), ymax(z)]` where the band endpoints are linear in z
    with coefficients of known sign, hence:
      Z: the feasible z form a contiguous range computed exactly by
         comparing the band with [y.lb, y.ub] (one division per inequality);
      Y: y is narrowed to the hull of the band endpoints over the narrowed
         z (the endpoints are monotone in z);
      X: x is narrowed to the 4-corner hull of the division (monotone in y,
         and in z for each fixed y).
    The two slices are then joined back into x, y, z.  Only two positive-
    slice solvers are needed (ztdiv_pos and zfdiv_pos); every other case
    reduces to them through the mirror identities
      trunc(y/z) = -trunc(y/(-z))        floor(y/z) = floor((-y)/(-z))
      ceil(y/z)  = -floor((-y)/z)        ceil(y/z)  = -floor(y/(-z))
    applied by mirroring the intervals of x, y and/or z.  Every corner
    computation goes through the infinity-aware helpers (imul, sadd,
    idiv_*), so unbounded intervals refine exactly as much as bounded ones
    would in the limit.  Only the copies needed to join the two slices are
    used. */

// [l, u] := [-u, -l], with the sentinel encoding (bot maps to bot).
template<class VT>
CUDA INLINE constexpr void zmirror(ZInterval<VT>& a) {
  a = ZInterval<VT>(ineg<VT>(a.ub()), ineg<VT>(a.lb()));
}

// Contracts x, y, z for x = tdiv(y, z) (truncated division) on the positive
// slice of z: z is first met with [1, +oo]; x and y are only narrowed if the
// slice is feasible (z not bot on exit).
// For z >= 1: tdiv(y, z) in [x.lb, x.ub]  <=>  y in [tymin(x.lb, z), tymax(x.ub, z)]
//   with tymin(v, z) = v > 0 ? v*z : (v-1)*z + 1
//   and  tymax(v, z) = v >= 0 ? (v+1)*z - 1 : v*z.
template<class VT>
CUDA INLINE constexpr void ztdiv_pos(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::min;
  using battery::max;
  z.lb().meet(VT{1});
  if(z.is_bot()) { return; }

  // Z: tymin(x.lb, z) <= y.ub
  if(x.lb() > VT{0}) { z.ub().meet(idiv_f<VT>(y.ub(), x.lb())); } // x.lb * z <= y.ub
  else { z.lb().meet(idiv_c<VT>(sadd<VT>(y.ub(), VT{-1}), sadd<VT>(x.lb(), VT{-1}))); } // (x.lb - 1) * z <= y.ub - 1
  // Z: tymax(x.ub, z) >= y.lb
  if(x.ub() >= VT{0}) { z.lb().meet(idiv_c<VT>(sadd<VT>(y.lb(), VT{1}), sadd<VT>(x.ub(), VT{1}))); } // (x.ub + 1) * z >= y.lb + 1
  else { z.ub().meet(idiv_f<VT>(y.lb(), x.ub())); } // x.ub * z >= y.lb
  if(z.is_bot()) { return; }

  // Y: hull of [tymin(x.lb, z), tymax(x.ub, z)] over the narrowed z.
  if(x.lb() > VT{0}) {
    y.lb().meet(min(imul<VT>(x.lb(), z.lb()), imul<VT>(x.lb(), z.ub())));
  }
  else {
    y.lb().meet(min(sadd<VT>(imul<VT>(sadd<VT>(x.lb(), VT{-1}), z.lb()), VT{1}),
                    sadd<VT>(imul<VT>(sadd<VT>(x.lb(), VT{-1}), z.ub()), VT{1})));
  }
  if(x.ub() >= VT{0}) {
    y.ub().meet(max(sadd<VT>(imul<VT>(sadd<VT>(x.ub(), VT{1}), z.lb()), VT{-1}),
                    sadd<VT>(imul<VT>(sadd<VT>(x.ub(), VT{1}), z.ub()), VT{-1})));
  }
  else {
    y.ub().meet(max(imul<VT>(x.ub(), z.lb()), imul<VT>(x.ub(), z.ub())));
  }
  if(y.is_bot()) { return; }

  // X: 4-corner hull of tdiv(y, z).
  x.lb().meet(min(min(idiv_t<VT>(y.lb(), z.lb()), idiv_t<VT>(y.lb(), z.ub())),
                  min(idiv_t<VT>(y.ub(), z.lb()), idiv_t<VT>(y.ub(), z.ub()))));
  x.ub().meet(max(max(idiv_t<VT>(y.lb(), z.lb()), idiv_t<VT>(y.lb(), z.ub())),
                  max(idiv_t<VT>(y.ub(), z.lb()), idiv_t<VT>(y.ub(), z.ub()))));
}

// Contracts x, y, z for x = fdiv(y, z) (floor division) on the positive
// slice of z: z is first met with [1, +oo]; x and y are only narrowed if the
// slice is feasible (z not bot on exit).
// For z >= 1: fdiv(y, z) in [x.lb, x.ub]  <=>  y in [x.lb*z, (x.ub+1)*z - 1].
template<class VT>
CUDA INLINE constexpr void zfdiv_pos(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  using battery::min;
  using battery::max;
  z.lb().meet(VT{1});
  if(z.is_bot()) { return; }

  // Z: x.lb * z <= y.ub
  if(x.lb() > VT{0}) { z.ub().meet(idiv_f<VT>(y.ub(), x.lb())); }
  else if(x.lb() != VT{0}) { z.lb().meet(idiv_c<VT>(y.ub(), x.lb())); }
  else if(y.ub() < VT{0}) { z.meet_bot(); }
  // Z: (x.ub + 1) * z >= y.lb + 1
  if(x.ub() > VT{-1}) { z.lb().meet(idiv_c<VT>(sadd<VT>(y.lb(), VT{1}), sadd<VT>(x.ub(), VT{1}))); }
  else if(x.ub() != VT{-1}) { z.ub().meet(idiv_f<VT>(sadd<VT>(y.lb(), VT{1}), sadd<VT>(x.ub(), VT{1}))); }
  else if(y.lb() >= VT{0}) { z.meet_bot(); }
  if(z.is_bot()) { return; }

  // Y: hull of [x.lb*z, (x.ub+1)*z - 1] over the narrowed z.
  y.lb().meet(min(imul<VT>(x.lb(), z.lb()), imul<VT>(x.lb(), z.ub())));
  y.ub().meet(max(sadd<VT>(imul<VT>(sadd<VT>(x.ub(), VT{1}), z.lb()), VT{-1}),
                  sadd<VT>(imul<VT>(sadd<VT>(x.ub(), VT{1}), z.ub()), VT{-1})));
  if(y.is_bot()) { return; }

  // X: 4-corner hull of fdiv(y, z).
  x.lb().meet(min(min(idiv_f<VT>(y.lb(), z.lb()), idiv_f<VT>(y.lb(), z.ub())),
                  min(idiv_f<VT>(y.ub(), z.lb()), idiv_f<VT>(y.ub(), z.ub()))));
  x.ub().meet(max(max(idiv_f<VT>(y.lb(), z.lb()), idiv_f<VT>(y.lb(), z.ub())),
                  max(idiv_f<VT>(y.ub(), z.lb()), idiv_f<VT>(y.ub(), z.ub()))));
}

// x = tdiv(y, z) (truncated division), z != 0.
template<class VT>
CUDA INLINE constexpr void ztdiv_4(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }
  ZInterval<VT> x2(x), y2(y), z2(z);
  // CASE 1: z is positive.
  ztdiv_pos(x, y, z);
  // CASE 2: z is negative: trunc(y/z) = -trunc(y/(-z)).
  zmirror(x2);
  zmirror(z2);
  ztdiv_pos(x2, y2, z2);
  zmirror(x2);
  zmirror(z2);
  if(x.is_bot() || y.is_bot() || z.is_bot()) {
    x = x2;
    y = y2;
    z = z2;
  }
  else if(!x2.is_bot() && !y2.is_bot() && !z2.is_bot()) {
    x.join(x2);
    y.join(y2);
    z.join(z2);
  }
}

// x = fdiv(y, z) (floor division), z != 0.
template<class VT>
CUDA INLINE constexpr void zfdiv_4(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }
  ZInterval<VT> x2(x), y2(y), z2(z);
  // CASE 1: z is positive.
  zfdiv_pos(x, y, z);
  // CASE 2: z is negative: floor(y/z) = floor((-y)/(-z)).
  zmirror(y2);
  zmirror(z2);
  zfdiv_pos(x2, y2, z2);
  zmirror(y2);
  zmirror(z2);
  if(x.is_bot() || y.is_bot() || z.is_bot()) {
    x = x2;
    y = y2;
    z = z2;
  }
  else if(!x2.is_bot() && !y2.is_bot() && !z2.is_bot()) {
    x.join(x2);
    y.join(y2);
    z.join(z2);
  }
}

// x = cdiv(y, z) (ceiling division), z != 0.
template<class VT>
CUDA INLINE constexpr void zcdiv_4(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }
  ZInterval<VT> x2(x), y2(y), z2(z);
  // CASE 1: z is positive: ceil(y/z) = -floor((-y)/z).
  zmirror(x);
  zmirror(y);
  zfdiv_pos(x, y, z);
  zmirror(x);
  zmirror(y);
  // CASE 2: z is negative: ceil(y/z) = -floor(y/(-z)).
  zmirror(x2);
  zmirror(z2);
  zfdiv_pos(x2, y2, z2);
  zmirror(x2);
  zmirror(z2);
  if(x.is_bot() || y.is_bot() || z.is_bot()) {
    x = x2;
    y = y2;
    z = z2;
  }
  else if(!x2.is_bot() && !y2.is_bot() && !z2.is_bot()) {
    x.join(x2);
    y.join(y2);
    z.join(z2);
  }
}

// x = ediv(y, z) (Euclidean division: y = x*z + r with 0 <= r < |z|), z != 0.
template<class VT>
CUDA INLINE constexpr void zediv_4(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  if(x.is_bot() || y.is_bot() || z.is_bot()) { return; }
  ZInterval<VT> x2(x), y2(y), z2(z);
  // CASE 1: z is positive: Euclidean division is the floor division.
  zfdiv_pos(x, y, z);
  // CASE 2: z is negative: ... and the ceiling division, ceil(y/z) = -floor(y/(-z)).
  zmirror(x2);
  zmirror(z2);
  zfdiv_pos(x2, y2, z2);
  zmirror(x2);
  zmirror(z2);
  if(x.is_bot() || y.is_bot() || z.is_bot()) {
    x = x2;
    y = y2;
    z = z2;
  }
  else if(!x2.is_bot() && !y2.is_bot() && !z2.is_bot()) {
    x.join(x2);
    y.join(y2);
    z.join(z2);
  }
}

} // namespace tell

} // namespace lala

#endif
