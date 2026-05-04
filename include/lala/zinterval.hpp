// Copyright 2026 Pierre Talbot

#ifndef LALA_INTERVAL_ZINTERVAL_HPP
#define LALA_INTERVAL_ZINTERVAL_HPP

#include "lala/lb.hpp"
#include "lala/ub.hpp"

namespace lala {

template <class VT, class Mem>
class ZInterval;

template <class VT, class Mem>
CUDA INLINE constexpr ZInterval<VT, Mem> qjoin(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b);
template <class VT, class Mem>
CUDA INLINE constexpr ZInterval<VT, Mem> join(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b);

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
    return l.is_bot() && u.is_bot();
  }

  CUDA INLINE constexpr bool is_top() const {
    return l.is_top() && u.is_top();
  }

  CUDA INLINE constexpr this_type& join_top() {
    l.join_top();
    u.join_top();
    return *this;
  }

  CUDA INLINE constexpr bool join(basic_type other) {
    bool r = l.join(other.l);
    r |= u.join(other.u);
    return r;
  }

  CUDA INLINE constexpr this_type& meet_bot() {
    l.meet_bot();
    u.meet_bot();
    return *this;
  }

  CUDA INLINE constexpr bool meet(basic_type other) {
    bool r = l.meet(other.l);
    r |= u.meet(other.u);
    return r;
  }

  CUDA INLINE constexpr bool leq(basic_type other) const {
    return l >= other.l && u <= other.u;
  }

  CUDA INLINE constexpr bool lt(basic_type other) const {
    return leq(other) && (l != other.l || u != other.u);
  }

  /** Lattice operations when considering the empty intervals to form an equivalence class with the bottom element `[oo, -oo]` selected as the representative element.
   * Taking this equivalence class is formally defined by the quotient lattice.
   * Therefore, we prepend the names of the operations with `q`.
   */

  CUDA INLINE constexpr bool is_qbot() const {
    return l > u || l.is_bot() || u.is_bot();
  }

  CUDA INLINE constexpr bool qjoin(basic_type other) {
    int mask = (is_qbot() ? 0 : 1) | (other.is_qbot() ? 0 : 2);
    switch(mask) {
      case 0: meet_bot(); return true;
      case 1: return false;
      case 2: l = other.l; u = other.u; return true;
      default: return join(other);
    }
  }

  CUDA INLINE constexpr bool qeq(basic_type other) const {
    return (is_qbot() && other.is_qbot()) || *this == other;
  }

  CUDA INLINE constexpr bool qleq(basic_type other) const {
    return is_qbot() || leq(other);
  }

  CUDA INLINE constexpr bool qlt(basic_type other) const {
    return (is_qbot() && !other.is_qbot()) || lt(other);
  }

  CUDA NI void print() const {
    printf("[");
    lb().print();
    printf(",");
    ub().print();
    printf("]");
  }

  /** precondition: `!is_qbot()` */
  CUDA constexpr value_type midpoint() const {
    if(l.is_top() && u.is_top()) return 0;
    if(l.is_top()) return l + VT{1}; // the largest negative number representable.
    if(u.is_top()) return u - VT{1}; // the largest positive number representable.
    return battery::midpoint(l, u);
  }

  /** Abstract functions. */

  CUDA INLINE UB<size_t> count() const {
    if(is_qbot()) { return 0; }
    if(l.is_top() || u.is_top()) { return UB<size_t>::top(); }
    return u - l + size_t{1};
  }

  CUDA INLINE constexpr bool contains(value_type v) {
    return l <= v && v <= u;
  }

  CUDA INLINE constexpr bool contains(basic_type a) {
    return a.qleq(*this);
  }

  // Remove 0 from the interval when possible.
  CUDA INLINE constexpr this_type& neq_zero() {
    if(l == 0) { l.meet(VT{1}); }
    if(u == 0) { u.meet(VT{-1}); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], -a)`.
  CUDA INLINE constexpr this_type& neg(basic_type a) {
    if(a.is_qbot()) { return meet_bot(); }
    if(!a.u.is_top()) { l.meet(-a.u); }
    if(!a.l.is_top()) { u.meet(-a.l); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a + b)`.
  CUDA INLINE constexpr this_type& add(basic_type a, basic_type b) {
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    if(!a.l.is_top() && !b.l.is_top()) { l.meet(a.l + b.l); }
    if(!a.u.is_top() && !b.u.is_top()) { u.meet(a.u + b.u); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a - b)`.
  CUDA INLINE constexpr this_type& sub(basic_type a, basic_type b) {
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    if(!a.l.is_top() && !b.l.is_top()) { l.meet(a.l - b.u); }
    if(!a.u.is_top() && !b.u.is_top()) { u.meet(a.u - b.l); }
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a * b)`.
  CUDA INLINE constexpr this_type& mul(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
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
  //   When implementing a propagator for `x = y * z`, it results in faster convergence to compute `z.mul_back_zero(x) ; y.mul_back_nz(x,z) ; y.mul_back_zero(x); z.mul_back_nz(x,y); ` instead of `y.mulb(x,z); z.mulb(x,y);` (if both were merged).
  CUDA INLINE constexpr this_type& mul_back_nz(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    using battery::cdiv;
    using battery::fdiv;
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
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
  }

  CUDA INLINE constexpr this_type& min(basic_type a, basic_type b) {
    using battery::min;
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    l.meet(min(a.l, b.l));
    u.meet(min(a.u, b.u));
    return *this;
  }

  // Let a = min(b, x), we update x according to a and b.
  CUDA INLINE constexpr this_type& min_back(basic_type a, basic_type b) {
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    l.meet(a.l);
    if(a.u < b.l) { u.meet(a.u); }
    return *this;
  }

  CUDA INLINE constexpr this_type& max(basic_type a, basic_type b) {
    using battery::max;
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    l.meet(max(a.l, b.l));
    u.meet(max(a.u, b.u));
    return *this;
  }

  CUDA INLINE constexpr this_type& max_back(basic_type a, basic_type b) {
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    if(a.l > b.u) { l.meet(a.l); }
    u.meet(a.u);
    return *this;
  }

private:
  // precondition: b.lb() != 0 && b.ub() != 0.
  template <class F>
  CUDA INLINE constexpr this_type& div_(basic_type a, basic_type b, F divz) {
    using battery::min;
    using battery::max;
    assert(b.l != 0 && b.u != 0);
    if(a.is_qbot() || b.is_qbot()) { meet_bot(); }
    else if(b.l < 0 && b.u > 0) { // TO CONFIRM: With the split on Z, this part becomes useless (as well as the test in else if)
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
    if(a.is_qbot() || b.is_qbot()) { meet_bot(); }
    else if(b.l < 0 && b.u > 0) {   // TO CONFIRM: With the split on Z, this part becomes useless (as well as the test in else if)
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
    if(a.is_qbot() || b.is_qbot()) { meet_bot(); }
    else if(a.l > 0) { fdiv_num(a, b); }
    else if(a.u < 0) { cdiv_num(a, b); }
    else {
      basic_type r(min<VT>(b.l, VT{-b.u}) + VT{1}, max<VT>(VT{-b.l}, b.u) - VT{1});
      r.qjoin(basic_type::top().cdiv_num(basic_type(a.l, -1), b));
      r.qjoin(basic_type::top().fdiv_num(basic_type(1, a.u), b));
      meet(r);
    }
    return *this;
  }

  // Let a = ediv(x, b), this function updates the numerator x according to a and b.
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& ediv_num(basic_type a, basic_type b) {
    assert(b.l != 0 && b.u != 0);
    if(a.is_qbot() || b.is_qbot()) { meet_bot(); }
    else if(b.l > 0) { fdiv_num(a, b); }
    else if(b.u < 0) { cdiv_num(a, b); }
    else { // TO CONFIRM: With the split on Z, this part becomes useless
      meet(::lala::qjoin(
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
    if(a.is_qbot() || b.is_qbot()) { meet_bot(); }
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
        meet(::lala::qjoin(
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
        // note: join is fine here as all arguments are normalized (either bot or non-empty).
        meet(::lala::join(
          b.l != 0 ? basic_type(1, UB2::top()) : basic_type::bot(),
          b.u != 0 ? basic_type(LB2::top(), -1) : basic_type::bot()));
      }
    }
    else {
      basic_type r(basic_type::top().fdiv_den(basic_type(a.l, -2), b));
      r.qjoin(basic_type::top().fdiv_den(basic_type(max<VT>(a.l,-1),-1), b));
      r.qjoin(basic_type::top().fdiv_den(basic_type(0, min<VT>(a.u, 0)), b));
      r.qjoin(basic_type::top().fdiv_den(basic_type(1, a.u), b));
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
    if(a.is_qbot() || b.is_qbot() || is_qbot()) { meet_bot(); }
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
      r.qjoin(basic_type::top().cdiv_den(basic_type(a.l, -1), b));
      r.qjoin(basic_type::top().fdiv_den(basic_type(1, a.u), b));
      meet(r);
    }
    return *this;
  }

  // Let a = ediv(b, x), this function updates the denominator x according to a and b.
  // precondition: lb() != 0 && ub() != 0
  CUDA INLINE constexpr this_type& ediv_den(basic_type a, basic_type b) {
    assert(l != 0 && u != 0);
    if(a.is_qbot() || b.is_qbot() || is_qbot()) { meet_bot(); }
    else if(l > 0) { fdiv_den(a, b); }
    else if(u < 0) { cdiv_den(a, b); }
    else {
      meet(::lala::qjoin(
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
CUDA INLINE constexpr ZInterval<VT, Mem> qjoin(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b) {
  a.qjoin(b);
  return a;
}

template<class VT, class Mem1, class Mem2>
CUDA INLINE constexpr bool operator==(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return a.lb() == b.lb() && a.ub() == b.ub();
}

template<class VT, class Mem1, class Mem2>
CUDA INLINE constexpr bool operator!=(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return a.lb() != b.lb() || a.ub() != b.ub();
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

template<class VT>
CUDA INLINE constexpr void zmul(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  x.mul(y, z);
  z.mul_back_zero(x);
  y.mul_back_nz(x, z);
  y.mul_back_zero(x);
  z.mul_back_nz(x, y);
}

template<class VT>
CUDA INLINE constexpr void fdiv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  z.neq_zero();
  x.fdiv(y, z);
  z.fdiv_den(x, y);
  y.fdiv_num(x, z);
  z.neq_zero();
  x.fdiv(y, z);
}

template<class VT>
CUDA INLINE constexpr void cdiv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  z.neq_zero();
  x.cdiv(y, z);
  z.cdiv_den(x, y);
  y.cdiv_num(x, z);
  z.neq_zero();
  x.cdiv(y, z);
}

template<class VT>
CUDA INLINE constexpr void tdiv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  z.neq_zero();
  x.tdiv(y, z);
  z.tdiv_den(x, y);
  y.tdiv_num(x, z);
  z.neq_zero();
  x.tdiv(y, z);
}

template<class VT>
CUDA INLINE constexpr void ediv_fast(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
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
  }
}

template<class VT>
CUDA INLINE constexpr void fdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, 0, fdiv_fast<VT>);
}

template<class VT>
CUDA INLINE constexpr void cdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, 0, cdiv_fast<VT>);
}

template<class VT>
CUDA INLINE constexpr void tdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, 0, tdiv_fast<VT>);
}

template<class VT>
CUDA INLINE constexpr void ediv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  splitjoin(x, y, z, z, 0, ediv_fast<VT>);
}

} // namespace tell

namespace ask {

template<class VT>
CUDA INLINE constexpr bool zadd(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
    (x.is_singleton() && y.is_singleton() && z.is_singleton() && x.lb() == y.lb() + z.lb());
}

template<class VT>
CUDA INLINE constexpr bool zsub(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return zadd(y, x, z);
}

template<class VT>
CUDA INLINE constexpr bool zmul(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
    (x.is_singleton() &&
      (y.is_singleton() && z.is_singleton() && x.lb() == y.lb() * z.lb()) ||
      (x.lb() == 0 && (y.is_singleton(0) || z.is_singleton(0))));
}

template<class VT>
CUDA INLINE constexpr bool fdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::fdiv<VT>(y.lb(), z.lb())) ||
             (x.lb() == 0 && y.lb() == 0))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool cdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::cdiv<VT>(y.lb(), z.lb())) ||
             (x.lb() == 0 && y.lb() == 0))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool tdiv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::tdiv<VT>(y.lb(), z.lb())) ||
             (x.lb() == 0 && y.lb() == 0))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool ediv(ZInterval<VT>& x, ZInterval<VT>& y, ZInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(0) &&
            ((z.is_singleton() && x.lb() == battery::ediv<VT>(y.lb(), z.lb())) ||
             (x.lb() == 0 && y.lb() == 0))); // 0 = 0 / z (for any z != 0).
}


} // namespace ask

} // namespace lala

#endif
