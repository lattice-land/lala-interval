// Copyright 2026 Pierre Talbot

#ifndef LALA_INTERVAL_ZINTERVAL_HPP
#define LALA_INTERVAL_ZINTERVAL_HPP

namespace lala {

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

  template <class Mem2>
  CUDA INLINE constexpr this_type& operator=(const ZInterval<value_type, Mem2>& other) {
    l = other.l;
    u = other.u;
    return *this;
  }

  constexpr this_type& operator=(const this_type&) = default;

  CUDA INLINE constexpr lb_type& lb() { return l; }
  CUDA INLINE constexpr ub_type& ub() { return u; }
  CUDA INLINE constexpr const lb_type& lb() const { return l; }
  CUDA INLINE constexpr const ub_type& ub() const { return u; }

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
    if(l.is_top()) return l + 1; // the largest negative number representable.
    if(u.is_top()) return u - 1; // the largest positive number representable.
    return battery::midpoint(l, u);
  }

  /** Abstract functions. */

  // Remove 0 from the interval when possible.
  CUDA INLINE constexpr this_type& neqzero() {
    if(l == 0) { l.meet(1); }
    if(u == 0) { u.meet(-1); }
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
    if(!a.l.is_top() && !b.l.is_top()) { l.meet(a.l - b.l); }
    if(!a.u.is_top() && !b.u.is_top()) { u.meet(a.u - b.u); }
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

  // Let a = _ * x where _ can be anything, then `mulzero` removes 0 from x (if possible) whenever 0 is not in a.
  CUDA INLINE constexpr this_type& mulzero(basic_type a) {
    if(a.l > 0 || a.u < 0) { neqzero(); }
    return *this;
  }

  // Let a = b * x, `mulr` computes the interval of `x` given a and b, called the residual.
  // Can be used in conjunction with `mulzero` for a more precise result.
  // Why is mulr and mulzero separated? When implementing a propagator for `x = y * z`, it results in faster convergence to compute `z.mulzero(x) ; y.mulr(x,z) ; y.mulzero(x); z.mulr(x,y); ` instead of `y.mulr(x,z); z.mulr(x,y);` (if both were merged).
  CUDA INLINE constexpr this_type& mulr(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    using battery::cdiv;
    using battery::fdiv;
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    if(!a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      if(b.l > 0 || b.u < 0) {
        l.meet(min(min(cdiv(a.l, b.l), cdiv(a.l, b.u)), min(cdiv(a.u, b.l), cdiv(a.u, b.u))));
        u.meet(max(max(fdiv(a.l, b.l), fdiv(a.l, b.u)), max(fdiv(a.u, b.l), fdiv(a.u, b.u))));
      }
      else if(b.l < 0 && b.u > 0 && (a.l > 0 || a.u < 0)) {
        l.meet(min(a.l, -a.u));
        u.meet(max(-a.l, a.u));
      }
    }
    return *this;
  }

  CUDA INLINE constexpr this_type& min(basic_type a, basic_type b) {
    using battery::min;
    if(a.is_qbot() || b.is_qbot()) { return meet_bot(); }
    l.meet(min(a.l, b.l));
    u.meet(min(a.u, b.u));
    return *this;
  }

  // Let a = min(b, x), we update x according to a and b.
  CUDA INLINE constexpr this_type& minr(basic_type a, basic_type b) {
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

  CUDA INLINE constexpr this_type& maxr(basic_type a, basic_type b) {
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
      if(!a.u.is_top()) { l.meet(min(a.l, -a.u)); }
      if(!a.l.is_top()) { u.meet(max(-a.l, a.u)); }
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
    return div_(a, b, battery::fdiv);
  }

  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& cdiv(basic_type a, basic_type b) {
    return div_(a, b, battery::cdiv);
  }

  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& tdiv(basic_type a, basic_type b) {
    return div_(a, b, battery::tdiv);
  }

  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& ediv(basic_type a, basic_type b) {
    return div_(a, b, battery::ediv);
  }

  // Let a = fdiv(x, b), this function updates the numerator x according to a and b.
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& fdiv_num(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    assert(b.l != 0 && b.u != 0);
    if(a.is_qbot() || b.is_qbot()) { meet_bot(); }
    else if(b.l < 0 && b.u > 0) {   // TO CONFIRM: With the split on Z, this part becomes useless (as well as the test in else if)
      l.meet(min(min(a.l, -a.u), min(a.l * b.u, (a.u + 1) * b.l + 1)));
      u.meet(max(max(-a.l, a.u), max(a.l * b.l, (a.u + 1) * b.u - 1)));
    }
    else {
      l.meet(min(min(a.l * b.l, a.l * b.u), min((a.u + 1) * b.l + 1, (a.u + 1) * b.u + 1)));
      u.meet(max(max(a.l * b.l, a.l * b.u), max((a.u + 1) * b.l - 1, (a.u + 1) * b.u - 1)));
    }
    return *this;
  }

  // Let a = cdiv(x, b), this function updates the numerator x according to a and b.
  // precondition: b.lb() != 0 && b.ub() != 0.
  CUDA INLINE constexpr this_type& cdiv_num(basic_type a, basic_type b) {
    return fdiv_num(top().neg(a), top().neg(b));
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
      basic_type r(min(b.l, -b.u) + 1, max(-b.l, b.u) - 1);
      r.qjoin(cdiv_num(basic_type(a.l,-1), b));
      r.qjoin(fdiv_num(basic_type(1, a.u), b));
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
      meet(qjoin(
            top().cdiv_num(a, basic_type(b.l, -1))
            top().fdiv_num(a, basic_type(1, b.u))));
    }
    return *this;
  }

  // Let a = fdiv(b, x), this function updates the denominator x according to a and b.
  CUDA INLINE constexpr this_type& fdiv_den(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    using battery::fdiv;
    if(a.is_qbot() || b.is_qbot()) { meet_bot(); }
    else if(a.l > 0 || a.u + 1 < 0) {
      if(b.l > 0) {
        l.meet(min(fdiv(b.l, a.u + 1), fdiv(b.u, a.u + 1)) + 1);
        u.meet(max(fdiv(b.l, a.l), fdiv(b.u, a.l)));
      }
      else if(b.u < 0) {
        l.meet(min(cdiv(b.l, a.l), cdiv(b.u, a.l)));
        u.meet(max(cdiv(b.l, a.u + 1), cdiv(b.u, a.u + 1)) - 1);
      }
      else {
        meet(qjoin(top().fdiv_den(a, basic_type(b.l, -1)), top().fdiv_den(a, basic_type(1, b.u))));
      }
    }
    else if(a.l == 0 && a.u == 0) {
      if(b.l > 0) { l.meet(b.l + 1); }
      else if(b.u < 0) { u.meet(b.u - 1); }
    }
    else if(a.l == -1 && a.u == -1) {
      if(b.l > 0) { u.meet(-b.l); }
      else if(b.u < 0) { l.meet(-b.u); }
      else {
        // note: join is fine here as all arguments are normalized (either bot or non-empty).
        meet(join(
          b.l != 0 ? basic_type(1, UB2::top()) : basic_type::bot(),
          b.u != 0 ? basic_type(LB2::top(), -1) : basic_type::bot()));
      }
    }
    else {
      basic_type r(top().fdiv_den(basic_type(a.l, -2), b));
      r.qjoin(top().fdiv_den(basic_type(max(a.l,-1),-1), b));
      r.qjoin(top().fdiv_den(basic_type(0, min(a.u, 0)), b));
      r.qjoin(top().fdiv_den(basic_type(1, a.u), b));
      meet(r);
    }
    return *this;
  }

  // Let a = cdiv(b, x), this function updates the denominator x according to a and b.
  CUDA INLINE constexpr this_type& cdiv_den(basic_type a, basic_type b) {
    return fdiv_den(top().neg(a), top().neg(b));
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
    else if(a.l == 0 && a.u == 0) {
      if(l > 0 && (b.l > 0 || b.u < 0)) {
        l.meet(max(b.l + 1, -b.u + 1));
      }
      else if(u < 0 && (b.l > 0 || b.u < 0)) {
        u.meet(min(-b.l - 1, b.u - 1));
      }
      // HERE an alternative implementation (unfolding the one above, maybe a bit clearer).
      // if(b.l > 0 && l > 0) { return basic_type(b.l + 1, UB2:top()); }
      // if(b.l > 0 && u < 0) { return basic_type(LB2::top(), -b.l - 1); }
      // if(b.u < 0 && l > 0) { return basic_type(-b.u + 1, UB2:top()); }
      // if(b.u < 0 && u < 0) { return basic_type(LB2::top(), b.u - 1); }
    }
    else {
      basic_type r(*this);
      r.tdiv_den(basic_type(0, 0), b);
      r.qjoin(top().cdiv_den(basic_type(a.l, -1), b));
      r.qjoin(top().fdiv_den(basic_type(1, a.u), b));
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
      meet(qjoin(top().fdiv_den(a, b), top().cdiv_den(a, b)));
    }
    return *this;
  }
};

// Lattice operations

template <class VT, class Mem>
CUDA constexpr ZInterval<VT, Mem> join(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b) {
  return a.join(b);
}

template <class VT, class Mem>
CUDA constexpr ZInterval<VT, Mem> meet(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b) {
  return a.meet(b);
}

template <class VT, class Mem>
CUDA constexpr ZInterval<VT, Mem> qjoin(ZInterval<VT, Mem> a, ZInterval<VT, Mem> b) {
  return a.qjoin(b);
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator==(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return a.lb() == b.lb() && a.ub() == b.ub();
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator!=(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return a.lb() != b.lb() || a.ub() != b.ub();
}

template<class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const ZInterval<VT, Mem> &itv) {
  return s << "[" << itv.lb() << "," << itv.ub() << "]";
}

} // namespace lala

#endif
