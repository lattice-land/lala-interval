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

  CUDA INLINE constexpr void join_top() {
    l.join_top();
    u.join_top();
  }

  CUDA INLINE constexpr bool join(basic_type other) {
    bool r = l.join(other.l);
    r |= u.join(other.u);
    return r;
  }

  CUDA INLINE constexpr void meet_bot() {
    l.meet_bot();
    u.meet_bot();
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

  // Given the current interval [l,u], it computes `meet([l,u], -a)`.
  template <class Mem1>
  CUDA constexpr this_type& neg(const ZInterval<value_type, Mem1>& a) {
    l.meet(-a.u);
    u.meet(-a.l);
    return *this;
  }


  // Given the current interval [l,u], it computes `meet([l,u], a + b)`.
  template <class Mem1, class Mem2>
  CUDA constexpr this_type& add(const ZInterval<value_type, Mem1>& a, const ZInterval<value_type, Mem2>& b) {
    l.meet(a.l + b.l);
    u.meet(a.u + b.u);
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a - b)`.
  template <class Mem1, class Mem2>
  CUDA constexpr this_type& sub(const ZInterval<value_type, Mem1>& a, const ZInterval<value_type, Mem2>& b) {
    l.meet(a.l - b.l);
    u.meet(a.u - b.u);
    return *this;
  }

  // Given the current interval [l,u], it computes `meet([l,u], a * b)`.
  template <class Mem1, class Mem2>
  CUDA constexpr this_type& sub(const ZInterval<value_type, Mem1>& a, const ZInterval<value_type, Mem2>& b) {
    l.meet(a.l - b.l);
    u.meet(a.u - b.u);
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
