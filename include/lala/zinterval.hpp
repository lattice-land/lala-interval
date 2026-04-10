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

  CUDA INLINE constexpr LB& lb() { return l; }
  CUDA INLINE constexpr UB& ub() { return u; }
  CUDA INLINE constexpr const LB& lb() const { return l; }
  CUDA INLINE constexpr const UB& ub() const { return u; }

  CUDA INLINE constexpr bool is_bot() const {
    return l > u || l.is_bot() || u.is_bot();
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

  CUDA INLINE constexpr bool leqbot(basic_type other) const {
    return is_bot() || leq(other);
  }

  CUDA INLINE constexpr bool ltbot(basic_type other) const {
    return (is_bot() && !other.is_bot()) || lt(other);
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
    if(l.is_top()) return l + 1; // the largest negative number representable.
    if(u.is_top()) return u - 1; // the largest positive number representable.
    return battery::midpoint(l, u);
  }
};

// Lattice operations

template <class VT, class Mem>
CUDA constexpr ZInterval<VT, Mem> join(const ZInterval<VT, Mem>& a, const ZInterval<VT, Mem>& b) {
  return ZInterval<VT, Mem>(join(a.lb(), b.lb()), join(a.ub(), b.ub()));
}

template <class VT, class Mem>
CUDA constexpr ZInterval<VT, Mem> meet(const ZInterval<VT, Mem>& a, const ZInterval<VT, Mem>& b) {
  return ZInterval<VT, Mem>(meet(a.lb(), b.lb()), meet(a.ub(), b.ub()));
}

template <class VT, class Mem>
CUDA constexpr ZInterval<VT, Mem> joinbot(const ZInterval<VT, Mem>& a, const ZInterval<VT, Mem>& b) {
  if(a.is_bot() && b.is_bot()) return ZInterval<VT, Mem>::bot();
  if(a.is_bot()) return b;
  if(b.is_bot()) return a;
  return join(a, b);
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator==(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return a.lb() == b.lb() && a.ub() == b.ub();
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator!=(const ZInterval<VT, Mem1>& a, const ZInterval<VT, Mem2>& b)
{
  return !(a == b);
}

template<class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const ZInterval<VT, Mem> &itv) {
  return s << "[" << itv.lb() << "," << itv.ub() << "]";
}

} // namespace lala

#endif
