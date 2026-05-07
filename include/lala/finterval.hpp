// Copyright 2026 Yi-Nung Tsao

#ifndef LALA_INTERVAL_FINTERVAL_HPP
#define LALA_INTERVAL_FINTERVAL_HPP

#include "lala/lb.hpp"
#include "lala/ub.hpp"

namespace lala {

template <class VT, class Mem = battery::local_memory>
class FInterval {
public:
    using value_type = VT;
    using memory_type = Mem;
    using lb_type = LB<value_type, memory_type>;
    using ub_type = UB<value_type, memory_type>;
    using this_type = FInterval<value_type, memory_type>;
    using basic_type = FInterval<value_type>;

    template <class VT2, class Mem2>
    friend class FInterval;

    constexpr static const bool is_totally_ordered = false;
    constexpr static const char* name = "FInterval";

private:
    lb_type l;
    ub_type u;

public:
    CUDA INLINE static constexpr this_type bot() { return this_type(lb_type::bot(), ub_type::bot()); }
    CUDA INLINE static constexpr this_type top() { return this_type(lb_type::top(), ub_type::top()); }

    constexpr FInterval() = default;
    constexpr FInterval(const this_type&) = default;
    CUDA constexpr FInterval(value_type x): l(x), u(x) {}
    CUDA constexpr FInterval(value_type l, value_type u): l(l), u(u) {}

    template <class Mem2>
    CUDA constexpr FInterval(const FInterval<value_type, Mem2>& other)
     : l(other.l)
     , u(other.u)
    {}

    constexpr this_type& operator=(const this_type&) = default;
    template <class Mem2>
    CUDA INLINE constexpr this_type& operator=(const FInterval<value_type, Mem2>& other) {
      l = other.l;
      u = other.u;
      return *this;
    }

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
    bool result = l.join(other.l);
    result |= u.join(other.u);
    return result;
  }

  CUDA INLINE constexpr this_type& meet_bot() {
    l.meet_bot();
    u.meet_bot();
    return *this;
  }

  CUDA INLINE constexpr bool meet(basic_type other) {
    bool result = l.meet(other.l);
    result |= u.meet(other.u);
    return result;
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
      case 2: {
        l = other.l;
        u = other.u;
        return true;
      }
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
    printf(", ");
    ub().print();
    printf("]\n");
  }

    /** precondition: `!is_qbot()` */
    CUDA constexpr value_type midpoint() const {
      if(l.is_top() && u.is_top()) return 0.0;
      if(l.is_top()) return battery::limits<value_type>::neg_inf();
      if(u.is_top()) return battery::limits<value_type>::inf();
      return battery::midpoint(l, u);
    }

  CUDA constexpr ub_type width() const {
    if(is_qbot()) return ub_type{-1.0};
    if(is_top()) return ub_type{battery::limits<value_type>::inf()};
    return ub_type{battery::sub_up(u, l)};
  }

  /** Abstract functions. */

  CUDA INLINE constexpr bool contains(value_type v) {
        return l <= v && v <= u;
  }

  CUDA INLINE constexpr bool constains(basic_type a) {
    return a.qleq(*this);
  }

  // Given the current interval [lb, ub], this function computes `meet([lb, ub], -a)`.
  CUDA INLINE constexpr this_type& neg(basic_type a) {
    if (a.is_qbot()) return meet_bot();
    if (!a.ub.is_top()) l.meet(-a.u);
    if (!a.lb.is_top()) u.meet(-a.l);
    return *this;
  }

  // Given the current interval [lb, ub], this function computes `meet([lb, ub], a + b)`.
  CUDA INLINE constexpr this_type& add(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (!a.l.is_top() && !b.l.is_top()) l.meet(battery::add_down(a.l, b.l));
    if (!a.u.is_top() && !b.u.is_top()) u.meet(battery::add_up(a.u, b.u));
    return *this;
  }

  // Given the current interval [lb, ub], this function computes `meet([lb, ub], a - b)`.
  CUDA INLINE constexpr this_type& sub(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (!a.l.is_top() && !b.l.is_top()) l.meet(battery::sub_down(a.l, b.u));
    if (!a.u.is_top() && !b.u.is_top()) u.meet(battery::sub_up(a.u, b.l));
    return *this;
  }

  // Given the current interval [lb, ub], this function computes `meet([lb, ub], a * b)`.
  CUDA INLINE constexpr this_type& mul(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (!a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      l.meet(battery::min(battery::min(battery::mul_down(a.l, b.l), battery::mul_down(a.l, b.u)), battery::min(battery::mul_down(a.u, b.l), battery::mul_down(a.u, b.u))));
      u.meet(battery::max(battery::max(battery::mul_up(a.l, b.l), battery::mul_up(a.l, b.u)), battery::max(battery::mul_up(a.u, b.l), battery::mul_up(a.u, b.l))));
    }
    return *this;
  }

  // Given the current interval [lb, ub], this function computes `meet([lb, ub], a / b)`.
  CUDA INLINE constexpr this_type& div(basic_type a, basic_type b) {
    if (b.l <= 0.0 && b.u >= 0.0) return *this;
    if (!a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      l.meet(battery::min(battery::min(battery::div_down(a.l, b.l), battery::div_down(a.l, b.u)), battery::min(battery::div_down(a.u, b.l), battery::div_down(a.u, b.u))));
      u.meet(battery::max(battery::max(battery::div_up(a.l, b.l), battery::div_up(a.l, b.u)), battery::max(battery::div_up(a.u, b.l), battery::div_up(a.u, b.l))));
    }
    return *this;
  }

  // Given the current interval [lb, ub], this function computes `meet([lb, ub], min(a, b))`.
  CUDA INLINE constexpr this_type& min(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    l.meet(battery::min(a.l, b.l));
    u.meet(battery::min(a.u, b.u));
    return *this;
  }

  // Let a = min(b, x), we update x according to a and b.
  CUDA INLINE constexpr this_type& min_back(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    l.meet(a.lb);
    if (a.u < b.l) u.meet(a.u);
    return *this;
  }

  // Given the current interval [lb, ub], this function computes `meet([lb, ub], max(a, b))`.
  CUDA INLINE constexpr this_type& max(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    l.meet(battery::max(a.l, b.l));
    u.meet(battery::max(a.u, b.u));
    return *this;
  }

  // Let a = max(b, x), we update x according to a and b.
  CUDA INLINE constexpr this_type& max_back(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (a.l > b.u) l.meet(a.l);
    u.meet(a.u);
    return *this;
  }

  // Let x = (a = b), we update x according to a and b.
  // precondition: x <= [0, 1]
  CUDA INLINE constexpr this_type& req(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (a.l == b.u && a.u == b.l) l.meet(ONE);
    else if (a.l > b.u || a.u < b.l) u.meet(ZERO);
    return *this;
  }

  // Let a = (x = b), we update x according to a and b.
  // precondition: a <= [0, 1]
  CUDA INLINE constexpr this_type& req_back(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (a.l == ONE) {
      l.meet(b.l);
      u.meet(b.u);
    }
    return *this;
  }

  // Let x = (a <= b), we update x according to a and b.
  // precondition: x <= [0, 1]
  CUDA INLINE constexpr this_type& rleq(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (a.u <= b.l) l.meet(ONE);
    else if (a.l() > b.u) u.meet(ZERO);
    return *this;
  }

  // Let a = (x <= b), we update x according to a and b.
  // precondition: a <= [0, 1]
  CUDA INLINE constexpr this_type& rleq_lback(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (a.l == ONE) u.meet(b.u);
    else if (a.u == ZERO) l.meet(b.l);
    return *this;
  }

  // Let a = (b <= x), we update x according to a and b.
  // precondition: a <= [0, 1]
  CUDA INLINE constexpr this_type& rleq_rback(basic_type a, basic_type b) {
    if (a.is_qbot() || b.is_qbot()) return meet_bot();
    if (a.l == ONE) l.meet(b.l);
    else if (a.u == ZERO) u.meet(b.u);
    return *this;
  }
};

// Lattice operations

template <class VT, class Mem>
CUDA INLINE constexpr FInterval<VT, Mem> join(FInterval<VT, Mem> a, FInterval<VT, Mem> b) {
  a.join(b);
  return a;
}

template <class VT, class Mem>
CUDA INLINE constexpr FInterval<VT, Mem> meet(FInterval<VT, Mem> a, FInterval<VT, Mem> b) {
  a.meet(b);
  return a;
}

template <class VT, class Mem>
CUDA INLINE constexpr FInterval<VT, Mem> qjoin(FInterval<VT, Mem> a, FInterval<VT, Mem> b) {
  a.qjoin(b);
  return a;
}

template<class VT, class Mem1, class Mem2>
CUDA INLINE constexpr bool operator==(const FInterval<VT, Mem1>& a, const FInterval<VT, Mem2>& b)
{
  return a.lb() == b.lb() && a.ub() == b.ub();
}

template<class VT, class Mem1, class Mem2>
CUDA INLINE constexpr bool operator!=(const FInterval<VT, Mem1>& a, const FInterval<VT, Mem2>& b)
{
  return !(a == b);
}

template<class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const FInterval<VT, Mem> &itv) {
  return s << "[" << itv.lb() << "," << itv.ub() << "]";
}

namespace tell {

template<class VT>
CUDA INLINE constexpr void fadd(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  x.add(y, z);
  y.sub(x, z);
  z.sub(x, y);
}

template<class VT>
CUDA INLINE constexpr void fsub(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  fadd(y, x, z);
}

template<class VT>
CUDA INLINE constexpr void fmul(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  x.mul(y, z);
  y.div(x, z);
  z.div(x, y);
}

template<class VT>
CUDA INLINE constexpr void fdiv(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  x.div(y, z);
  y.mul(x, z);
  z.div(y, x);
}

template<class VT>
CUDA INLINE constexpr void fmin(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  x.min(y, z);
  y.min_back(x, z);
  z.min_back(x, y);
}

template<class VT>
CUDA INLINE constexpr void fmax(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  x.max(y, z);
  y.max_back(x, z);
  z.max_back(x, y);
}

template<class VT>
CUDA INLINE constexpr void freq(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  constexpr VT ZERO{0.0};
  constexpr VT ONE{1.0};
  if (x.lb() == ZERO && x.ub() < ONE) x.meet(FInterval<VT>(ZERO, ZERO));
  else if (x.lb() > ZERO && x.ub() == ONE) x.meet(FInterval<VT>(ONE, ONE));
  else if (x.lb() > ZERO && x.ub() < ONE)  x.join(FInterval<VT>(ZERO, ONE));
  x.req(y, z);
  y.req_back(x, z);
  z.req_back(x, y);
}

template<class VT>
CUDA INLINE constexpr void frleq(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  constexpr VT ZERO{0.0};
  constexpr VT ONE{1.0};
  if (x.lb() == ZERO && x.ub() < ONE) x.meet(FInterval<VT>(ZERO, ZERO));
  else if (x.lb() > ZERO && x.ub() == ONE) x.meet(FInterval<VT>(ONE, ONE));
  else if (x.lb() > ZERO && x.ub() < ONE) x.join(FInterval<VT>(ZERO, ONE));
  x.rleq(y, z);
  y.rleq_lback(x, z);
  z.rleq_rback(x, y);
}

}


namespace ask {

template<class VT>
CUDA INLINE constexpr bool fadd(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  VT mid_x = x.midpoint();
  VT mid_y = y.midpoint();
  VT mid_z = z.midpoint();
  return mid_x == mid_y + mid_z;
}

template<class VT>
CUDA INLINE constexpr bool fsub(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return fadd(y, x, z);
}

template <class VT>
CUDA INLINE constexpr bool fmul(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  VT mid_x = x.midpoint();
  VT mid_y = y.midpoint();
  VT mid_z = z.midpoint();
  return mid_x == mid_y * mid_z;
}

template <class VT>
CUDA INLINE constexpr bool fmin(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
    (x.lb() == y.ub() && x.ub() == y.lb() && y.ub() <= z.lb()) ||
    (x.lb() == z.ub() && x.ub() == z.lb() && z.ub() <= y.lb());
}

template <class VT>
CUDA INLINE constexpr bool fmax(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
    (x.lb() == y.ub() && x.ub() == y.lb() && y.lb() >= z.ub()) ||
    (x.lb() == z.ub() && x.ub() == z.lb() && z.lb() >= y.ub());
}

// precondition: x <= [0, 1]
template <class VT>
CUDA INLINE constexpr bool freq(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
    (x.lb() == VT{1.0} && y.ub() == z.lb() && y.lb() == z.ub()) ||
    (x.ub() == VT{0.0} && (y.ub() < z.lb() || y.lb() > z.ub()));
}

template <class VT>
CUDA INLINE constexpr bool frleq(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_qbot() || y.is_qbot() || z.is_qbot() ||
    (x.lb() == VT{1.0} && y.ub() <= z.lb()) ||
    (x.ub() == VT{0.0} && y.lb() >= z.ub());
}

}

}

#endif