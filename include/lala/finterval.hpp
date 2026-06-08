// Copyright 2026 Yi-Nung Tsao, Pierre Talbot

#ifndef LALA_INTERVAL_FINTERVAL_HPP
#define LALA_INTERVAL_FINTERVAL_HPP

#include "lala/lb.hpp"
#include "lala/ub.hpp"

namespace lala {

template <class VT, class Mem>
class FInterval;

template <class VT, class Mem>
CUDA INLINE constexpr FInterval<VT, Mem> join(FInterval<VT, Mem> a, FInterval<VT, Mem> b);
template <class VT, class Mem>
CUDA INLINE constexpr FInterval<VT, Mem> join_nobot(FInterval<VT, Mem> a, FInterval<VT, Mem> b);

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
    printf(", ");
    ub().print();
    printf("]\n");
  }

  /** precondition: `!is_bot()` */
  CUDA constexpr value_type midpoint() const {
    if(l.is_top() && u.is_top()) return VT{0.0};
    if(l.is_top()) return std::numeric_limits<VT>::min(); // the largest negative number representable.
    if(u.is_top()) return std::numeric_limits<VT>::max(); // the largest positive number representable.
    return battery::midpoint(l, u);
  }

  CUDA constexpr ub_type width() const {
    if(is_bot()) return ub_type{-1.0};
    if(l.is_top() || u.is_top()) return ub_type::top();
    return battery::sub_up<VT>(u, l);
  }

  /** Abstract functions. */

  CUDA INLINE constexpr bool contains(value_type v) {
    return l <= v && v <= u;
  }

  CUDA INLINE constexpr bool constains(basic_type a) {
    return a.leq(*this);
  }

  // Given the current interval [l,u], this function computes `meet([l,u], -a)`.
  CUDA INLINE constexpr this_type& neg(basic_type a) {
    if (a.is_bot()) return meet_bot();
    l.meet(-a.u);
    u.meet(-a.l);
    return *this;
  }

private:
  // Useful to avoid a few tests during division.
  // See Sec. 5.2 of Hickey et al., "Interval Arithmetic: From Principles to Implementation", JACM, 2001.
  CUDA INLINE constexpr void normalize_zeroes() {
    if(l == VT{0.0}) l = VT{+0.0};
    if(u == VT{0.0}) u = VT{-0.0};
  }

public:
  // Given the current interval [l,u], this function computes `meet([l,u], a + b)`.
  CUDA INLINE constexpr this_type& add(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    l.meet(battery::add_down<VT>(a.l, b.l)); // top case: -oo + -oo = -oo
    u.meet(battery::add_up<VT>(a.u, b.u));  // top case: oo + oo = oo
    return *this;
  }

  // Given the current interval [l,u], this function computes `meet([l,u], a - b)`.
  CUDA INLINE constexpr this_type& sub(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    l.meet(battery::sub_down<VT>(a.l, b.u)); // top case: -oo - oo = -oo
    u.meet(battery::sub_up<VT>(a.u, b.l));   // top case: oo - -oo = oo
    return *this;
  }

  // Given the current interval [l,u], this function computes `meet([l,u], a * b)`.
  CUDA INLINE constexpr this_type& mul(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    using battery::mul_down;
    using battery::mul_up;
    if (a.is_bot() || b.is_bot()) { return meet_bot(); }
    // Bounded case
    if (!a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      l.meet(min(min(mul_down<VT>(a.l, b.l), mul_down<VT>(a.l, b.u)), min(mul_down<VT>(a.u, b.l), mul_down<VT>(a.u, b.u))));
      u.meet(max(max(mul_up<VT>(a.l, b.l), mul_up<VT>(a.l, b.u)), max(mul_up<VT>(a.u, b.l), mul_up<VT>(a.u, b.l))));
    }
    // Unbounded case (either a.l, a.u, b.l or b.u is top).
    // Note this also covers the bounded case. We keep the first case to reduce thread divergence.
    // Based on Hickey et al., "Interval Arithmetic: From Principles to Implementation", JACM, 2001.
    else {
      if(a.is_singleton(VT{0.0}) || b.is_singleton(VT{0.0})) {
        l.meet(VT{0.0});
        u.meet(VT{0.0});
      }
      else {
        // There are 9 possible cases according to the following classification.
        // 0: positive (l >= 0 /\ u > 0), 1: mixed (l < 0 < u), 2: negative (l < 0 /\ u <= 0)
        // int class_a = (a.l >= 0 ? 0 : (a.u > 0 ? 1 : 2));
        // int class_b = (b.l >= 0 ? 0 : (b.u > 0 ? 1 : 2));
        // switch(3 * class_a + class_b) {
        switch(3 * (a.l >= 0 ? 0 : (a.u > 0 ? 1 : 2)) + (b.l >= 0 ? 0 : (b.u > 0 ? 1 : 2))) {
          case 0: { l.meet(mul_down<VT>(a.l, b.l)); u.meet(mul_up<VT>(a.u, b.u)); break; }
          case 1: { l.meet(mul_down<VT>(a.u, b.l)); u.meet(mul_up<VT>(a.u, b.u)); break; }
          case 2: { l.meet(mul_down<VT>(a.u, b.l)); u.meet(mul_up<VT>(a.l, b.u)); break; }
          case 3: { l.meet(mul_down<VT>(a.l, b.u)); u.meet(mul_up<VT>(a.u, b.u)); break; }
          case 4: {
            l.meet(min(mul_down<VT>(a.l, b.u), mul_down<VT>(a.u, b.l)));
            u.meet(max(mul_up<VT>(a.l, b.l), mul_up<VT>(a.u, b.u)));
            break;
          }
          case 5: { l.meet(mul_down<VT>(a.u, b.l)); u.meet(mul_up<VT>(a.l, b.l)); break; }
          case 6: { l.meet(mul_down<VT>(a.l, b.u)); u.meet(mul_up<VT>(a.u, b.l)); break; }
          case 7: { l.meet(mul_down<VT>(a.l, b.u)); u.meet(mul_up<VT>(a.l, b.l)); break; }
          case 8:
          default: { l.meet(mul_down<VT>(a.u, b.u)); u.meet(mul_up<VT>(a.l, b.l)); break; }
        }
      }
    }
    return *this;
  }

private:
  // Suppose !a.is_singleton(0) /\ !b.is_singleton(0) /\ !a.is_bot() /\ !b.is_bot()
  CUDA INLINE constexpr this_type& div_nz(const basic_type& a, const basic_type& b) {
    using battery::min;
    using battery::max;
    using battery::mul_down;
    using battery::mul_up;
    // Mixed case: 0 is contained in b, but not on the endpoints.
    if (b.l < VT{0.0} && b.u > VT{0.0}) { return *this; }
    // Bounded case with 0 \notin b.
    if (b.l != VT{0.0} && b.u != VT{0.0} && !a.l.is_top() && !a.u.is_top() && !b.l.is_top() && !b.u.is_top()) {
      l.meet(min(min(div_down<VT>(a.l, b.l), div_down<VT>(a.l, b.u)), min(div_down<VT>(a.u, b.l), div_down<VT>(a.u, b.u))));
      u.meet(max(max(div_up<VT>(a.l, b.l), div_up<VT>(a.l, b.u)), max(div_up<VT>(a.u, b.l), div_up<VT>(a.u, b.l))));
    }
    // Unbounded case (either a.l, a.u, b.l or b.u is top).
    // Note this also covers the bounded case. We keep the first case to reduce thread divergence.
    // Based on Hickey et al., "Interval Arithmetic: From Principles to Implementation", JACM, 2001.
    else {
      b.normalize_zeroes();
      // 0: positive+ (l > 0), 1: positive0 (l = 0 /\ u > 0), 2: mixed (l < 0 < u), 3: negative0 (l < 0 /\ u = 0), 4: negative- (u < 0).
      // int class_a = (a.l > 0 ? 0 : (a.l == 0 ? 1 : (a.l < 0 && a.u > 0 ? 2 : (a.u == 0 ? 3 : 4))));
      // 0: positive (l >= 0 /\ u > 0), 2: negative (l < 0 /\ u <= 0)
      // int class_b = (b.l >= 0 ? 1 : 2);
      // switch(class_a * class_b) {
      switch((a.l > 0 ? 0 : (a.l == 0 ? 1 : (a.l < 0 && a.u > 0 ? 2 : (a.u == 0 ? 3 : 4)))) * (b.l >= 0 ? 1 : 2)) {
        case 0: { l.meet(div_down<VT>(a.l, b.u)); u.meet(div_up<VT>(a.u, b.l)); break; }
        case 1: { l.meet(VT{0.0}); u.meet(div_up<VT>(a.u, b.l)); break; }
        case 2: { l.meet(div_down<VT>(a.l, b.l)); u.meet(div_up<VT>(a.u, b.l)); break; }
        case 3: { l.meet(div_down<VT>(a.l, b.l)); u.meet(VT{0.0}); break; }
        case 4: { l.meet(div_down<VT>(a.l, b.l)); u.meet(div_up<VT>(a.u, b.u)); break; }
        case 5: { l.meet(div_down<VT>(a.u, b.u)); u.meet(div_up<VT>(a.l, b.l)); break; }
        case 6: { l.meet(div_down<VT>(a.u, b.u)); u.meet(VT{0.0}); break; }
        case 7: { l.meet(div_down<VT>(a.u, b.u)); u.meet(div_up<VT>(a.l, b.u)); break; }
        case 8: { l.meet(VT{0.0}); u.meet(div_up<VT>(a.l, b.u)); break; }
        case 9:
        default: { l.meet(div_down<VT>(a.u, b.l)); u.meet(div_up<VT>(a.l, b.u)); break; }
      }
    }
    return *this;
  }

public:
  // Let a = b * x, we update x according to a and b.
  CUDA INLINE constexpr this_type& mul_back(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) { return meet_bot(); }
    if (b.is_singleton(VT{0.0}) || is_singleton(VT{0.0})) { return *this; }
    if (a.is_singleton(VT{0.0}) && !b.contains(VT{0.0})) {
      l.meet(VT{0.0});
      u.meet(VT{0.0});
      return *this;
    }
    return div_nz(a, b);
  }

  // Given the current interval [l,u], this function computes `meet([l,u], a / b)`.
  CUDA INLINE constexpr this_type& div(basic_type a, basic_type b) {
    using battery::min;
    using battery::max;
    using battery::mul_down;
    using battery::mul_up;
    // Bottom cases.
    if (a.is_bot() || b.is_bot() || b.is_singleton(VT{0.0})) { return meet_bot(); }
    // `a` is zero.
    if(a.is_singleton(VT{0.0})) {
      l.meet(VT{0.0});
      u.meet(VT{0.0});
      return *this;
    }
    return div_nz(a, b);
  }

  // Given the current interval [l,u], this function computes `meet([l,u], min(a, b))`.
  CUDA INLINE constexpr this_type& min(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
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

  // Given the current interval [l,u], this function computes `meet([l,u], max(a, b))`.
  CUDA INLINE constexpr this_type& max(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    l.meet(battery::max(a.l, b.l));
    u.meet(battery::max(a.u, b.u));
    return *this;
  }

  // Let a = max(b, x), we update x according to a and b.
  CUDA INLINE constexpr this_type& max_back(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    if (a.l > b.u) l.meet(a.l);
    u.meet(a.u);
    return *this;
  }

  // Let x = (a = b), we update x according to a and b.
  CUDA INLINE constexpr this_type& req(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    if (!contains(VT{0.0}) || (a.l == b.u && a.u == b.l)) {
      l.meet(VT{1.0});
      u.meet(VT{1.0});
    }
    else if (!contains(VT{1.0}) || a.l > b.u || a.u < b.l) {
      l.meet(VT{0.0});
      u.meet(VT{0.0});
    }
    return *this;
  }

  // Let a = (x = b), we update x according to a and b.
  CUDA INLINE constexpr this_type& req_back(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    if (a.is_singleton(VT{1.0})) {
      l.meet(b.l);
      u.meet(b.u);
    }
    return *this;
  }

  // Let x = (a <= b), we update x according to a and b.
  CUDA INLINE constexpr this_type& rleq(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    if (!contains(VT{0.0}) || a.u <= b.l) {
      l.meet(VT{1.0});
      u.meet(VT{1.0});
    }
    else if (!contains(VT{1.0}) || a.l() > b.u) {
      l.meet(VT{0.0});
      u.meet(VT{0.0});
    }
    return *this;
  }

  // Let a = (x <= b), we update x according to a and b.
  CUDA INLINE constexpr this_type& rleq_lback(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    if (a.is_singleton(VT{1.0})) {
      u.meet(b.u);
    }
    else if (a.is_singleton(VT{0.0})) {
      l.meet(b.l);
    }
    return *this;
  }

  // Let a = (b <= x), we update x according to a and b.
  CUDA INLINE constexpr this_type& rleq_rback(basic_type a, basic_type b) {
    if (a.is_bot() || b.is_bot()) return meet_bot();
    if (a.is_singleton(VT{1.0})) {
      l.meet(b.l);
    }
    else if (a.is_singleton(VT{0.0})) {
      u.meet(b.u);
    }
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
CUDA INLINE constexpr FInterval<VT, Mem> join_nobot(FInterval<VT, Mem> a, FInterval<VT, Mem> b) {
  a.join_nobot(b);
  return a;
}

template<class VT, class Mem1, class Mem2>
CUDA INLINE constexpr bool operator==(const FInterval<VT, Mem1>& a, const FInterval<VT, Mem2>& b)
{
  return a.eq(b);
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
  y.mul_back(x, z);
  z.mul_back(x, y);
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
  x.req(y, z);
  y.req_back(x, z);
  z.req_back(x, y);
}

template<class VT>
CUDA INLINE constexpr void frleq(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  x.rleq(y, z);
  y.rleq_lback(x, z);
  z.rleq_rback(x, y);
}

}

namespace ask {

template<class VT>
CUDA INLINE constexpr bool fadd(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.is_singleton() && y.is_singleton() && z.is_singleton() && x.lb() == y.lb() + z.lb());
}

template<class VT>
CUDA INLINE constexpr bool fsub(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return fadd(y, x, z);
}

template<class VT>
CUDA INLINE constexpr bool fmul(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.is_singleton() &&
      ((y.is_singleton() && z.is_singleton() && x.lb() == y.lb() * z.lb()) ||
      (x.lb() == VT{0.0} && (y.is_singleton(VT{0.0}) || z.is_singleton(VT{0.0})))));
}

template<class VT>
CUDA INLINE constexpr bool fdiv(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
         (x.is_singleton() && y.is_singleton() && !z.contains(VT{0.0}) &&
            ((z.is_singleton() && x.lb() == y.lb() / z.lb()) ||
             (x.lb() ==  VT{0.0} && y.lb() ==  VT{0.0}))); // 0 = 0 / z (for any z != 0).
}

template<class VT>
CUDA INLINE constexpr bool fmin(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.lb() == y.ub() && x.ub() == y.lb() && y.ub() <= z.lb()) ||
    (x.lb() == z.ub() && x.ub() == z.lb() && z.ub() <= y.lb());
}

template<class VT>
CUDA INLINE constexpr bool fmax(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.lb() == y.ub() && x.ub() == y.lb() && y.lb() >= z.ub()) ||
    (x.lb() == z.ub() && x.ub() == z.lb() && z.lb() >= y.ub());
}

template<class VT>
CUDA INLINE constexpr bool freq(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
    (x.is_singleton(VT{1.0}) && y.ub() == z.lb() && y.lb() == z.ub()) ||
    (x.is_singleton(VT{0.0}) && (y.ub() < z.lb() || y.lb() > z.ub()));
}

template<class VT>
CUDA INLINE constexpr bool frleq(FInterval<VT>& x, FInterval<VT>& y, FInterval<VT>& z) {
  return x.is_bot() || y.is_bot() || z.is_bot() ||
      (x.is_singleton(VT{1.0}) && y.ub() <= z.lb()) ||
      (x.is_singleton(VT{0.0}) && y.lb() > z.ub());
}

} // namespace ask
} // namespace lala

#endif
