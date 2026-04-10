// Copyright 2026 Yi-Nung Tsao

#ifndef LALA_INTERVAL_FINTERVAL_HPP
#define LALA_INTERVAL_FINTERVAL_HPP

#include "lb.hpp"
#include "ub.hpp"

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
    lb_type lb;
    ub_type ub;

public:
    CUDA INLINE static constexpr this_type bot() { return this_type(lb_type::bot(), ub_type::bot()); } 
    CUDA INLINE static constexpr this_type top() { return this_type(lb_type::top(), ub_type::top()); }

    constexpr FInterval() = default;
    constexpr FInterval(const this_type&) = default;
    CUDA constexpr FInterval(value_type x): lb(x), ub(x) {}
    CUDA constexpr FInterval(value_type _lb, value_type _ub) lb(_lb), ub(_ub) {}

    template <class Mem2>
    CUDA constexpr FInterval(const FInterval<value_type, Mem2>& other) 
     : lb(other.lb)
     , ub(other.ub)
    {}

    template <class Mem2>
    CUDA INLINE constexpr this_type& operator=(const FInterval<value_type, Mem2>& other) {
        lb = other.lb;
        ub = other.ub;
        return *this;
    }

    constexpr this_type& operator=(const this_type&) = default;

    CUDA INLINE constexpr lb_type lb() { return lb; }
    CUDA INLINE constexpr ub_type ub() { return ub; }
    CUDA INLINE constexpr const lb_type& lb() { return lb; }
    CUDA INLINE constexpr const ub_type& ub() { return ub; }

    CUDA INLINE constexpr bool is_bot() const { 
        return lb > ub || lb.is_bot() || ub.is_bot();
    }

    CUDA INLINE constexpr bool is_top() const {
        return lb.is_top() && ub.is_top();
    }

    CUDA INLINE constexpr void join_top() {
        lb.join_top();
        ub.join_top();
    }

    CUDA INLINE constexpr void meet_bot() {
        lb.meet_bot();
        ub.meet_bot();
    }

    CUDA INLINE constexpr bool meet(basic_type other) {
        bool result = lb.meet(other.lb);
        result |= ub.meet(other.ub);
        return result;
    }

    CUDA INLINE constexpr bool join(basic_type other) {
        bool result = lb.join(other.lb);
        result |= ub.join(other.ub);
        return result;
    }

    CUDA INLINE constexpr bool leq(basic_type other) const {
        return lb >= other.lb && ub <= other.ub;
    }

    CUDA INLINE constexpr bool lt(basic_type other) const {
        return leq(other) && (lb != other.lb || ub != other.ub);
    }

    CUDA INLINE constexpr bool leqbot(basic_type other) const {
        // TODO:
        return;
    }

    CUDA INLINE constexpr bool ltbot(basic_type other) const {
        // TODO:
        return;
    }

    CUDA NI void print() const {
        printf("[");
        lb.print();
        printf(", ");
        ub.print();
        printf("]\n");
    }

    CUDA constexpr value_type midpoint() const {
        // TODO:
        return;
    }

    CUDA constexpr value_type width() const {
        // if (!(is_bot() && is_top())) return value_type{-1.0};
        // TODO: add a precondition.
        return battery::sub_down(ub.load(), lb.load());
    }

    /** Abstract functions. */
    // TODO: 
};

// Lattice operations

template <class VT, class Mem>
CUDA constexpr FInterval<VT, Mem> join(const FInterval<VT, Mem>& a, const FInterval<VT, Mem>& b) {
  return FInterval<VT, Mem>(join(a.lb(), b.lb()), join(a.ub(), b.ub()));
}

template <class VT, class Mem>
CUDA constexpr FInterval<VT, Mem> meet(const FInterval<VT, Mem>& a, const FInterval<VT, Mem>& b) {
  return FInterval<VT, Mem>(meet(a.lb(), b.lb()), meet(a.ub(), b.ub()));
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator==(const FInterval<VT, Mem1>& a, const FInterval<VT, Mem2>& b)
{
  return a.lb() == b.lb() && a.ub() == b.ub();
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator!=(const FInterval<VT, Mem1>& a, const FInterval<VT, Mem2>& b)
{
  return !(a == b);
}

template<class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const FInterval<VT, Mem> &itv) {
  return s << "[" << itv.lb() << "," << itv.ub() << "]";
}

}

#endif