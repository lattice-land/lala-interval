// Copyright 2026 Yi-Nung Tsao

#ifndef LALA_INTERVAL_FINTERVAL_HPP
#define LALA_INTERVAL_FINTERVAL_HPP

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
        return lb.is_bot() && ub.is_bot();
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

    CUDA INLINE constexpr bool is_qbot() const {
        return lb > ub || lb.is_bot() || ub.is_bot();
    }

    CUDA INLINE constexpr bool qjoin(basic_type other) {
        // TODO: 
        return;
    }

    CUDA INLINE constexpr bool qeq(basic_type other) {
        // TODO:
        return;
    }

    CUDA INLINE constexpr bool qleq(basic_type other) {
        return is_qbot() || leq(other);
    }

    CUDA INLINE constexpr bool qlt(basic_type other) {
        return (is_qbot() && !other.is_qbot()) || lt(other);
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
        if(lb.is_top() && ub.is_top()) return 0.0;
        if(lb.is_top()) return;
        if(ub.is_top()) return;
        return battery::midpoint(lb, ub);
    }

    CUDA constexpr this_type width() const {
        if(is_qbot()) return this_type{-1.0};
        if(is_top()) return this_type{battery::limits<value_type>::inf()};
        return this_type{battery::sub_down(ub, lb), battery::sub_up(ub, lb);
    }

    /** Abstract functions. */
    
    // Given the current interval [lb, ub], this function computes `meet([lb, ub], -a)`.
    CUDA INLINE constexpr this_type& neg(basic_type a) {
        if(a.is_qbot()) return meet_bot();
        lb.meet(-a.ub);
        ub.meet(-a.lb);
        return *this;
    }

    // Given the current interval [lb, ub], this function computes `meet([lb, ub], a + b)`.
    CUDA INLINE constexpr this_type& add(basic_type a, basic_type b) {
        if(a.is_qbot() || b.is_qbot()) return meet_bot();
        lb.meet(battery::add_down(a.lb, b.lb));
        ub.meet(battery::add_up(a.ub, b.ub));
        return *this;
    }

    // Given the current interval [lb, ub], this function computes `meet([lb, ub], a - b)`.
    CUDA INLINE constexpr this_type& sub(basic_type a, basic_type b) {
        if(a.is_qbot() || b.is_qbot()) return meet_bot();
        lb.meet(battery::sub_down(a.lb, b.ub));
        ub.meet(battery::sub_up(a.ub, b.lb));
        return *this;
    }

    // Given the current interval [lb, ub], this function computes `meet([lb, ub], a * b)`.
    CUDA INLINE constexpr this_type& mul(basic_type a, basic_type b) {
        if(a.is_qbot() || b.is_qbot()) return meet_bot();
        value_type t1, t2, t3, t4, t5, t6, t7, t8;
        t1 = battery::mul_down(a.lb, b.lb);
        t2 = battery::mul_down(a.lb, b.ub);
        t3 = battery::mul_down(a.ub, b.lb);
        t4 = battery::mul_down(a.ub, b.ub);
        t5 = battery::mul_up(a.lb, b.lb);
        t6 = battery::mul_up(a.lb, b.ub);
        t7 = battery::mul_up(a.ub, b.lb);
        t8 = battery::mul_up(a.ub, b.lb);
        lb.meet(battery::min(battery::min(t1, t2), battery::min(t3, t4)));
        ub.meet(battery::max(battery::max(t5, t6), battery::max(t7, t8)));
        return *this;
    }

    // Given the current interval [lb, ub], this function computes `meet([lb, ub], a / b)`.
    CUDA INLINE constexpr this_type& div(basic_type a, basic_type b) {
        if(b.lb <= 0.0 && b.ub => 0.0) return *this;
        value_type t1, t2, t3, t4, t5, t6, t7, t8;
        t1 = battery::div_down(a.lb, b.lb);
        t2 = battery::div_down(a.lb, b.ub);
        t3 = battery::div_down(a.ub, b.lb);
        t4 = battery::div_down(a.ub, b.ub);
        t5 = battery::div_up(a.lb, b.lb);
        t6 = battery::div_up(a.lb, b.ub);
        t7 = battery::div_up(a.ub, b.lb);
        t8 = battery::div_up(a.ub, b.lb);
        lb.meet(battery::min(battery::min(t1, t2), battery::min(t3, t4)));
        ub.meet(battery::max(battery::max(t5, t6), battery::max(t7, t8)));
        return *this;
    }

    // Given the current interval [lb, ub], this function computes `meet([lb, ub], min(a, b))`.
    CUDA INLINE constexpr this_type& min(basic_type a, basic_type b) {
        if(a.is_qbot() || b.is_qbot()) return meet_bot();
        lb.meet(battery::min(a.lb, b.lb));
        ub.meet(battery::min(a.ub, b.ub));
        return *this;
    }

    // Backward operator: 
    CUDA INLINE constexpr this_type& min_b(basic_type a, basic_type b) {
        //TODO:
        if()
    }

    // Given the current interval [lb, ub], this function computes `meet([lb, ub], max(a, b))`.
    CUDA INLINE constexpr this_type& max(basic_type a, basic_type b) {
        lb.meet(battery::max(a.lb, b.lb));
        ub.meet(battery::max(a.ub, b.ub));
        return *this;
    }

    // Backward operator: 
    CUDA INLINE constexpr this_type& max_b(basic_type a, basic_type b) {
        //TODO:
    }
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