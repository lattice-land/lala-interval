// Copyright 2026 Yi-Nung Tsao

#ifndef LALA_FLB_HPP
#define LALA_FLB_HPP

#include <type_traits>
#include <utility>
#include <cmath>
#include <iostream>
#include "../logic/logic.hpp"
#include "pre_flb.hpp"
#include "pre_fub.hpp"
#include "pre_zlb.hpp"
#include "pre_zub.hpp"
#include "../b.hpp"
#include "battery/memory.hpp"

namespace lala {

template<class VT, class Mem>
class FLB
{
public:
    using value_type = VT; 
    using memory_type = Mem;
    using this_type = FLB<value_type, memory_type>;
    using basic_type = FLB<value_type, battery::local_memory>;
    using atomic_type = memory_type::template atomic_type<value_type>;
    using top = battery::limits<value_type>::neg_inf();
    using bot = battery::limits<value_type>::inf();

    constexpr static const bool is_totally_ordered = true;
    constexpr static const bool preserve_bot = true;
    constexpr static const bool preserve_top = true;
    constexpr static const bool preserve_join = true;
    constexpr static const bool preserve_meet = true;
    /** Note that -0 and +0 are treated as the same element. */
    constexpr static const bool injective_concretization = true;
    constexpr static const bool preserve_concrete_covers = false;
    constexpr static const bool is_lower_bound = true;
    constexpr static const bool is_upper_bound = false;
    constexpr static const char* name = "FLB";
    constexpr static const bool is_arithmetic = true;
    CUDA constexpr static value_type zero() { return 0.0; }
    CUDA constexpr static value_type one() { return 1.0; }

private:
    atomic_type value;

public:
    CUDA static constexpr basic_type top() { return basic_type(top); }
    CUDA static constexpr basic_type bot() { return basic_type(bot); }
    CUDA constexpr FLB(): value() { memory_type::store(value, top); }
    CUDA constexpr FLB(value_type x): value() { memory_type::store(value, x); }
    const FLB(const this_type& other) { memory_type::store(value, other.load()); }
    const FLB(this_type&& other) { memory_type::store(value, other.load()); }

    CUDA constexpr this_type& operator=(const this_type& other) {
        memory_type::store(value, other.load());
        return *this;
    }

    CUDA constexpr value_type load() const { return memory_type::load(value); }
    CUDA constexpr atomic_type& atomic_load() { return value; }
    CUDA constexpr void store(basic_type other) { memory_type::store(value, other.load()); }
    CUDA constexpr operator value_type() const { return load(); }
    CUDA constexpr local::B is_top() const { return battery::isinf(load()); }
    CUDA constexpr local::B is_bot() const { return battery::isinf(load()); }
    CUDA static constexpr value_type meet(value_type x, value_type y) { return battery::max(x, y); }
    CUDA static constexpr value_type join(value_type x, value_type y) { return battery::min(x, y); }

    CUDA static constexpr bool meet(const basic_type& other) { 
        value_type r1 = load();
        if(lt(r1, other.load())) {
            memory_type::store(value, other.load());
            return true;
        }
        return false; 
    }

    CUDA static constexpr bool join(const basic_type& other) { 
        value_type r1 = load();
        if(lt(other.load(), r1)) {
            memory_type::store(value, other.load());
            return true;
        }
        return false; 
    }

    CUDA constexpr void meet_bot() { memory_type::store(value, bot); }
    CUDA constexpr void join_top() { memory_type::store(value, top); }

    CUDA NI void print() const {
        if(is_bot()) {
            printf("\u22A5");
        }
        else if(is_top()) {
            printf("\u22A4");
        }
        else {
            ::battery::print(load());
        }
    }

private: 
    CUDA static constexpr bool leq(value_type x, value_type y) { return x >= y; }
    CUDA static constexpr bool lt(value_type x, value_type y) { return x > y; }
};

template<class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const FLB<VT, Mem> &a) {
  if(a.is_bot()) {
    s << "\u22A5";
  }
  else if(a.is_top()) {
    s << "\u22A4";
  }
  else {
    s << a.load();
  }
  return s;
}

}

#endif 