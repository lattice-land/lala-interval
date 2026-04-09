// Copyright 2026 Pierre Talbot

#ifndef LALA_INTERVAL_ZLB_HPP
#define LALA_INTERVAL_ZLB_HPP

#include <type_traits>
#include <utility>
#include <cmath>
#include <iostream>
#include "battery/memory.hpp"

namespace lala {

template<class VT, class Mem = battery::local_memory>
class ZLB
{
public:
  using value_type = VT;
  using memory_type = Mem;
  using this_type = ZLB<value_type, memory_type>;
  using basic_type = ZLB<value_type>;
  using atomic_type = memory_type::template atomic_type<value_type>;

  template<class VT2, class Mem2>
  friend class ZLB;

  constexpr static const bool is_totally_ordered = true;
  constexpr static const char* name = "ZLB";

private:
  atomic_type val;

  CUDA INLINE static constexpr this_type neg_inf() {
    return battery::limits<value_type>::neg_inf();
  }

  CUDA INLINE static constexpr this_type inf() {
    return battery::limits<value_type>::inf();
  }

public:
  CUDA INLINE static constexpr this_type bot() { return inf(); }
  CUDA INLINE static constexpr this_type top() { return neg_inf(); }

  CUDA constexpr ZLB(): val(neg_inf()) {}
  CUDA constexpr ZLB(value_type x): val(x) {}

  template <class Mem2>
  CUDA constexpr ZLB(const ZLB<value_type, Mem2>& other): val(other.load()) {}

  constexpr ZLB(const this_type& other) = default;
  constexpr ZLB(this_type&& other) = default;

  CUDA INLINE constexpr this_type& operator=(value_type other) {
    memory_type::store(val, other);
    return *this;
  }

  CUDA INLINE constexpr value_type load() const {
    return memory_type::load(val);
  }

  CUDA INLINE constexpr atomic_type& atomic() { return val; }
  CUDA INLINE constexpr operator value_type() const { return load(); }

  CUDA INLINE constexpr bool is_top() const {
    return load() == neg_inf();
  }

  CUDA INLINE constexpr bool is_bot() const {
    return load() == inf();
  }

  CUDA INLINE constexpr void join_top() {
    memory_type::store(val, neg_inf());
  }

  CUDA INLINE constexpr bool join(basic_type other) {
    if(load() > other.val) {
      memory_type::store(val, other.val);
      return true;
    }
    return false;
  }

  CUDA INLINE constexpr void meet_bot() {
    memory_type::store(val, inf());
  }

  CUDA INLINE constexpr bool meet(basic_type other) {
    if(load() < other.val) {
      memory_type::store(val, other.val);
      return true;
    }
    return false;
  }

  CUDA INLINE constexpr bool leq(basic_type other) const {
    return load() >= other.val;
  }

  CUDA INLINE constexpr bool lt(basic_type other) const {
    return load() > other.val;
  }

  CUDA NI void print() const {
    if(is_bot()) {
      printf("\u221E");
    }
    else if(is_top()) {
      printf("-\u221E");
    }
    else {
      ::battery::print(load());
    }
  }
};

template <class VT, class Mem>
CUDA constexpr ZLB<VT, Mem> join(ZLB<VT, Mem> a, ZLB<VT, Mem> b) {
  return battery::min(a.load(), b.load());
}

template <class VT, class Mem>
CUDA constexpr ZLB<VT, Mem> meet(ZLB<VT, Mem> a, ZLB<VT, Mem> b) {
  return battery::max(a.load(), b.load());
}

template <class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const ZLB<VT, Mem>& a) {
  if(a.is_bot()) {
    s << "\u221E";
  }
  else if(a.is_top()) {
    s << "-\u221E";
  }
  else {
    s << a.load();
  }
  return s;
}

} // namespace lala

#endif
