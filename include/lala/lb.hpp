// Copyright 2026 Pierre Talbot

#ifndef LALA_INTERVAL_LB_HPP
#define LALA_INTERVAL_LB_HPP

#include <iostream>
#include "battery/memory.hpp"

namespace lala {

template<class VT, class Mem = battery::local_memory>
class LB
{
public:
  using value_type = VT;
  using memory_type = Mem;
  using this_type = LB<value_type, memory_type>;
  using basic_type = LB<value_type>;
  using atomic_type = memory_type::template atomic_type<value_type>;

  template<class VT2, class Mem2>
  friend class LB;

  constexpr static const bool is_totally_ordered = true;
  constexpr static const char* name = "LB";

private:
  atomic_type value;

  CUDA INLINE static constexpr value_type neg_inf() {
    return battery::limits<value_type>::neg_inf();
  }

  CUDA INLINE static constexpr value_type inf() {
    return battery::limits<value_type>::inf();
  }

public:
  CUDA INLINE static constexpr this_type bot() { return inf(); }
  CUDA INLINE static constexpr this_type top() { return neg_inf(); }

  CUDA constexpr LB(): value(neg_inf()) {}
  CUDA constexpr LB(value_type x): value(x) {}

  CUDA constexpr LB(const this_type& other): value(other.load()) {}
  template <class Mem2>
  CUDA constexpr LB(const LB<value_type, Mem2>& other): value(other.load()) {}

  constexpr LB(this_type&& other) = default;

  CUDA INLINE constexpr this_type& operator=(const this_type& other) {
    memory_type::store(value, other.load());
    return *this;
  }

  template <class Mem2>
  CUDA INLINE constexpr this_type& operator=(const LB<VT, Mem2>& other) {
    memory_type::store(value, other.load());
    return *this;
  }

  CUDA INLINE constexpr this_type& operator=(value_type other) {
    memory_type::store(value, other);
    return *this;
  }

  CUDA INLINE constexpr value_type load() const {
    return memory_type::load(value);
  }

  CUDA INLINE constexpr atomic_type& atomic() { return value; }
  CUDA INLINE constexpr operator value_type() const { return load(); }

  CUDA INLINE constexpr bool is_top() const {
    return load() == top();
  }

  CUDA INLINE constexpr bool is_bot() const {
    return load() == bot();
  }

  CUDA INLINE constexpr void join_top() {
    memory_type::store(value, neg_inf());
  }

  CUDA INLINE constexpr bool join(basic_type other) {
    if(load() > other.value) {
      memory_type::store(value, other.value);
      return true;
    }
    return false;
  }

  CUDA INLINE constexpr void meet_bot() {
    memory_type::store(value, inf());
  }

  CUDA INLINE constexpr bool meet(basic_type other) {
    if(load() < other.value) {
      memory_type::store(value, other.value);
      return true;
    }
    return false;
  }

  CUDA INLINE constexpr bool leq(basic_type other) const {
    return load() >= other.value;
  }

  CUDA INLINE constexpr bool lt(basic_type other) const {
    return load() > other.value;
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
CUDA INLINE constexpr LB<VT, Mem> join(LB<VT, Mem> a, LB<VT, Mem> b) {
  a.join(b);
  return a;
}

template <class VT, class Mem>
CUDA INLINE constexpr LB<VT, Mem> meet(LB<VT, Mem> a, LB<VT, Mem> b) {
  a.meet(b);
  return a;
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator==(const LB<VT, Mem1>& a, const LB<VT, Mem2>& b)
{
  return a.load() == b.load();
}

template<class VT, class Mem1, class Mem2>
CUDA constexpr bool operator!=(const LB<VT, Mem1>& a, const LB<VT, Mem2>& b)
{
  return a.load() != b.load();
}

template <class VT, class Mem>
std::ostream& operator<<(std::ostream &s, const LB<VT, Mem>& a) {
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
