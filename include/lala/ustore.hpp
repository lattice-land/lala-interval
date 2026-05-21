// Copyright 2021 Pierre Talbot

#ifndef LALA_CORE_USTORE_HPP
#define LALA_CORE_USTORE_HPP


namespace lala {

/** A variable identifier is a pair (aty, index) such that `index` is the index of the variable inside the abstract domain identified with `aty` (abstract type). */
template <class ValueType = int, int num_bits_aty = 5>
class VarID {
public:
  using value_type = ValueType;

private:
  value_type value;

public:
  CUDA constexpr VarID(): value(-1) {}
  constexpr VarID(const VarID&) = default;
  constexpr VarID(VarID&&) = default;
  constexpr VarID& operator=(const VarID&) = default;
  constexpr VarID& operator=(VarID&&) = default;
  CUDA constexpr bool operator==(const VarID& other) const {
    return value == other.value;
  }
  CUDA constexpr bool operator!=(const VarID& other) const {
    return value != other.value;
  }

  CUDA constexpr VarID(value_type atype, value_type idx): value((idx << num_bits_aty) | atype) {
    assert(atype >= 0);
    assert(idx >= 0);
    assert(atype < (1 << num_bits_aty));
    assert(idx < (1 << (sizeof(value_type)*8 - num_bits_aty - 1))); // -1 bit because we use -1 to represent "unknown ID", hence negative numbers are not used.
  }

  CUDA constexpr static value_type untyped() {
    return -1;
  }

  CUDA constexpr bool is_unknown() const {
    return value == -1;
  }

  CUDA constexpr value_type aty() const {
    return is_unknown() ? -1 : (value & ((1 << num_bits_aty) - 1));
  }

  CUDA constexpr value_type idx() const {
    return is_unknown() ? -1 : value >> num_bits_aty;
  }

  CUDA constexpr void type_as(value_type atype) {
    value = (vid() << num_bits_aty) | atype;
  }
};

/** The universe store abstract domain is a _domain transformer_ built on top of an abstract universe `U`.
Concretization function: \f$ \gamma(\rho) := \bigcap_{x \in \pi(\rho)} \gamma_{U_x}(\rho(x)) \f$.
The bot element is smashed and the equality between two stores is represented by the following equivalence relation, for two stores \f$ S \f$ and \f$ T \f$:
\f$ S \equiv T \Leftrightarrow \forall{x \in \mathit{Vars}},~S(x) = T(x) \lor \exists{x \in \mathit{dom}(S)},\exists{y \in \mathit{dom}(T)},~S(x) = \bot \land T(y) = \bot \f$.
Intuitively, it means that either all elements are equal or both stores have a bot element, in which case they "collapse" to the bot element, and are considered equal.

The top element is the element \f$ \langle \top, \ldots \rangle \f$, that is an infinite number of universes initialized to top.
In practice, we cannot represent infinite collections, so we represent top either as the empty collection or with a finite number of top elements.
Therefore, the top element is an equivalence class, and any sequence of top elements is considered equal.
Any finite store \f$ \langle x_1, \ldots, x_n \rangle \f$ should be seen as the concrete store \f$ \langle x_1, \ldots, x_n, \top, \ldots \rangle \f$.

This semantics has implication when joining or merging two elements.
For instance, \f$ \langle 1 \rangle.\mathit{meet}(\langle \bot, 4 \rangle) \f$ will be equal to bottom, in that case represented by \f$ \langle \bot \rangle \f$.

Template parameters:
  - `U` is the type of the abstract universe.
  - `Allocator` is the allocator of the underlying array of universes.
  - `VarIDType` is the type of the variable's identifier.
  - `MemType` is the type of memory used to represent a private Boolean member denoting whether the store is bot or not.
*/
template<class U, class Allocator, class VarIDType = VarID<>, class MemType = typename U::memory_type>
class UStore {
public:
  using universe_type = U;
  using basic_universe = typename universe_type::basic_type;
  using allocator_type = Allocator;
  using this_type = UStore<universe_type, allocator_type>;
  using memory_type = MemType;
  using id_type = typename VarIDType::value_type;

  constexpr static const bool is_totally_ordered = false;
  constexpr static const char* name = "UStore";

  template<class U2, class Alloc2>
  friend class UStore;

private:
  using store_type = battery::vector<universe_type, allocator_type>;

  id_type atype;
  store_type data;
  LB<bool, memory_type> is_at_bot;

public:
  CUDA UStore(const this_type& other)
    : atype(other.atype), data(other.data), is_at_bot(other.is_at_bot)
  {}

  /** Initialize an empty store (top element). */
  CUDA UStore(const allocator_type& alloc = allocator_type())
   : atype(VarIDType::untyped()), data(alloc), is_at_bot(false)
  {}

  /** Initialize an empty store (top element). */
  CUDA UStore(id_type atype, const allocator_type& alloc = allocator_type())
   : atype(atype), data(alloc), is_at_bot(false)
  {}

  /** Initialize a store of size `n`. */
  CUDA UStore(id_type atype, size_t n, const allocator_type& alloc = allocator_type())
   : atype(atype), data(n, alloc), is_at_bot(false)
  {}

  template<class R>
  CUDA UStore(const UStore<R, allocator_type>& other)
    : atype(other.atype), data(other.data), is_at_bot(other.is_at_bot)
  {}

  template<class R, class Alloc2>
  CUDA UStore(const UStore<R, Alloc2>& other, const allocator_type& alloc = allocator_type())
    : atype(other.atype), data(other.data, alloc), is_at_bot(other.is_at_bot)
  {}

  /** Copy the ustore `other` in the current element.
   *  `deps` can be empty and is not used besides to get the allocator (since this abstract domain does not have dependencies). */
  template<class R, class Alloc2, class Deps>
  CUDA UStore(const UStore<R, Alloc2>& other, const Deps& deps)
   : UStore(other, deps.template get_allocator<allocator_type>()) {}

  CUDA UStore(this_type&& other):
    atype(other.atype), data(std::move(other.data)), is_at_bot(other.is_at_bot) {}

  CUDA allocator_type get_allocator() const {
    return data.get_allocator();
  }

  CUDA id_type aty() const {
    return atype;
  }

  CUDA size_t size() const {
    return data.size();
  }

  CUDA static this_type top(id_type atype = VarIDType::untyped(),
    const allocator_type& alloc = allocator_type{})
  {
    return UStore(atype, alloc);
  }

  /** A special symbolic element representing top. */
  CUDA static this_type bot(AType atype = VarIDType::untyped(),
    const allocator_type& alloc = allocator_type{})
  {
    auto s = UStore{atype, alloc};
    s.meet_bot();
    return std::move(s);
  }

  /** \return `true` if at least one element is equal to bot in the store, `false` otherwise. */
  CUDA bool is_bot() const {
    return is_at_bot.load();
  }

  /** The top element of a store of `n` variables is when all variables are at top, or the store is empty.
   * We do not expect to use this operation a lot, so its complexity is linear in the number of variables. */
  CUDA bool is_top() const {
    if(is_at_bot) { return false; }
    for(size_t i = 0; i < size(); ++i) {
      if(!data[i].is_top()) {
        return false;
      }
    }
    return true;
  }

private:
  struct SingleThreadGroup {
    CUDA inline unsigned int thread_rank() { return 0; }
    CUDA inline unsigned int num_threads() { return 1; }
    CUDA inline void sync() { return; }
  };

public:
  CUDA void resize(size_t n) {
    data.resize(n);
  }

  // parallel access: `this` and `other` cannot be resized by another thread during the execution of this function.
  template <class Group, class U2, class Alloc2>
  CUDA bool join(const Group& group, const UStore<U2, Alloc2>& other)  {
    if(other.is_bot()) { return false; }
    int n = battery::min(vars(), other.vars());
    bool has_changed = is_at_bot.meet(other.is_at_bot);
    for (int i = group.thread_rank(); i < n; i += group.num_threads()) {
      has_changed |= data[i].join(other.data[i]);
    }
    for (int i = n + group.thread_rank(); i < size(); i += group.num_threads()) {
      has_changed |= data[i].join(universe_type::top());
    }
    return has_changed;
  }

  template <class U2, class Alloc2>
  CUDA bool join(const UStore<U2, Alloc2>& other)  {
    return join(SingleThreadGroup{}, other);
  }

  template <class Group>
  CUDA void join_top(const Group& group) {
    is_at_bot.join_top();
    for(int i = group.thread_rank(); i < data.size(); i += group_num_threads()) {
      data[i].join_top();
    }
  }

  CUDA void join_top() {
    join_top(SingleThreadGroup{});
  }

  // precondition: `other.size() <= size()`
  template <class Group, class U2, class Alloc2>
  CUDA bool meet(const Group& group, const UStore<U2, Alloc2>& other)  {
    assert(other.size() <= size());
    if(is_bot()) { return false; }
    if(other.is_bot()) { is_at_bot.meet_bot(); return true; }
    bool has_changed = false;
    for (int i = group.thread_rank(); i < other.size(); i += group.num_threads()) {
      has_changed |= data[i].meet(other.data[i]);
    }
    return has_changed;
  }

  template <class U2, class Alloc2>
  CUDA bool meet(const UStore<U2, Alloc2>& other)  {
    if(is_bot()) { return false; }
    if(other.is_bot()) { is_at_bot.meet_bot(); return true; }
    if(other.size() > size()) {
      resize(other.size());
    }
    return meet(SingleThreadGroup{}, other);
  }

  template <class Group, class Store>
  CUDA void copy_to(const Group& group, Store& other) const {
    assert(size() == other.size());
    if(group.thread_rank() == 0) {
      other.is_at_bot = is_at_bot;
    }
    if(is_at_bot) {
      return;
    }
    for (int i = group.thread_rank(); i < other.size(); i += group.num_threads()) {
      other.data[i] = data[i];
    }
  }

  template <class Store>
  CUDA void copy_to(Store& other) const {
    copy_to(SingleThreadGroup{}, other);
  }

  template <class AVar>
  CUDA const universe_type& project(AVar x) const {
    assert(x.aty() == aty());
    assert(x.vid() < data.size());
    return data[x.vid()];
  }

  /** This projection must stay const, otherwise the user might modify the result, but we need to know in case we reach `top`. */
  CUDA const universe_type& operator[](int x) const {
    return data[x];
  }

  template <class AVar>
  CUDA const universe_type& operator[](AVar x) const {
    return project(x);
  }

  CUDA void meet_bot() {
    is_at_bot.meet_bot();
  }

  /** Embedding is similar to `project(i).meet(dom)` with additional care for the case when the result is bottom (which is the reason why `project` cannot be directly used).
   * precondition: `size() > x`
  */
  CUDA bool embed(int x, const universe_type& dom) {
    assert(x < data.size());
    bool has_changed = data[x].meet(dom);
    if(has_changed && data[x].is_bot()) {
      is_at_bot.meet_bot();
    }
    return has_changed;
  }

  template <class AVar>
  CUDA bool embed(AVar x, const universe_type& dom) {
    assert(x.aty() == aty());
    return embed(x.vid(), dom);
  }

  CUDA void print() const {
    if(is_bot()) {
      printf("\u22A5 | ");
    }
    printf("<");
    for(int i = 0; i < size(); ++i) {
      data[i].print();
      printf("%s", (i+1 == size() ? "" : ", "));
    }
    printf(">\n");
  }
};

// Lattice operations.
// Note that we do not consider the logical names.
// These operations are only considering the indices of the elements.

template<class L, class K, class Alloc>
CUDA auto fmeet(const UStore<L, Alloc>& a, const UStore<K, Alloc>& b)
{
  using U = decltype(fmeet(a[0], b[0]));
  if(a.is_bot() || b.is_bot()) {
    return UStore<U, Alloc>::bot(UNTYPED, a.get_allocator());
  }
  int max_size = battery::max(a.vars(), b.vars());
  int min_size = battery::min(a.vars(), b.vars());
  UStore<U, Alloc> res(UNTYPED, max_size, a.get_allocator());
  for(int i = 0; i < min_size; ++i) {
    res.embed(i, fmeet(a[i], b[i]));
  }
  for(int i = min_size; i < a.vars(); ++i) {
    res.embed(i, a[i]);
  }
  for(int i = min_size; i < b.vars(); ++i) {
    res.embed(i, b[i]);
  }
  return res;
}

template<class L, class K, class Alloc>
CUDA auto fjoin(const UStore<L, Alloc>& a, const UStore<K, Alloc>& b)
{
  using U = decltype(fjoin(a[0], b[0]));
  if(a.is_bot()) {
    if(b.is_bot()) {
      return UStore<U, Alloc>::bot(UNTYPED, a.get_allocator());
    }
    else {
      return UStore<U, Alloc>(b);
    }
  }
  else if(b.is_bot()) {
    return UStore<U, Alloc>(a);
  }
  else {
    int min_size = battery::min(a.vars(), b.vars());
    UStore<U, Alloc> res(UNTYPED, min_size, a.get_allocator());
    for(int i = 0; i < min_size; ++i) {
      res.embed(i, fjoin(a[i], b[i]));
    }
    return res;
  }
}

template<class L, class K, class Alloc1, class Alloc2>
CUDA bool operator<=(const UStore<L, Alloc1>& a, const UStore<K, Alloc2>& b)
{
  if(b.is_top()) {
    return true;
  }
  else {
    int min_size = battery::min(a.vars(), b.vars());
    for(int i = 0; i < min_size; ++i) {
      if(!(a[i] <= b[i])) {
        return false;
      }
    }
    for(int i = min_size; i < b.vars(); ++i) {
      if(!b[i].is_top()) {
        return false;
      }
    }
  }
  return true;
}

template<class L, class K, class Alloc1, class Alloc2>
CUDA bool operator<(const UStore<L, Alloc1>& a, const UStore<K, Alloc2>& b)
{
  if(a.is_bot()) {
    return !b.is_bot();
  }
  else {
    int min_size = battery::min(a.vars(), b.vars());
    bool strict = false;
    for(int i = 0; i < a.vars(); ++i) {
      if(i < b.vars()) {
        if(a[i] < b[i]) {
          strict = true;
        }
        else if(!(a[i] <= b[i])) {
          return false;
        }
      }
      else if(!a[i].is_top()) {
        strict = true;
        break;
      }
    }
    for(int i = min_size; i < b.vars(); ++i) {
      if(!b[i].is_top()) {
        return false;
      }
    }
    return strict;
  }
}

template<class L, class K, class Alloc1, class Alloc2>
CUDA bool operator>=(const UStore<L, Alloc1>& a, const UStore<K, Alloc2>& b)
{
  return b <= a;
}

template<class L, class K, class Alloc1, class Alloc2>
CUDA bool operator>(const UStore<L, Alloc1>& a, const UStore<K, Alloc2>& b)
{
  return b < a;
}

template<class L, class K, class Alloc1, class Alloc2>
CUDA bool operator==(const UStore<L, Alloc1>& a, const UStore<K, Alloc2>& b)
{
  if(a.is_bot()) {
    return b.is_bot();
  }
  else if(b.is_bot()) {
    return false;
  }
  else {
    int min_size = battery::min(a.vars(), b.vars());
    for(int i = 0; i < min_size; ++i) {
      if(a[i] != b[i]) {
        return false;
      }
    }
    for(int i = min_size; i < a.vars(); ++i) {
      if(!a[i].is_top()) {
        return false;
      }
    }
    for(int i = min_size; i < b.vars(); ++i) {
      if(!b[i].is_top()) {
        return false;
      }
    }
  }
  return true;
}

template<class L, class K, class Alloc1, class Alloc2>
CUDA bool operator!=(const UStore<L, Alloc1>& a, const UStore<K, Alloc2>& b)
{
  return !(a == b);
}

template<class L, class Alloc>
std::ostream& operator<<(std::ostream &s, const UStore<L, Alloc> &vstore) {
  if(vstore.is_bot()) {
    s << "\u22A5: ";
  }
  else {
    s << "<";
    for(int i = 0; i < vstore.vars(); ++i) {
      s << vstore[i] << (i+1 == vstore.vars() ? "" : ", ");
    }
    s << ">";
  }
  return s;
}

} // namespace lala

#endif
