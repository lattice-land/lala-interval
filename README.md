# Interval Reasoning

This library provides several abstract domains for interval reasoning over integer and real numbers.
We aim to be general enough to be reused across fields:

* [Constraint programming](https://en.wikipedia.org/wiki/Constraint_programming): Enforce _bound(Z)_ and _bound(R)_ consistencies on interval domains (see e.g. [Choi et al. 2006](https://arxiv.org/pdf/cs/0412021)).
* [Abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation): Provide interval abstractions of integer and real numbers, including forward and backward interval arithmetics (see e.g. [Cousot, 2021](https://mitpress.mit.edu/9780262044905/principles-of-abstract-interpretation/)).
* [Conflict-free replicated data type](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type): Provide simple [anonymous state-based CRDTs](https://members.loria.fr/CIgnat/files/replication/Delta-CRDT.pdf) with `LB` and `UB`.
* [Asynchronous fixpoint iterations](https://web.mit.edu/dimitrib/www/pdc.html): Provide lock-free join and meet operations, compatible with execution on GPU hardware (see [Talbot et al., 2022](https://ojs.aaai.org/index.php/AAAI/article/view/20298)).

## Abstract Universes

We propose abstractions of the universe of discourse of integers $\mathbb{Z}$ and real numbers $\mathbb{R}$.
Let $\mathbb{A}$ be either $\mathbb{Z}$ or $\mathbb{R}$.
The following abstractions are approximating any subset of the universe of discourse:

* **Lower bound abstract universe**: `LB` approximates a set $S \subseteq \mathbb{A}$ by taking its lower bound $\mathit{min}~S$ if it is a bounded set, and $-\infty$ otherwise.
* **Upper bound abstract universe**: `UB` approximates a set $S \subseteq \mathbb{A}$ by taking its upper bound $\mathit{max}~S$ if it is a bounded set, and $\infty$ otherwise.
* **Integer interval abstract universe**: `ZInterval` approximates the lower and upper bounds of a set $S \subseteq \mathbb{Z}$.
* **Floating-point interval abstract universe**: `FInterval` approximates the lower and upper bounds of a set $S \subseteq \mathbb{R}$.

We represent infinities $\{-\infty, \infty\}$ using the minimum and maximum representable values on the underlying arithmetic type: for integers type `I` we rely on `std::numeric_limits<I>::min()` and `std::numeric_limits<I>::max()`, and for floating-point type `F` we rely on `-std::numeric_limits<F>::infinity()` and `std::numeric_limits<F>::infinity()`.

### Lattice Operations

We have a unified interface for standard lattice operations.
Let `L` be one of the abstract universe above.

| Operation  | Mathematical notation | Programming notation |
| ------------- | ------------- | ------------- |
| Bottom  | $\bot$ | `L::bot()` |
| Top  | $\top$ | `L::top()` or default constructor `L()` |
| Partial order | $a \leq b$ | `a.leq(b)` |
| Strict partial order | $a < b$ | `a.lt(b)` |
| Meet | $a \sqcap b$ | `meet(a,b)` or `a.meet(b)` (in-place) |
| Join | $a \sqcup b$ | `join(a,b)` or `a.join(b)` (in-place) |

The following operations are mostly there for optimization purposes, but could be easily recovered from the previous lattice operations.

| Operation  | Mathematical notation | Programming notation |
| ------------- | ------------- | ------------- |
| Equality | $a = b$ | `a == b` |
| Disequality | $a \neq b$ | `a != b` |
| Meet bottom | $a \sqcap \bot$ | `a.meet_bot()` (in-place) |
| Join top | $a \sqcup \top$ | `a.join_top()` (in-place) |
| Bottom test | $a = \bot$ | `a.is_bot()` |
| Top test | $a = \top$ | `a.is_top()` |

### Interval Lattice

In this library, the bottom element of the interval abstract universe is the equivalence class of all empty intervals $\set{[\ell,u] \;|\; \ell > u }$, the function `is_bot` is `true` on all such intervals.
We give the corresponding definition of the lattice operations.

| Operation  | Definition | Programming notation |
| ------------- | ------------- | ------------- |
| $\textnormal{isbot}([\ell, u])$ | $\ell > u \lor \ell = \infty \lor u = -\infty$ | `a.is_bot()` |
| $[\ell, u] \leq [\ell', u']$ | $\textnormal{isbot}([\ell, u]) \lor (\ell \geq \ell' \land u \leq u')$ | `a.leq(b)` |
| $[\ell, u] < [\ell', u']$ | $(\textnormal{isbot}([\ell, u]) \land \lnot \textnormal{isbot}([\ell', u'])) \lor ([\ell, u] \leq [\ell', u'] \land (\ell \neq \ell' \lor u \neq u'))$ | `a.lt(b)` |
| $[\ell, u] \sqcup [\ell', u']$ | $\textnormal{join}(a,b)$ (see below) | `join(a,b)` or `a.join(b)` (in-place) |
| $[\ell, u] = [\ell', u']$ | $(\textnormal{isbot}([\ell, u]) \land \textnormal{isbot}([\ell', u'])) \lor (\ell = \ell' \land u = u')$ | `a.eq(b)` |

With the join defined as:
```math
  \textnormal{join}(x, y) \triangleq
    \begin{cases}
        x &\text{if } \textnormal{isbot}(y) \\
        y &\text{if } \textnormal{isbot}(x) \\
        x \sqcup y & \text{otherwise }
    \end{cases}
```

The lattice operations must take care of the cases where one or both arguments are in this equivalence class.
Sometimes, we are sure none of the arguments is bottom, hence we provide more efficient versions named `*_nobot`.

### ZInterval: Abstract Operations

Also known as _abstract transformers_ in the field of abstract interpretation.
In constraint programming, those operations can be used to design _propagators_, see below.

*Note*: To project the interval of an expression, e.g. `y + z`, initialize the result variable to top (e.g. `ZInterval<int> x;`) and call the forward operator on it: `x.add(y,z)`.

In the following, we let `x,y,z` be integer intervals of type `ZInterval`.

| Operation  | Constraint | Forward operator | Left backward operator | Right backward operator |
| ------------- | ------------- | ------------- | ------------- | ------------- |
| Identity  | $x = y$ | `x.meet(y)`  | `y.meet(x)` | n/a |
| Negation  | $x = -y$ | `x.neg(y)`  | `y.neg(x)` | n/a |
| Addition  | $x = y + z$ | `x.add(y,z)`  | `y.sub(x,z)` | `z.sub(x,y)` |
| Subtraction  | $x = y - z$ | `x.sub(y,z)`  | `y.add(x,z)` | `z.sub(y,x)` |
| Multiplication | $x = y * z$ | `x.mul(y, z)` | `y.mul_back(x,z)` | `z.mul_back(x,y)` |
| Floor division | $x = \textnormal{fdiv}(y,z)$ | `x.fdiv(y, z)`[^1] | `y.fdiv_num(x, z)`[^1] | `z.fdiv_den(x,y)` |
| Ceiling division | $x = \textnormal{cdiv}(y,z)$ | `x.cdiv(y, z)`[^1] | `y.cdiv_num(x, z)`[^1] | `z.cdiv_den(x,y)` |
| Truncated division | $x = \textnormal{tdiv}(y,z)$ | `x.tdiv(y, z)`[^1] | `y.tdiv_num(x, z)`[^1] | `z.tdiv_den(x,y)` |
| Euclidean division | $x = \textnormal{ediv}(y,z)$ | `x.ediv(y, z)`[^1] | `y.ediv_num(x, z)`[^1] | `z.ediv_den(x,y)` |
| Maximum | $x = \textnormal{max}(y, z)$ | `x.max(y, z)` | `y.max_back(x,z)` | `z.max_back(x,y)` |
| Minimum | $x = \textnormal{min}(y, z)$ | `x.min(y, z)` | `y.min_back(x,z)` | `z.min_back(x,y)` |
| Reified Equality | $x = (y = z)$ | `x.req(y, z)`[^2] | `y.req_back(x,z)`[^2] | `z.req_back(x,y)`[^2] |
| Reified Inequality | $x = (y \leq z)$ | `x.rleq(y, z)`[^2] | `y.rleq_lback(x,z)`[^2] | `z.rleq_rback(x,y)`[^2] |

#### Semantics of Division Operators

Let $\frac{.}{.}$ be the division over the real numbers, $\lfloor . \rfloor \in \mathbb{R} \to \mathbb{Z}$ be the function rounding downwards a real number, and $\lceil . \rceil \in \mathbb{R} \to \mathbb{Z}$ be the function rounding upwards a real number.

* **Semantics of floor division**
```math
x = \textnormal{fdiv}(y,z) \Leftrightarrow x = \lfloor \frac{y}{z} \rfloor
```
* **Semantics of ceiling division**
```math
x = \textnormal{cdiv}(y,z) \Leftrightarrow x = \lceil \frac{y}{z} \rceil
```
* **Semantics of truncated division**
```math
x = \textnormal{tdiv}(y,z) \Leftrightarrow
    x=\begin{cases}
        \lfloor\frac{y}{z}\rfloor&\text{if }\frac{y}{z}\geq 0\\
        \lceil\frac{y}{z}\rceil&\text{if }\frac{y}{z}< 0
    \end{cases}
```
* **Semantics of Euclidean division**
```math
x = \textnormal{ediv}(y,z) \Leftrightarrow
    x=\begin{cases}
        \lfloor\frac{y}{z}\rfloor&\text{if }z> 0\\
        \lceil\frac{y}{z}\rceil&\text{if }z< 0
    \end{cases}
```

[^1]: Precondition: the lower and upper bounds of the denominator `z` must be different from zero.
[^2]: Precondition: the domain of `x` must be included in `[0,1]`.

### FInterval: Abstract Operations

In the following, we let `x,y,z` be integer intervals of type `FInterval`.

| Operation  | Constraint | Forward operator | Left backward operator | Right backward operator |
| ------------- | ------------- | ------------- | ------------- | ------------- |
| Identity  | $x = y$ | `x.meet(y)`  | `y.meet(x)` | n/a |
| Negation  | $x = -y$ | `x.neg(y)`  | `y.neg(x)` | n/a |
| Addition  | $x = y + z$ | `x.add(y,z)`  | `y.sub(x,z)` | `z.sub(x,y)` |
| Subtraction  | $x = y - z$ | `x.sub(y,z)`  | `y.add(x,z)` | `z.sub(y,x)` |
| Multiplication | $x = y * z$ | `x.mul(y, z)` | `y.div(x,z)` | `z.div(x,y)` |
| Division | $x = y / z$ | `x.div(y, z)` | `y.mul(x, z)` | `z.div(y,x)` |
| Maximum | $x = \textnormal{max}(y, z)$ | `x.max(y, z)` | `y.max_b(x,z)` | `z.max_b(x,y)` |
| Minimum | $x = \textnormal{min}(y, z)$ | `x.min(y, z)` | `y.min_b(x,z)` | `z.min_b(x,y)` |

## Interval Bound Propagation

We have implemented various interval propagators for ternary arithmetic constraints of the form $x = y \odot z$ where $\odot$ is a binary operator.
The term "propagator" stems from constraint programming, it is also sometimes called _filtering function_.
In abstract interpretation, it is usually called _test_ in order to deal with conditional statement.

### Propagators on ZInterval

Let `x,y,z` be integer intervals of type `ZInterval`.

| Constraint | Propagator | Best? |
| ------------- | ------------- | ------------- |
| $x = y + z$ | `tell::zadd(x, y, z)` | Yes |
| $x = y - z$ | `tell::zsub(x, y, z)` | Yes |
| $x = y * z$ | `tell::zmul(x, y, z)` | No |
| $x = \textnormal{fdiv}(y, z)$ | `tell::fdiv(x, y, z)` | Yes[^3] |
| $x = \textnormal{cdiv}(y, z)$ | `tell::cdiv(x, y, z)` | Yes[^3] |
| $x = \textnormal{tdiv}(y, z)$ | `tell::tdiv(x, y, z)` | Yes[^3] |
| $x = \textnormal{ediv}(y, z)$ | `tell::ediv(x, y, z)` | Yes[^3] |
| $x = \textnormal{max}(y, z)$ | `tell::zmax(x, y, z)` | Yes |
| $x = \textnormal{min}(y, z)$ | `tell::zmin(x, y, z)` | Yes |
| $x = (y = z)$ | `tell::zreq(x, y, z)` | Yes |
| $x = (y \leq z)$ | `tell::zrleq(x, y, z)` | Yes |

[^3]: This is currently a conjecture from experimental results. Faster but less precise propagators, postfixed by `_fast` (e.g. `tell::fdiv_fast`) are also available: they do not perform a `splitjoin` operation on `z`.

### Entailment Test on ZInterval

Let `x,y,z` be integer intervals of type `ZInterval`.

| Constraint | Entailment test |
| ------------- | ------------- |
| $x = y + z$ | `ask::zadd(x, y, z)` |
| $x = y - z$ | `ask::zsub(x, y, z)` |
| $x = y * z$ | `ask::zmul(x, y, z)` |
| $x = \textnormal{fdiv}(y, z)$ | `ask::fdiv(x, y, z)` |
| $x = \textnormal{cdiv}(y, z)$ | `ask::cdiv(x, y, z)` |
| $x = \textnormal{tdiv}(y, z)$ | `ask::tdiv(x, y, z)` |
| $x = \textnormal{ediv}(y, z)$ | `ask::ediv(x, y, z)` |
| $x = \textnormal{max}(y, z)$ | `ask::zmax(x, y, z)` |
| $x = \textnormal{min}(y, z)$ | `ask::zmin(x, y, z)` |
| $x = (y = z)$ | `ask::zreq(x, y, z)` |
| $x = (y \leq z)$ | `ask::zrleq(x, y, z)` |

## Abstract Domain

An _abstract domain_ is an abstraction of a set of assignments $\mathcal{P}(X \to U)$ where $X$ is a set of variables and $U$ the universe of discourse.
It essentially extends the concept of abstract universe with variables.

### UStore Abstract Domain

The _universe store abstract domain_ `UStore` is an array of universes $X \to A$ where $X = \set{0, 1, \ldots, n}$ and $A$ is a parametric abstract universe.
In abstract interpretation, `UStore<ZInterval<int>>` is called the _interval abstract domain_ (can also be defined over `FInterval`).

Let `L` be a `UStore` abstract domain with any underlying abstract universe.

| Operation  | Mathematical notation | Programming notation |
| ------------- | ------------- | ------------- |
| Bottom  | $\bot$ | `L::bot()` |
| Top  | $\top$ | `L::top()` or default constructor `L()` |
| Partial order | $a \leq b$ | `a.leq(b)` |
| Strict partial order | $a < b$ | `a.lt(b)` |
| Meet | $a \sqcap b$ | `meet(a,b)` or `a.meet(b)` (in-place) |
| Join | $a \sqcup b$ | `join(a,b)` or `a.join(b)` (in-place) |

