# Interval Reasoning

This library provides several abstract domains for interval reasoning over integer and real numbers.
We aim to be general enough to be reused across domains, here what is this library for in different domains:

* [Constraint programming](https://en.wikipedia.org/wiki/Constraint_programming): Enforce _bound(Z)_ and _bound(R)_ consistencies on interval domains (see e.g. [Choi et al. 2006](https://arxiv.org/pdf/cs/0412021)).
* [Abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation): Provide interval abstractions of integer and real numbers, including forward and backward interval arithmetics (see e.g. [Cousot, 2021](https://mitpress.mit.edu/9780262044905/principles-of-abstract-interpretation/)).
* [Conflict-free replicated data type](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type): Provide simple [anonymous state-based CRDTs](https://members.loria.fr/CIgnat/files/replication/Delta-CRDT.pdf) with `LB` and `UB`.
* [Asynchronous fixpoint iterations](https://web.mit.edu/dimitrib/www/pdc.html): Provide lock-free join and meet operations, compatible with execution on GPU hardware (see [Talbot et al., 2022](https://ojs.aaai.org/index.php/AAAI/article/view/20298)).

## Abstract Universes

We propose abstractions of the universe of discourse of integers $\mathbb{Z}$ and real numbers $\mathbb{R}$.
Let $\mathbb{A}$ be either $\mathbb{Z}$ or $\mathbb{R}$.
The following abstractions are approximating a subset of the universe of discourse.

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

### Extra Interval Quotient Lattice Operations

In this library, the bottom element of the interval abstract universe is $[\infty, -\infty]$ where infinities are represented as noted above (using `std::numeric_limits`).
In particular, we do not do anything special with empty intervals ($[\ell, u]$ where $\ell > u$) and the lattice operations are well-defined on those, e.g. $[1,0] \sqcap [0,10] = [\textnormal{max}(1,0), \textnormal{min}(0,10)] = [1, 0]$.
However, it is sometimes preferable to consider all empty intervals as a unique bottom element, in which case intervals are the set $\set{[\ell, u] \;|\; \ell \leq u} \cup \set{\bot}$ in which $\bot$ is a special element.
This is the typical implementation in abstract interpretation.

This library gives users both options: considering $[\infty, -\infty]$ as the only bottom element, or viewing all empty intervals as an equivalence class equal to $\bot$.
The first is given by the "standard" lattice operations described above.
The second is given by the "quotient" lattice operations described in the following table (prefixed by "q").

| Operation  | Mathematical definition | Programming notation |
| ------------- | ------------- | ------------- |
| Quotient bottom test  | $\textnormal{isqbot}([\ell, u]) \triangleq \ell > u \lor \ell = \infty \lor u = -\infty$ | `a.is_qbot()` |
| Quotient partial order | $a \leq b \lor (\textnormal{isqbot}(a) \land \textnormal{isqbot}(b))$ | `a.qleq(b)` |
| Strict quotient partial order | $a < b \land \textnormal{isqbot}(a) \neq \textnormal{isqbot}(b)$ | `a.qlt(b)` |
| Quotient Join | $\textnormal{qjoin}(a,b)$ | `qjoin(a,b)` or `a.qjoin(b)` (in-place) |
| Quotient Equality | $a = b \lor (\textnormal{isqbot}(a) \land \textnormal{isqbot}(b))$ | `a.qeq(b)` |

With the quotient join defined as:
```math
  \textnormal{qjoin}(x, y) \triangleq
    \begin{cases}
        \bot &\text{if } \textnormal{isqbot}(x) \land \textnormal{isqbot}(y) \\
        y &\text{if } \textnormal{isqbot}(x) \\
        x &\text{if } \textnormal{isqbot}(y) \\
        x \sqcup y & \text{otherwise }
    \end{cases}
```

### ZInterval: Abstract Operations

Also known as _abstract transformers_ in the field of abstract interpretation.
In constraint programming, those operations can be used to design propagators, see below.

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

### FInterval: Abstract Operations

In the following, we let `x,y,z` be integer intervals of type `FInterval`.

| Operation  | Constraint | Forward operator | Backward operator |
| ------------- | ------------- | ------------- | ------------- |
| Identity  | $x = y$ | `x.meet(y)`  | `y.meet(x)` |
| Negation  | $x = -y$ | `x.neg(y)`  | `y.neg(x)` |
| Addition  | $x = y + z$ | `x.add(y,z)`  | `y.sub(x,z)` and `z.sub(x,y)` |
| Subtraction  | $x = y - z$ | `x.sub(y,z)`  | `y.add(x,z)` and `z.sub(y,x)` |
| Multiplication | $x = y * z$ | `x.mul(y, z)` | `y.div(x,z)` and `z.div(x,y)` |
| Division | $x = y / z$ | `x.div(y, z)` | `y.mul(x, z)` and `z.div(y,x)` |
| Maximum | $x = \textnormal{max}(y, z)$ | `x.max(y, z)` | `y.max_b(x,z)` and `z.max_b(x,y)` |
| Minimum | $x = \textnormal{min}(y, z)$ | `x.min(y, z)` | `y.min_b(x,z)` and `z.min_b(x,y)` |

## Interval Bound Propagation

We have implemented various interval propagators for ternary arithmetic constraints of the form $x = y \odot z$ where $\odot$ is a binary operator.
The terminology of propagators stems from constraint programming, it is also sometimes called _filtering function_.
In abstract interpretation, it is called _test_ in order to deal with conditional statement.

| Constraint | Propagator | Best? |
| ------------- | ------------- | ------------- |
| $x = y + z$ | `tell::zadd(x, y, z)` | Yes |
| $x = y - z$ | `tell::zsub(x, y, z)` | Yes |
| $x = y * z$ | `tell::zmul(x, y, z)` | No |
| $x = \textnormal{fdiv}(y, z)$ | `tell::fdiv(x, y, z)` | No |
| $x = \textnormal{cdiv}(y, z)$ | `tell::cdiv(x, y, z)` | No |
| $x = \textnormal{tdiv}(y, z)$ | `tell::tdiv(x, y, z)` | No |
| $x = \textnormal{ediv}(y, z)$ | `tell::ediv(x, y, z)` | No |
| $x = \textnormal{max}(y, z)$ | `tell::max(x, y, z)` | Yes |
| $x = \textnormal{min}(y, z)$ | `tell::min(x, y, z)` | Yes |
| $x = (y = z)$ | `tell::req(x, y, z)` | Yes |
| $x = (y \leq z)$ | `tell::rleq(x, y, z)` | Yes |

## Entailment Test

| Constraint | Entailment test |
| ------------- | ------------- |
| $x = y + z$ | `ask::zadd(x, y, z)` |
| $x = y - z$ | `ask::zsub(x, y, z)` |
| $x = y * z$ | `ask::zmul(x, y, z)` |
| $x = \textnormal{fdiv}(y, z)$ | `ask::fdiv(x, y, z)` |
| $x = \textnormal{cdiv}(y, z)$ | `ask::cdiv(x, y, z)` |
| $x = \textnormal{tdiv}(y, z)$ | `ask::tdiv(x, y, z)` |
| $x = \textnormal{ediv}(y, z)$ | `ask::ediv(x, y, z)` |
| $x = \textnormal{max}(y, z)$ | `ask::max(x, y, z)` |
| $x = \textnormal{min}(y, z)$ | `ask::min(x, y, z)` |
| $x = (y = z)$ | `ask::req(x, y, z)` |
| $x = (y \leq z)$ | `ask::rleq(x, y, z)` |

## Interval Abstract Domain

## Abstract Domain
