# Interval Reasoning

This library provides several abstract domains for interval reasoning over integer and real numbers.
We aim to be general enough to be reused across domains, here what is this library for in different domains:

* [Constraint programming](https://en.wikipedia.org/wiki/Constraint_programming): Enforce _bound(Z)_ and _bound(R)_ consistencies on interval domains (see e.g. [Choi et al. 2006](https://arxiv.org/pdf/cs/0412021)).
* [Abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation): Provide interval abstractions of integer and real numbers, including forward and backward interval arithmetics (see e.g. [Cousot, 2021](https://mitpress.mit.edu/9780262044905/principles-of-abstract-interpretation/)).
* [Conflict-free replicated data type](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type): Provide simple [anonymous state-based CRDTs](https://members.loria.fr/CIgnat/files/replication/Delta-CRDT.pdf) with `LB` and `UB`.
* [Asynchronous fixpoint iterations](https://web.mit.edu/dimitrib/www/pdc.html): Provide lock-free join and meet operations, compatible with execution on GPU hardware (see [Talbot et al., 2022](https://ojs.aaai.org/index.php/AAAI/article/view/20298)).

## Abstract Universes

We propose abstractions of the universe of discourse of integers $\mathbb{Z}$ and real numbers $\mathbb{R}$.
Let $\mathbb{I}$ be either $\mathbb{Z}$ or $\mathbb{R}$.
The following abstractions are approximating a subset of the universe of discourse.

* **Lower bound abstract universe**: `LB` approximates a set $S \subseteq \mathbb{I}$ by taking its lower bound $\mathit{min}~S$ if it is a bounded set, and $-\infty$ otherwise.
* **Upper bound abstract universe**: `UB` approximates a set $S \subseteq \mathbb{I}$ by taking its upper bound $\mathit{max}~S$ if it is a bounded set, and $\infty$ otherwise.
* **Integer interval abstract universe**: `ZInterval` approximates the lower and upper bounds of a set $S \subseteq \mathbb{Z}$.
* **Floating-point interval abstract universe**: `FInterval` approximates the lower and upper bounds of a set $S \subseteq \mathbb{R}$.

We represent infinities $\{-\infty, \infty\}$ using the minimum and maximum representable values on the underlying arithmetic type: for integers type `I` we rely on `std::numeric_limits<I>::min()` and `std::numeric_limits<I>::max()`, and for floating-point type `F` we rely on `-std::numeric_limits<F>::infinity()` and `std::numeric_limits<F>::infinity()`.

### ZInterval: Abstract Operations

Also known as _abstract transformers_ in the field of abstract interpretation.
In constraint programming, those operations can be used to design propagators, see below.

*Note*: To project the interval of an expression, e.g. `y + z`, initialize the result variable to top (e.g. `ZInterval<int> x;`) and call the forward operator on it: `x.add(y,z)`.

In the following, we let `x,y,z` be integer intervals of type `ZInterval`.

| Operation  | Constraint | Forward operator | Backward operator |
| ------------- | ------------- | ------------- | ------------- |
| Identity  | $x = y$ | `x.meet(y)`  | `y.meet(x)` |
| Negation  | $x = -y$ | `x.neg(y)`  | `y.neg(x)` |
| Addition  | $x = y + z$ | `x.add(y,z)`  | `y.sub(x,z)` and `z.sub(x,y)` |
| Subtraction  | $x = y - z$ | `x.sub(y,z)`  | `y.add(x,z)` and `z.add(x,y)` |
| Multiplication | $x = y * z$ | `x.mul(y, z)` | `y.mulb(x,z)` and `z.mulb(x,y)` |
| Floor division | $x = \textnormal{fdiv}(y,z)$ | `x.fdiv(y, z)`[^1] | `y.fdiv_num(x, z)`[^1] and `z.fdiv_den(x,y)` |
| Ceiling division | $x = \textnormal{cdiv}(y,z)$ | `x.cdiv(y, z)`[^1] | `y.cdiv_num(x, z)`[^1] and `z.cdiv_den(x,y)` |
| Truncated division | $x = \textnormal{tdiv}(y,z)$ | `x.tdiv(y, z)`[^1] | `y.tdiv_num(x, z)`[^1] and `z.tdiv_den(x,y)` |
| Euclidean division | $x = \textnormal{ediv}(y,z)$ | `x.ediv(y, z)`[^1] | `y.ediv_num(x, z)`[^1] and `z.ediv_den(x,y)` |
| Maximum | $x = \textnormal{max}(y, z)$ | `x.max(y, z)` | `y.maxb(x,z)` and `z.maxb(x,y)` |
| Minimum | $x = \textnormal{min}(y, z)$ | `x.min(y, z)` | `y.minb(x,z)` and `z.minb(x,y)` |

#### Semantics of Division Operators

Let $\frac{.}{.}$ be the division over the real numbers, $\lfloor . \rfloor \in \mathbb{R} \to \mathbb{Z}$ be the function rounding downwards a real number, and  $\lceil . \rceil \in \mathbb{R} \to \mathbb{Z}$ be the function rounding upwards a real number.

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
        \lceil\frac{y}{z}\rceil&\text{if }\frac{y}{z}< 0\\
    \end{cases}
```
* **Semantics of Euclidean division**
```math
x = \textnormal{ediv}(y,z) \Leftrightarrow
    x=\begin{cases}
        \lfloor\frac{y}{z}\rfloor&\text{if }z> 0\\
        \lceil\frac{y}{z}\rceil&\text{if }z< 0\\
    \end{cases}
```

[^1]: Precondition: the lower and upper bounds of the denominator `z` must be different from zero.

### FInterval: Abstract Operations

## Abstract Domain
