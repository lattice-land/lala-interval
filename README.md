# Interval Abstract Domain

This library provides several abstract domains for interval reasoning over integer and real numbers.
We aim to be general enough to be reused across domains, here what is this library for in different domains:

* [Constraint programming](https://en.wikipedia.org/wiki/Constraint_programming): Enforce _bound(Z)_ and _bound(R)_ consistencies on interval domains (see e.g. [Choi et al. 2006](https://arxiv.org/pdf/cs/0412021)).
* [Abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation): Provide interval abstractions of integer and real numbers, including forward and backward interval arithmetics (see e.g. [Cousot, 2021](https://mitpress.mit.edu/9780262044905/principles-of-abstract-interpretation/)).
* [Conflict-free replicated data type](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type): Provide simple [anonymous state-based CRDTs](https://members.loria.fr/CIgnat/files/replication/Delta-CRDT.pdf) with `LB` and `UB`.
* [Asynchronous fixpoint iterations](https://web.mit.edu/dimitrib/www/pdc.html): Provide lock-free join and meet operations, compatible with execution on GPU hardware (see [Talbot et al., 2022](https://ojs.aaai.org/index.php/AAAI/article/view/20298)).

## Operations Supported

If you want to project the interval of an expression, e.g. `y + z`, initialize the result variable `Interval r;` and call the forward operator on it `r.add(y,z)`.

| Operation  | Constraint | Forward operator | Backward operator |
| ------------- | ------------- | ------------- | ------------- |
| Negation  | x = -y | `x.neg(y)`  | `y.neg(x)` |
| Addition  | x = y + z | `x.add(y,z)`  | `y.sub(x,z)` and `z.sub(x,y)` |
| Subtraction  | x = y - z | `x.sub(y,z)`  | `y.add(x,z)` and `z.add(x,y)` |

TBC
