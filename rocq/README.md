# Rocq Mechanization of Integer Interval Bound Propagation

This mechanization was obtained with the help of Claude Opus 4.8.
We performed incrementally by manually inspecting the definitions.
We also edited deleted useless lemmas, renamed definitions and lemmas, grouped into distinct files.

## Concrete.v

The concrete domain is the set of solutions of a constraint network, that is, $\mathcal{P}(X \to \mathbb{Z})$ where $X$ is a set of variables.
The universe of discourse is $\mathbb{Z}$.
This file provides several definitions of functions over the universe of the discourse: addition, multiplication, floor division, ceiling division, truncated division and Euclidean division.
The goal of the mechanization is to prove the correctness of interval propagators over those functions.

It contains a few lemmas useful to derive bounds, notably when proving division and multiplication.

* `cdiv`: Ceiling division over integers, no extra prefix/suffix because it is the concrete operation over the universe of discourse.
* `*_rel`: Definitions of relation of constraints, e.g. `fdiv_rel` is the relation of the constraint $x = \floor{\frac{y}{z}}$, that is, all triples of values satisfying this constraint.

```coq
Definition cdiv (a b : Z) : Z := - ((- a) / b).
Definition fdiv_rel (x y z : Z) : Prop := z <> 0 /\ x =  y / z.
Definition cdiv_rel (x y z : Z) : Prop := z <> 0 /\ x = cdiv y z.
Definition ediv_rel (x y z : Z) : Prop := z <> 0 /\ x = (if 0 <? z then y / z else cdiv y z).
Definition tdiv_rel (x y z : Z) : Prop := z <> 0 /\ x = Z.quot y z.
```

## ZInf.v

The type `zinf` is the set of integers extended with positive and negative infinities, that is, $\mathbb{Z} \cup \{\infty,{-\infty}\}$.
All operations over the extended integers are suffixed by `_zinf`.

```coq
Inductive zinf : Type := Fin (v : Z) | Pinf | Ninf.
Definition leq_zinf (a b : zinf) : Prop.
Definition leqb_zinf (a b : zinf) : bool.
Definition min_zinf (a b : zinf) : zinf.
Definition max_zinf (a b : zinf) : zinf.
Definition addk_zinf (a : zinf) (k : Z) : zinf.
Definition mul_zinf (a b : zinf) : zinf.
Definition fdiv_zinf (n m : zinf) : zinf.
Definition cdiv_zinf (n m : zinf) : zinf.
Definition ispos_zinf (a : zinf) : bool.
...
```

## ZItv.v

Definition of Interval over `zinf`.

```coq
Record zitv := ZItv { lb : zinf ; ub : zinf }.
Definition in_zitv (i : zitv) (v : Z) : Prop.
Definition isbot_zitv (i : zitv) : bool.
Definition leq_zitv (i j : zitv) : Prop.
Definition meet_zitv (i j : zitv) : zitv.
Definition neg_zitv (i : zitv) : zitv.
...
```

## ZItv3.v

The type `zitv3` is the Cartesian product of three intervals `zitv`, sometimes referred to as _store_.

```coq
Record zitv3 := ZItv3 { x : zitv ; y : zitv ; z : zitv }.
Definition leq_zitv3 (a b : zitv3) : Prop.
Definition join_zitv3 (s t : zitv3) : zitv3.
Definition in_zitv3 (s : zitv3) (vx vy vz : Z) : Prop.
Definition is_not_bot_zitv3 (s : zitv3) : bool.
Definition join_nobot_zitv3 (s t : zitv3) : zitv3.
(*...*)
```
The next definition is at the core of soundness and completeness:

```coq
Definition preserve_solutions (P : Z -> Z -> Z -> Prop) (s t : zitv3) : Prop :=
  forall vx vy vz, in_zitv3 s vx vy vz -> P vx vy vz -> in_zitv3 t vx vy vz.
```

It states that given two stores `s` and `t`, typically `t <= s` and `t` is obtained after propagating `s`, the solutions that were in `s` are still in `t`.

## AddZItv3.v

This file in_zitv the definition of the propagator for the addition constraint `x = y + z` over `zitv3`.

```coq
Definition add_zitv3 (s : zitv3) : zitv3.
```

Properties of propagators are defined as follows:
```coq
Theorem add_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> vx = vy + vz ->
  in_zitv3 (add_zitv3 s) vx vy vz.

Theorem add_zitv3_singleton_complete : forall s vx vy vz,
  x s = ZItv (Fin vx) (Fin vx) ->
  y s = ZItv (Fin vy) (Fin vy) ->
  z s = ZItv (Fin vz) (Fin vz) ->
  is_not_bot_zitv3 (add_zitv3 s) = true ->
  vx = vy + vz.

Theorem add_zitv3_complete : forall s t,
  preserve_solutions add_rel s t -> leq_zitv3 (add_zitv3 s) t.
```

The fact `add_zitv3` is a closure operator is proven as a consequence of completeness.

```coq
Theorem add_zitv3_reductive : forall s, leq_zitv3 (add_zitv3 s) s.
Theorem add_zitv3_monotone : forall s t, leq_zitv3 s t -> leq_zitv3 (add_zitv3 s) (add_zitv3 t).
Theorem add_zitv3_idempotent : forall s,
  leq_zitv3 (add_zitv3 (add_zitv3 s)) (add_zitv3 s) /\ leq_zitv3 (add_zitv3 s) (add_zitv3 (add_zitv3 s)).
```

## DivZItv3.v

The following defines the propagators for the four divisions.
They rely on the specialized propagator `fdiv_pos_z_zitv3` for floor division when the denominator `z` is positive.

```coq
Definition fdiv_pos_z_zitv3 (s : zitv3) : zitv3.

Theorem fdiv_pos_z_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> fdiv_rel vx vy vz -> 1 <= vz ->
  in_zitv3 (fdiv_pos_z_zitv3 s) vx vy vz.

Theorem fdiv_pos_z_zitv3_completeness : forall s, slice_feasible fdiv_rel s ->
  forall t, slice_contains fdiv_rel s t -> leq_zitv3 (fdiv_pos_z_zitv3 s) t.
```

The propagators for the four division constraints are then defined.

The `*_not_bot_feasible` theorems state that whenever the result of propagation does not lead to bottom, then there is still a solution to the constraint within the bounds of the variables.


### Floor division

```coq
Definition fdiv_zitv3 (s : zitv3) : zitv3 :=
  if negb (is_not_bot_zitv3 s) then s
  else join_zitv3 (fdiv_pos_z_zitv3 s) (neg_yz_zitv3 (fdiv_pos_z_zitv3 (neg_yz_zitv3 s))).

Theorem fdiv_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> fdiv_rel vx vy vz -> in_zitv3 (fdiv_zitv3 s) vx vy vz.

Theorem fdiv_zitv3_not_bot_feasible : forall s,
  is_not_bot_zitv3 (fdiv_zitv3 s) = true -> feasible fdiv_rel s.

Theorem fdiv_zitv3_completeness : forall s t, preserve_solutions fdiv_rel s t -> leq_zitv3 (fdiv_zitv3 s) t.

Theorem fdiv_zitv3_reductive : forall s, leq_zitv3 (fdiv_zitv3 s) s.
Theorem fdiv_zitv3_monotone : forall s t, leq_zitv3 s t -> leq_zitv3 (fdiv_zitv3 s) (fdiv_zitv3 t).
Theorem fdiv_zitv3_idempotent : forall s,
  leq_zitv3 (fdiv_zitv3 (fdiv_zitv3 s)) (fdiv_zitv3 s) /\ leq_zitv3 (fdiv_zitv3 s) (fdiv_zitv3 (fdiv_zitv3 s)).
```

### Ceiling division

```coq
Definition cdiv_zitv3 (s : zitv3) : zitv3 :=
  if negb (is_not_bot_zitv3 s) then s
  else join_zitv3 (neg_xy_zitv3 (fdiv_pos_z_zitv3 (neg_xy_zitv3 s))) (neg_xz_zitv3 (fdiv_pos_z_zitv3 (neg_xz_zitv3 s))).

Theorem cdiv_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> cdiv_rel vx vy vz -> in_zitv3 (cdiv_zitv3 s) vx vy vz.

Lemma cdiv_zitv3_best_feasible : forall s,
  feasible cdiv_rel s -> forall t, preserve_solutions cdiv_rel s t -> leq_zitv3 (cdiv_zitv3 s) t.

Theorem cdiv_zitv3_not_bot_feasible : forall s,
  is_not_bot_zitv3 (cdiv_zitv3 s) = true -> feasible cdiv_rel s.

Theorem cdiv_zitv3_completeness : forall s t, preserve_solutions cdiv_rel s t -> leq_zitv3 (cdiv_zitv3 s) t.

Theorem cdiv_zitv3_reductive : forall s, leq_zitv3 (cdiv_zitv3 s) s.
Theorem cdiv_zitv3_monotone : forall s t, leq_zitv3 s t -> leq_zitv3 (cdiv_zitv3 s) (cdiv_zitv3 t).
Theorem cdiv_zitv3_idempotent : forall s,
  leq_zitv3 (cdiv_zitv3 (cdiv_zitv3 s)) (cdiv_zitv3 s) /\ leq_zitv3 (cdiv_zitv3 s) (cdiv_zitv3 (cdiv_zitv3 s)).
```

### Euclidean division

```coq
Definition ediv_zitv3 (s : zitv3) : zitv3 :=
  if negb (is_not_bot_zitv3 s) then s
  else join_zitv3 (fdiv_pos_z_zitv3 s) (neg_xz_zitv3 (fdiv_pos_z_zitv3 (neg_xz_zitv3 s))).

Theorem ediv_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> ediv_rel vx vy vz -> in_zitv3 (ediv_zitv3 s) vx vy vz.

Lemma ediv_zitv3_best_feasible : forall s,
  feasible ediv_rel s -> forall t, preserve_solutions ediv_rel s t -> leq_zitv3 (ediv_zitv3 s) t.

Theorem ediv_zitv3_not_bot_feasible : forall s,
  is_not_bot_zitv3 (ediv_zitv3 s) = true -> feasible ediv_rel s.

Theorem ediv_zitv3_completeness : forall s t, preserve_solutions ediv_rel s t -> leq_zitv3 (ediv_zitv3 s) t.

Theorem ediv_zitv3_reductive : forall s, leq_zitv3 (ediv_zitv3 s) s.
Theorem ediv_zitv3_monotone : forall s t, leq_zitv3 s t -> leq_zitv3 (ediv_zitv3 s) (ediv_zitv3 t).
Theorem ediv_zitv3_idempotent : forall s,
  leq_zitv3 (ediv_zitv3 (ediv_zitv3 s)) (ediv_zitv3 s) /\ leq_zitv3 (ediv_zitv3 s) (ediv_zitv3 (ediv_zitv3 s)).
```

### Truncated division

```coq
Definition tdiv_zitv3 (s : zitv3) : zitv3 :=
  if negb (is_not_bot_zitv3 s) then s
  else join_zitv3 (fdiv_pos_z_zitv3 (pos_y s))
       (join_zitv3 (neg_xz_zitv3 (fdiv_pos_z_zitv3 (neg_xz_zitv3 (pos_y s))))
       (join_zitv3 (neg_xy_zitv3 (fdiv_pos_z_zitv3 (neg_xy_zitv3 (neg_y s))))
                   (neg_yz_zitv3 (fdiv_pos_z_zitv3 (neg_yz_zitv3 (neg_y s)))))).

Theorem tdiv_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> tdiv_rel vx vy vz -> in_zitv3 (tdiv_zitv3 s) vx vy vz.

Theorem tdiv_zitv3_best_feasible : forall s,
  feasible tdiv_rel s -> forall t, preserve_solutions tdiv_rel s t -> leq_zitv3 (tdiv_zitv3 s) t.

Theorem tdiv_zitv3_not_bot_feasible : forall s,
  is_not_bot_zitv3 (tdiv_zitv3 s) = true -> feasible tdiv_rel s.

Theorem tdiv_zitv3_completeness : forall s t, preserve_solutions tdiv_rel s t -> leq_zitv3 (tdiv_zitv3 s) t.

Theorem tdiv_zitv3_reductive : forall s, leq_zitv3 (tdiv_zitv3 s) s.
Theorem tdiv_zitv3_monotone : forall s t, leq_zitv3 s t -> leq_zitv3 (tdiv_zitv3 s) (tdiv_zitv3 t).
Theorem tdiv_zitv3_idempotent : forall s, leq_zitv3 (tdiv_zitv3 (tdiv_zitv3 s)) (tdiv_zitv3 s) /\ leq_zitv3 (tdiv_zitv3 s) (tdiv_zitv3 (tdiv_zitv3 s)).

Theorem tdiv_zitv3_singleton_complete : forall s vx vy vz,
  x s = ZItv (Fin vx) (Fin vx) ->
  y s = ZItv (Fin vy) (Fin vy) ->
  z s = ZItv (Fin vz) (Fin vz) ->
  is_not_bot_zitv3 (tdiv_zitv3 s) = true -> tdiv_rel vx vy vz.
```

## MulZItv3.v

In comparison to addition and division, the multiplication propagator is not the strongest possible one.
We conjecture it is not possible to obtain a O(1) propagator in time and space to achieve bounds(Z) consistency for multiplication.

Multiplication is a function composition of three main components: update `x`, remove zero from `y` and `z` if needed, and update `y` and `z`.
The proof strategy is to prove each property separately on each component, including reductivity, monotonicity and soundness.
Those properties compose on functional compositional.

```coq
Definition mul_zitv3 (s : zitv3) : zitv3.

Theorem mul_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> vx = vy * vz ->
  in_zitv3 (mul_zitv3 s) vx vy vz.

Theorem mul_zitv3_reductive : forall s, leq_zitv3 (mul_zitv3 s) s.
Theorem mul_zitv3_monotone : forall s t, leq_zitv3 s t -> leq_zitv3 (mul_zitv3 s) (mul_zitv3 t).

Theorem mul_zitv3_singleton_complete : forall s vx vy vz,
  x s = ZItv (Fin vx) (Fin vx) ->
  y s = ZItv (Fin vy) (Fin vy) ->
  z s = ZItv (Fin vz) (Fin vz) ->
  is_not_bot_zitv3 (mul_zitv3 s) = true ->
  vx = vy * vz.
```

## Equivalence with C++ Implementation (equivcpp.v)

There are a few differences between the formalization given above and the C++ implementation.
We aim to bridge this gap in this part.

### Simplified truncated division

Similarly to floor division, it defines a specialized propagator for the case where $z > 0$:

```coq
Definition tdiv_pos_z_zitv3 (s : zitv3) : zitv3.

Theorem tdiv_pos_z_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> tdiv_rel vx vy vz -> 1 <= vz ->
  in_zitv3 (tdiv_pos_z_zitv3 s) vx vy vz.

Theorem tdiv_pos_z_zitv3_completeness : forall s, slice_feasible tdiv_rel s ->
  forall t, slice_contains tdiv_rel s t -> leq_zitv3 (tdiv_pos_z_zitv3 s) t.
```

This specialized propagator is then used to define the simplified truncated division.

```coq
Definition tdiv_simpl_zitv3 (s : zitv3) : zitv3 :=
  if negb (is_not_bot_zitv3 s) then s
  else join_zitv3 (tdiv_pos_z_zitv3 s) (neg_xz_zitv3 (tdiv_pos_z_zitv3 (neg_xz_zitv3 s))).

Theorem tdiv_simpl_zitv3_not_bot_feasible : forall s,
  is_not_bot_zitv (x s) = true -> is_not_bot_zitv (y s) = true ->
  is_not_bot_zitv3 (tdiv_pos_z_zitv3 s) = true -> slice_feasible tdiv_rel s.

Lemma tdiv_simpl_zitv3_best_feasible : forall s,
  feasible tdiv_rel s -> forall t, preserve_solutions tdiv_rel s t -> leq_zitv3 (tdiv_simpl_zitv3 s) t.

Theorem tdiv_simpl_zitv3_not_bot_feasible : forall s,
  is_not_bot_zitv3 (tdiv_simpl_zitv3 s) = true -> feasible tdiv_rel s.

Theorem tdiv_simpl_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> tdiv_rel vx vy vz -> in_zitv3 (tdiv_simpl_zitv3 s) vx vy vz.

Theorem tdiv_simpl_zitv3_completeness : forall s t, preserve_solutions tdiv_rel s t -> leq_zitv3 (tdiv_simpl_zitv3 s) t.
```

The proof of equivalence between both definitions of truncated division is given next.
```coq
Theorem tdiv_simpl_equiv_tdiv_zitv3: forall s, seq3 (tdiv_simpl_zitv3 s) (tdiv_zitv3 s).
```
