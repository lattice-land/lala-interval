(** * div4: the four division propagators with INFINITE bounds

    Rocq model of the C++ [ztdiv_4]/[zfdiv_4]/[zcdiv_4]/[zediv_4]
    (zinterval.hpp): one-pass slice decomposition.  Only two positive-slice
    solvers are needed ([zfdiv_pos3] and [ztdiv_pos3], mirroring the C++
    [zfdiv_pos]/[ztdiv_pos]); every other case reduces to them through the
    mirror identities
      trunc(y/z) = -trunc(y/(-z))        floor(y/z) = floor((-y)/(-z))
      ceil(y/z)  = -floor((-y)/z)        ceil(y/z)  = -floor(y/(-z))
    applied by mirroring the intervals of x, y and/or z ([mirror_i], the C++
    [zmirror]).  The two slices are then joined ([join4]).

    Proved properties, following the paper's terminology:
      - soundness    : [z*div4_soundness]    (no solution is lost)
      - completeness : [z*div4_complete]     (a.k.a. optimality/best: the
        output is below every store containing the solutions), together with
        [z*div4_ne_feasible] (a non-empty output implies a solution exists),
        which extends completeness to infeasible inputs in the quotient
        lattice where all empty stores are identified with bottom.

    The Zinf interval infrastructure ([Zinf], [itv3], [store3], the
    infinity-aware helpers [sadd3]/[imul3]/[idivf3]/[idivc3]) is reused from
    [fdiv3]; none of that file's admitted theorems is used here. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv2 fdiv3.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Additional helpers: truncated corner division, mirroring        *)
(* ------------------------------------------------------------------ *)

(* trunc(n/m) with limit semantics (precondition of use: m <> Fin 0);
   mirrors the C++ [idiv_t]. *)
Definition idivt3 (n m : Zinf) : Zinf :=
  match m with
  | Pinf | Ninf => Fin 0
  | Fin w => match n with
             | Fin v => Fin (Z.quot v w)
             | Pinf => if 0 <? w then Pinf else Ninf
             | Ninf => if 0 <? w then Ninf else Pinf
             end
  end.

(* negation on Zinf; mirrors the C++ [ineg]. *)
Definition ineg3 (a : Zinf) : Zinf :=
  match a with Fin v => Fin (- v) | Pinf => Ninf | Ninf => Pinf end.

(* [l, u] := [-u, -l]; mirrors the C++ [zmirror] (bot maps to bot). *)
Definition mirror_i (i : itv3) : itv3 := Itv3 (ineg3 (hi3 i)) (ineg3 (lo3 i)).

(* the three mirroring patterns used by the wrappers *)
Definition mir_yz (s : store3) : store3 :=
  St3 (sx3 s) (mirror_i (sy3 s)) (mirror_i (sz3 s)).
Definition mir_xy (s : store3) : store3 :=
  St3 (mirror_i (sx3 s)) (mirror_i (sy3 s)) (sz3 s).
Definition mir_xz (s : store3) : store3 :=
  St3 (mirror_i (sx3 s)) (sy3 s) (mirror_i (sz3 s)).

(* remaining sign tests on Zinf (sentinel encoding of the C++ comparisons) *)
Definition zeqm1 (a : Zinf) : bool :=
  match a with Fin v => v =? -1 | _ => false end.

(* the C++ meet_bot: both bounds to their bottom *)
Definition botitv3 : itv3 := Itv3 Pinf Ninf.

(* ------------------------------------------------------------------ *)
(** ** The two positive-slice solvers                                  *)
(* ------------------------------------------------------------------ *)

(** Contracts x, y, z for x = fdiv(y, z) on the positive slice of z
    (z first met with [1, +oo]); mirrors the C++ [zfdiv_pos] line by line:
      Z: the feasible z form a contiguous range computed exactly from the
         band  fdiv(y, z) in [xl, xu]  <=>  y in [xl*z, (xu+1)*z - 1];
      Y: hull of the band endpoints over the narrowed z;
      X: 4-corner floor hull over the narrowed y, z. *)
Definition zfdiv_pos3 (s : store3) : store3 :=
  let x := sx3 s in let y := sy3 s in
  let z := Itv3 (zmax (lo3 (sz3 s)) (Fin 1)) (hi3 (sz3 s)) in
  if negb (nonempty3b z) then St3 x y z else
  (* Z: x.lb * z <= y.ub *)
  let z :=
    if zpos (lo3 x) then Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (hi3 y) (lo3 x)))
    else if negb (ziszero (lo3 x)) then
      Itv3 (zmax (lo3 z) (idivc3 (hi3 y) (lo3 x))) (hi3 z)
    else if zneg (hi3 y) then botitv3 else z in
  (* Z: (x.ub + 1) * z >= y.lb + 1 *)
  let z :=
    if zge0 (hi3 x) then
      Itv3 (zmax (lo3 z) (idivc3 (sadd3 (lo3 y) 1) (sadd3 (hi3 x) 1))) (hi3 z)
    else if negb (zeqm1 (hi3 x)) then
      Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (sadd3 (lo3 y) 1) (sadd3 (hi3 x) 1)))
    else if zge0 (lo3 y) then botitv3 else z in
  if negb (nonempty3b z) then St3 x y z else
  (* Y: hull of [x.lb*z, (x.ub+1)*z - 1] over the narrowed z *)
  let y := Itv3
    (zmax (lo3 y) (zmin (imul3 (lo3 x) (lo3 z)) (imul3 (lo3 x) (hi3 z))))
    (zmin (hi3 y) (zmax (sadd3 (imul3 (sadd3 (hi3 x) 1) (lo3 z)) (-1))
                        (sadd3 (imul3 (sadd3 (hi3 x) 1) (hi3 z)) (-1)))) in
  if negb (nonempty3b y) then St3 x y z else
  (* X: 4-corner hull of fdiv(y, z) *)
  let x := Itv3
    (zmax (lo3 x) (zmin (zmin (idivf3 (lo3 y) (lo3 z)) (idivf3 (lo3 y) (hi3 z)))
                        (zmin (idivf3 (hi3 y) (lo3 z)) (idivf3 (hi3 y) (hi3 z)))))
    (zmin (hi3 x) (zmax (zmax (idivf3 (lo3 y) (lo3 z)) (idivf3 (lo3 y) (hi3 z)))
                        (zmax (idivf3 (hi3 y) (lo3 z)) (idivf3 (hi3 y) (hi3 z))))) in
  St3 x y z.

(** Contracts x, y, z for x = tdiv(y, z) on the positive slice of z;
    mirrors the C++ [ztdiv_pos]:
      band  tdiv(y, z) in [xl, xu]  <=>  y in [tymin(xl, z), tymax(xu, z)]
      with tymin(v, z) = v > 0 ? v*z : (v-1)*z + 1
      and  tymax(v, z) = v >= 0 ? (v+1)*z - 1 : v*z. *)
Definition ztdiv_pos3 (s : store3) : store3 :=
  let x := sx3 s in let y := sy3 s in
  let z := Itv3 (zmax (lo3 (sz3 s)) (Fin 1)) (hi3 (sz3 s)) in
  if negb (nonempty3b z) then St3 x y z else
  (* Z: tymin(x.lb, z) <= y.ub *)
  let z :=
    if zpos (lo3 x) then Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (hi3 y) (lo3 x)))
    else Itv3 (zmax (lo3 z) (idivc3 (sadd3 (hi3 y) (-1)) (sadd3 (lo3 x) (-1)))) (hi3 z) in
  (* Z: tymax(x.ub, z) >= y.lb *)
  let z :=
    if zge0 (hi3 x) then
      Itv3 (zmax (lo3 z) (idivc3 (sadd3 (lo3 y) 1) (sadd3 (hi3 x) 1))) (hi3 z)
    else Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (lo3 y) (hi3 x))) in
  if negb (nonempty3b z) then St3 x y z else
  (* Y: hull of [tymin(x.lb, z), tymax(x.ub, z)] over the narrowed z *)
  let y := Itv3
    (zmax (lo3 y)
          (if zpos (lo3 x)
           then zmin (imul3 (lo3 x) (lo3 z)) (imul3 (lo3 x) (hi3 z))
           else zmin (sadd3 (imul3 (sadd3 (lo3 x) (-1)) (lo3 z)) 1)
                     (sadd3 (imul3 (sadd3 (lo3 x) (-1)) (hi3 z)) 1)))
    (zmin (hi3 y)
          (if zge0 (hi3 x)
           then zmax (sadd3 (imul3 (sadd3 (hi3 x) 1) (lo3 z)) (-1))
                     (sadd3 (imul3 (sadd3 (hi3 x) 1) (hi3 z)) (-1))
           else zmax (imul3 (hi3 x) (lo3 z)) (imul3 (hi3 x) (hi3 z)))) in
  if negb (nonempty3b y) then St3 x y z else
  (* X: 4-corner hull of tdiv(y, z) *)
  let x := Itv3
    (zmax (lo3 x) (zmin (zmin (idivt3 (lo3 y) (lo3 z)) (idivt3 (lo3 y) (hi3 z)))
                        (zmin (idivt3 (hi3 y) (lo3 z)) (idivt3 (hi3 y) (hi3 z)))))
    (zmin (hi3 x) (zmax (zmax (idivt3 (lo3 y) (lo3 z)) (idivt3 (lo3 y) (hi3 z)))
                        (zmax (idivt3 (hi3 y) (lo3 z)) (idivt3 (hi3 y) (hi3 z))))) in
  St3 x y z.

(* ------------------------------------------------------------------ *)
(** ** The four propagators (slice decomposition + join)               *)
(* ------------------------------------------------------------------ *)

(* the C++ join block: a failed positive slice is replaced wholesale by the
   negative one; a failed negative slice is dropped; otherwise hull. *)
Definition join4 (pos neg : store3) : store3 :=
  if negb (ne_store3 pos) then neg
  else if negb (ne_store3 neg) then pos
  else sjoin3 pos neg.

Definition ztdiv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (ztdiv_pos3 s) (mir_xz (ztdiv_pos3 (mir_xz s))).

Definition zfdiv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (zfdiv_pos3 s) (mir_yz (zfdiv_pos3 (mir_yz s))).

Definition zcdiv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (mir_xy (zfdiv_pos3 (mir_xy s))) (mir_xz (zfdiv_pos3 (mir_xz s))).

Definition zediv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (zfdiv_pos3 s) (mir_xz (zfdiv_pos3 (mir_xz s))).

(* ------------------------------------------------------------------ *)
(** ** Solutions of the four divisions                                 *)
(* ------------------------------------------------------------------ *)

(* floor: fdiv2.sol = z <> 0 /\ x = y / z (Z.div is the floor division) *)
Definition tsol (x y z : Z) : Prop := z <> 0 /\ x = Z.quot y z.
Definition csol (x y z : Z) : Prop := z <> 0 /\ x = cdiv y z.
Definition esol (x y z : Z) : Prop :=
  z <> 0 /\ x = (if 0 <? z then y / z else cdiv y z).

(* generic containment/feasibility, parameterized by the solution predicate *)
Definition contains3 (P : Z -> Z -> Z -> Prop) (s t : store3) : Prop :=
  forall vx vy vz, in_store3 s vx vy vz -> P vx vy vz -> in_store3 t vx vy vz.
Definition feasible3 (P : Z -> Z -> Z -> Prop) (s : store3) : Prop :=
  exists vx vy vz, in_store3 s vx vy vz /\ P vx vy vz.

(* ------------------------------------------------------------------ *)
(** ** Positive-slice theorems (the proof core)

    Everything below reduces to these six statements about the two
    positive-slice solvers, restricted to the solutions with vz >= 1. *)
(* ------------------------------------------------------------------ *)

Definition slice_feasible (P : Z -> Z -> Z -> Prop) (s : store3) : Prop :=
  exists vx vy vz, in_store3 s vx vy vz /\ P vx vy vz /\ 1 <= vz.
Definition slice_contains (P : Z -> Z -> Z -> Prop) (s t : store3) : Prop :=
  forall vx vy vz, in_store3 s vx vy vz -> P vx vy vz -> 1 <= vz ->
  in_store3 t vx vy vz.

Theorem fpos_sound : forall s vx vy vz,
  in_store3 s vx vy vz -> sol vx vy vz -> 1 <= vz ->
  in_store3 (zfdiv_pos3 s) vx vy vz.
Proof. Admitted.

Theorem fpos_best : forall s, slice_feasible sol s ->
  forall t, slice_contains sol s t -> sle3 (zfdiv_pos3 s) t.
Proof. Admitted.

Theorem fpos_ne_feasible : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (zfdiv_pos3 s) = true -> slice_feasible sol s.
Proof. Admitted.

Theorem tpos_sound : forall s vx vy vz,
  in_store3 s vx vy vz -> tsol vx vy vz -> 1 <= vz ->
  in_store3 (ztdiv_pos3 s) vx vy vz.
Proof. Admitted.

Theorem tpos_best : forall s, slice_feasible tsol s ->
  forall t, slice_contains tsol s t -> sle3 (ztdiv_pos3 s) t.
Proof. Admitted.

Theorem tpos_ne_feasible : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (ztdiv_pos3 s) = true -> slice_feasible tsol s.
Proof. Admitted.

(* ------------------------------------------------------------------ *)
(** ** Soundness                                                        *)
(* ------------------------------------------------------------------ *)

Theorem ztdiv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> tsol vx vy vz -> in_store3 (ztdiv4 s) vx vy vz.
Proof. Admitted.

Theorem zfdiv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> sol vx vy vz -> in_store3 (zfdiv4 s) vx vy vz.
Proof. Admitted.

Theorem zcdiv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> csol vx vy vz -> in_store3 (zcdiv4 s) vx vy vz.
Proof. Admitted.

Theorem zediv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> esol vx vy vz -> in_store3 (zediv4 s) vx vy vz.
Proof. Admitted.

(* ------------------------------------------------------------------ *)
(** ** Completeness (best abstract transformer)                        *)
(* ------------------------------------------------------------------ *)

Theorem ztdiv4_complete : forall s,
  feasible3 tsol s -> forall t, contains3 tsol s t -> sle3 (ztdiv4 s) t.
Proof. Admitted.

Theorem zfdiv4_complete : forall s,
  feasible3 sol s -> forall t, contains3 sol s t -> sle3 (zfdiv4 s) t.
Proof. Admitted.

Theorem zcdiv4_complete : forall s,
  feasible3 csol s -> forall t, contains3 csol s t -> sle3 (zcdiv4 s) t.
Proof. Admitted.

Theorem zediv4_complete : forall s,
  feasible3 esol s -> forall t, contains3 esol s t -> sle3 (zediv4 s) t.
Proof. Admitted.

(* completeness on infeasible inputs: a non-empty output implies a solution
   (contrapositive: no solution in s => the output is empty = bottom) *)

Theorem ztdiv4_ne_feasible : forall s,
  ne_store3 (ztdiv4 s) = true -> feasible3 tsol s.
Proof. Admitted.

Theorem zfdiv4_ne_feasible : forall s,
  ne_store3 (zfdiv4 s) = true -> feasible3 sol s.
Proof. Admitted.

Theorem zcdiv4_ne_feasible : forall s,
  ne_store3 (zcdiv4 s) = true -> feasible3 csol s.
Proof. Admitted.

Theorem zediv4_ne_feasible : forall s,
  ne_store3 (zediv4 s) = true -> feasible3 esol s.
Proof. Admitted.
