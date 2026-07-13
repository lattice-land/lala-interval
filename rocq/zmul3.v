(** * zmul3: the multiplication propagator with INFINITE bounds

    Rocq model of the C++ [zmul3] (zinterval.hpp): x = y * z over Zinf
    intervals.  Constant-time structure: 4-corner product hull, zero-shaving
    of the factors when 0 is not in x, division-back by the cdiv/fdiv corner
    hull when the co-factor is sign-definite (on solutions y = x / z exactly),
    and the absolute-value bound |factor| <= |x| when it straddles zero.

    The four defining propagator properties:
      - soundness              : [zmul3_soundness]
      - reductivity            : [zmul3_reductive]
      - monotonicity           : [zmul3_monotone]  (up to bottom)
      - completeness/singleton : [zmul3_singleton_complete] *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv3 zadd3.
From LalaInterval Require fdiv2.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Auxiliary operations (mirror the C++)                           *)
(* ------------------------------------------------------------------ *)

Definition zneg3 (a : Zinf) : Zinf :=
  match a with Fin v => Fin (- v) | Pinf => Ninf | Ninf => Pinf end.

(* neq_zero: shave a zero bound *)
Definition neqz3 (i : itv3) : itv3 :=
  Itv3 (if ziszero (lo3 i) then Fin 1 else lo3 i)
       (if ziszero (hi3 i) then Fin (-1) else hi3 i).

(* 4-corner product hull *)
Definition mul_hull3 (iy iz : itv3) : itv3 :=
  Itv3 (zmin (zmin (imul3 (lo3 iy) (lo3 iz)) (imul3 (lo3 iy) (hi3 iz)))
             (zmin (imul3 (hi3 iy) (lo3 iz)) (imul3 (hi3 iy) (hi3 iz))))
       (zmax (zmax (imul3 (lo3 iy) (lo3 iz)) (imul3 (lo3 iy) (hi3 iz)))
             (zmax (imul3 (hi3 iy) (lo3 iz)) (imul3 (hi3 iy) (hi3 iz)))).

(* division-back corner hull (sound for EXACT quotients: y = x / z on
   solutions); only used on sign-definite ib *)
Definition div_back3 (ix ib : itv3) : itv3 :=
  Itv3 (zmin (zmin (idivc3 (lo3 ix) (lo3 ib)) (idivc3 (lo3 ix) (hi3 ib)))
             (zmin (idivc3 (hi3 ix) (lo3 ib)) (idivc3 (hi3 ix) (hi3 ib))))
       (zmax (zmax (idivf3 (lo3 ix) (lo3 ib)) (idivf3 (lo3 ix) (hi3 ib)))
             (zmax (idivf3 (hi3 ix) (lo3 ib)) (idivf3 (hi3 ix) (hi3 ib)))).

(* |target| <= |x| window (used when the co-factor straddles 0 but 0 notin x,
   so the co-factor is a non-zero integer: |b| >= 1) *)
Definition absb3 (ix : itv3) : itv3 :=
  Itv3 (zmin (lo3 ix) (zneg3 (hi3 ix))) (zmax (zneg3 (lo3 ix)) (hi3 ix)).

Definition sgndefb (i : itv3) : bool := (zpos (lo3 i) || zneg (hi3 i))%bool.
Definition xnzb (i : itv3) : bool := sgndefb i.

(* ------------------------------------------------------------------ *)
(** ** The propagator (mirrors zmul3)                                  *)
(* ------------------------------------------------------------------ *)

Definition zmul3 (s : store3) : store3 :=
  (* MUL *)
  let x := inter3 (sx3 s) (mul_hull3 (sy3 s) (sz3 s)) in
  let xnz := xnzb x in
  (* z.mul_back_zero(x) *)
  let z0 := if xnz then neqz3 (sz3 s) else sz3 s in
  (* y.mul_back_nz(x, z) *)
  let y0 := if sgndefb z0 then inter3 (sy3 s) (div_back3 x z0)
            else if xnz then inter3 (sy3 s) (absb3 x)
            else sy3 s in
  (* y.mul_back_zero(x) *)
  let y1 := if xnz then neqz3 y0 else y0 in
  (* z.mul_back_nz(x, y) *)
  let z1 := if sgndefb y1 then inter3 z0 (div_back3 x y1)
            else if xnz then inter3 z0 (absb3 x)
            else z0 in
  (* MUL *)
  let x2 := inter3 x (mul_hull3 y1 z1) in
  St3 x2 y1 z1.

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem zmul3_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> vx = vy * vz ->
  in_store3 (zmul3 s) vx vy vz.
Proof. Admitted.

(* the zero-shave only moves bounds inward *)
Lemma neqz3_ile3 : forall i, ile3 (neqz3 i) i.
Proof.
  intros [l u]; split; cbn [lo3 hi3].
  - destruct l as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
  - destruct u as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
Qed.

Theorem zmul3_reductive : forall s, sle3 (zmul3 s) s.
Proof.
  intro s. unfold zmul3; cbv zeta. unfold sle3; cbn [sx3 sy3 sz3].
  repeat (match goal with |- context[if ?b then _ else _] => destruct b end).
  all: split; [|split].
  all: repeat (first [ apply ile3_refl
                | apply neqz3_ile3
                | apply inter3_ile3_l
                | eapply ile3_trans; [apply neqz3_ile3|]
                | eapply ile3_trans; [apply inter3_ile3_l|] ]).
Qed.

Theorem zmul3_monotone : forall s t,
  sle3 s t ->
  ne_store3 (zmul3 s) = true ->
  sle3 (zmul3 s) (zmul3 t).
Proof. Admitted.

Theorem zmul3_singleton_complete : forall s vx vy vz,
  sx3 s = Itv3 (Fin vx) (Fin vx) ->
  sy3 s = Itv3 (Fin vy) (Fin vy) ->
  sz3 s = Itv3 (Fin vz) (Fin vz) ->
  ne_store3 (zmul3 s) = true ->
  vx = vy * vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold zmul3 in Hne; cbv zeta in Hne.
  rewrite Hx, Hy, Hz in Hne.
  unfold ne_store3 in Hne.
  apply Bool.andb_true_iff in Hne as [Hne _].
  apply Bool.andb_true_iff in Hne as [Hnex _].
  (* the x-component is nested inter3s of the singleton hull *)
  apply ne_inter3 in Hnex.
  cbn in Hnex. apply Z.leb_le in Hnex. lia.
Qed.
