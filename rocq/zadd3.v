(** * zadd3: the addition propagator with INFINITE bounds

    Rocq model of the C++ [zadd3] (zinterval.hpp): x = y + z over Zinf
    intervals, refining x by the sum hull, then y and z by difference hulls
    (each using the already-refined companions), with no finiteness guard.

    The four defining propagator properties are proved:
      - soundness              : [zadd3_soundness]
      - reductivity            : [zadd3_reductive]
      - monotonicity           : [zadd3_monotone]   (unconditional: no join)
      - completeness/singleton : [zadd3_singleton_complete] *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv3.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Infinity-aware addition/subtraction (mirrors the C++ iadd/isub) *)
(* ------------------------------------------------------------------ *)

Definition iadd3 (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x + y)
  | Pinf, _ => Pinf
  | Ninf, _ => Ninf
  | _, Pinf => Pinf
  | _, Ninf => Ninf
  end.

Definition isub3 (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x - y)
  | Pinf, _ => Pinf
  | Ninf, _ => Ninf
  | _, Pinf => Ninf
  | _, Ninf => Pinf
  end.

(* ------------------------------------------------------------------ *)
(** ** The propagator (mirrors zadd3)                                  *)
(* ------------------------------------------------------------------ *)

Definition zadd3 (s : store3) : store3 :=
  let x := inter3 (sx3 s) (Itv3 (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))
                                (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s)))) in
  let y := inter3 (sy3 s) (Itv3 (isub3 (lo3 x) (hi3 (sz3 s)))
                                (isub3 (hi3 x) (lo3 (sz3 s)))) in
  let z := inter3 (sz3 s) (Itv3 (isub3 (lo3 x) (hi3 y))
                                (isub3 (hi3 x) (lo3 y))) in
  St3 x y z.

(* ------------------------------------------------------------------ *)
(** ** Order and arithmetic lemmas                                     *)
(* ------------------------------------------------------------------ *)

Lemma iadd3_ub : forall a b u v,
  zle a (Fin u) -> zle b (Fin v) -> zle (iadd3 a b) (Fin (u + v)).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma iadd3_lb : forall a b u v,
  zle (Fin u) a -> zle (Fin v) b -> zle (Fin (u + v)) (iadd3 a b).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma isub3_ub : forall a b u v,
  zle a (Fin u) -> zle (Fin v) b -> zle (isub3 a b) (Fin (u - v)).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma isub3_lb : forall a b u v,
  zle (Fin u) a -> zle b (Fin v) -> zle (Fin (u - v)) (isub3 a b).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma zle_refl3 : forall a, zle a a.
Proof. intros [x| |]; cbn; try easy; lia. Qed.

Lemma zle_zmax_l : forall a b, zle a (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma zle_zmin_l : forall a b, zle (zmin a b) a.
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma inter3_ile3_l : forall i j, ile3 (inter3 i j) i.
Proof. intros i j; split; cbn [lo3 hi3]; [apply zle_zmax_l | apply zle_zmin_l]. Qed.

Lemma mem3_inter : forall i j v, mem3 i v -> mem3 j v -> mem3 (inter3 i j) v.
Proof.
  intros [li ui] [lj uj] v [H1 H2] [H3 H4]; cbn in *; split; cbn.
  - destruct li as [x| |], lj as [y| |]; cbn in *; try easy; lia.
  - destruct ui as [x| |], uj as [y| |]; cbn in *; try easy; lia.
Qed.

Lemma zmax_mono : forall a b c d, zle a b -> zle c d -> zle (zmax a c) (zmax b d).
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma zmin_mono : forall a b c d, zle a b -> zle c d -> zle (zmin a c) (zmin b d).
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma inter3_mono : forall i i' j j',
  ile3 i i' -> ile3 j j' -> ile3 (inter3 i j) (inter3 i' j').
Proof.
  intros i i' j j' [H1 H2] [H3 H4]; split; cbn [lo3 hi3];
  [apply zmax_mono | apply zmin_mono]; assumption.
Qed.

Lemma iadd3_mono : forall a a' b b',
  zle a a' -> zle b b' -> zle (iadd3 a b) (iadd3 a' b').
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma isub3_mono : forall a a' b b',
  zle a a' -> zle b' b -> zle (isub3 a b) (isub3 a' b').
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem zadd3_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> vx = vy + vz ->
  in_store3 (zadd3 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Heq.
  destruct Hx as [Hx1 Hx2], Hy as [Hy1 Hy2], Hz as [Hz1 Hz2].
  unfold zadd3; cbv zeta.
  (* refined x contains vx *)
  assert (HXr : mem3 (inter3 (sx3 s) (Itv3 (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))
                                           (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s))))) vx).
  { apply mem3_inter; [split; assumption|]. split; cbn [lo3 hi3].
    - replace vx with (vy + vz) by lia. apply iadd3_ub; assumption.
    - replace vx with (vy + vz) by lia. apply iadd3_lb; assumption. }
  destruct HXr as [HX1 HX2].
  (* refined y contains vy *)
  assert (HYr : mem3 (inter3 (sy3 s)
     (Itv3 (isub3 (zmax (lo3 (sx3 s)) (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))) (hi3 (sz3 s)))
           (isub3 (zmin (hi3 (sx3 s)) (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s)))) (lo3 (sz3 s))))) vy).
  { apply mem3_inter; [split; assumption|]. split; cbn [lo3 hi3].
    - replace vy with (vx - vz) by lia. apply isub3_ub; assumption.
    - replace vy with (vx - vz) by lia. apply isub3_lb; assumption. }
  split; [|split].
  - split; assumption.
  - exact HYr.
  - destruct HYr as [HY1 HY2].
    apply mem3_inter; [split; assumption|]. split; cbn [lo3 hi3].
    + replace vz with (vx - vy) by lia. apply isub3_ub; assumption.
    + replace vz with (vx - vy) by lia. apply isub3_lb; assumption.
Qed.

Theorem zadd3_reductive : forall s, sle3 (zadd3 s) s.
Proof.
  intro s. unfold zadd3; cbv zeta. unfold sle3; cbn [sx3 sy3 sz3].
  split; [|split]; apply inter3_ile3_l.
Qed.

Theorem zadd3_monotone : forall s t,
  sle3 s t -> sle3 (zadd3 s) (zadd3 t).
Proof.
  intros s t (HX & HY & HZ).
  destruct HX as [HX1 HX2], HY as [HY1 HY2], HZ as [HZ1 HZ2].
  unfold zadd3; cbv zeta. unfold sle3; cbn [sx3 sy3 sz3].
  (* refined x is monotone *)
  assert (MX : ile3
    (inter3 (sx3 s) (Itv3 (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))
                          (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s)))))
    (inter3 (sx3 t) (Itv3 (iadd3 (lo3 (sy3 t)) (lo3 (sz3 t)))
                          (iadd3 (hi3 (sy3 t)) (hi3 (sz3 t)))))).
  { apply inter3_mono; [split; assumption|]. split; cbn [lo3 hi3].
    - apply iadd3_mono; assumption.
    - apply iadd3_mono; assumption. }
  destruct MX as [MX1 MX2].
  (* refined y is monotone *)
  assert (MY : ile3
    (inter3 (sy3 s) (Itv3 (isub3 (zmax (lo3 (sx3 s)) (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))) (hi3 (sz3 s)))
                          (isub3 (zmin (hi3 (sx3 s)) (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s)))) (lo3 (sz3 s)))))
    (inter3 (sy3 t) (Itv3 (isub3 (zmax (lo3 (sx3 t)) (iadd3 (lo3 (sy3 t)) (lo3 (sz3 t)))) (hi3 (sz3 t)))
                          (isub3 (zmin (hi3 (sx3 t)) (iadd3 (hi3 (sy3 t)) (hi3 (sz3 t)))) (lo3 (sz3 t)))))).
  { apply inter3_mono; [split; assumption|]. split; cbn [lo3 hi3].
    - apply isub3_mono; [exact MX1 | assumption].
    - apply isub3_mono; [exact MX2 | assumption]. }
  destruct MY as [MY1 MY2].
  split; [|split].
  - split; [exact MX1 | exact MX2].
  - split; [exact MY1 | exact MY2].
  - apply inter3_mono; [split; assumption|]. split; cbn [lo3 hi3].
    + apply isub3_mono; [exact MX1 | exact MY2].
    + apply isub3_mono; [exact MX2 | exact MY1].
Qed.

Theorem zadd3_singleton_complete : forall s vx vy vz,
  sx3 s = Itv3 (Fin vx) (Fin vx) ->
  sy3 s = Itv3 (Fin vy) (Fin vy) ->
  sz3 s = Itv3 (Fin vz) (Fin vz) ->
  ne_store3 (zadd3 s) = true ->
  vx = vy + vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold zadd3 in Hne; cbv zeta in Hne.
  rewrite Hx, Hy, Hz in Hne.
  unfold ne_store3 in Hne.
  apply Bool.andb_true_iff in Hne as [Hne _].
  apply Bool.andb_true_iff in Hne as [Hnex _].
  cbn in Hnex.
  apply Z.leb_le in Hnex. lia.
Qed.
