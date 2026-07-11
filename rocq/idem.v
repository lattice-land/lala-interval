(** * Idempotency of the floored-division propagator

    Building on [fdiv.v] (soundness).  Goal: the propagator reaches a fixpoint
    in one pass, i.e. [propagator (propagator s) = propagator s] on consistent
    (non-empty) results.

    We build bottom-up.  This file is WORK IN PROGRESS: it collects the
    verified building blocks toward the full idempotency theorem. *)

From Stdlib Require Import ZArith Lia.
From LalaInterval Require Import fdiv.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Interval algebra facts                                          *)
(* ------------------------------------------------------------------ *)

(** [inter] is idempotent when re-meeting with the same interval. *)
Lemma inter_reidem : forall i j, inter (inter i j) j = inter i j.
Proof.
  intros [il ih] [jl jh]. unfold inter; cbn [lo hi]. f_equal; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [refine_y] is idempotent                                        *)
(* ------------------------------------------------------------------ *)

Lemma refine_y_idem : forall s, refine_y (refine_y s) = refine_y s.
Proof.
  intros s. unfold refine_y; cbn [sx sy sz].
  f_equal. apply inter_reidem.
Qed.

Lemma ijoin_id : forall i, ijoin i i = i.
Proof. intros [il ih]; unfold ijoin; cbn [lo hi]; f_equal; lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** The branch/join stage [J] and its [y]-component                 *)
(* ------------------------------------------------------------------ *)

Definition J (s : store) : store :=
  sqcupbot (fdivxz_neg (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)).

Lemma propagator_J : forall s, propagator s = refine_y (J s).
Proof. intro s. unfold propagator, J. reflexivity. Qed.

Lemma sy_restrict_pos : forall s, sy (restrict_z_pos s) = sy s.
Proof. intro s. unfold restrict_z_pos. reflexivity. Qed.
Lemma sy_restrict_neg : forall s, sy (restrict_z_neg s) = sy s.
Proof. intro s. unfold restrict_z_neg. reflexivity. Qed.
Lemma sy_fdivxz_pos : forall w, sy (fdivxz_pos w) = sy w.
Proof. intro w. unfold fdivxz_pos; cbv zeta; cbn [sy]. reflexivity. Qed.
Lemma sy_fdivxz_neg : forall w, sy (fdivxz_neg w) = sy w.
Proof. intro w. unfold fdivxz_neg; cbv zeta; cbn [sy]. reflexivity. Qed.

(** [J] leaves the [y] component untouched. *)
Lemma J_sy : forall s, sy (J s) = sy s.
Proof.
  intro s. unfold J, sqcupbot.
  destruct (ne_store (fdivxz_neg (restrict_z_neg s))) eqn:E1;
  destruct (ne_store (fdivxz_pos (restrict_z_pos s))) eqn:E2; cbn [sy].
  - unfold sjoin; cbn [sy].
    rewrite sy_fdivxz_neg, sy_restrict_neg, sy_fdivxz_pos, sy_restrict_pos.
    apply ijoin_id.
  - rewrite sy_fdivxz_neg, sy_restrict_neg. reflexivity.
  - rewrite sy_fdivxz_pos, sy_restrict_pos. reflexivity.
  - rewrite sy_fdivxz_pos, sy_restrict_pos. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reductivity: the propagator only narrows (a Def.1 property, and *)
(*     one inclusion of the idempotency fixpoint).                      *)
(* ------------------------------------------------------------------ *)

Definition ile (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.   (* i subset of j *)
Definition sle (a b : store) : Prop :=
  ile (sx a) (sx b) /\ ile (sy a) (sy b) /\ ile (sz a) (sz b).

Lemma ile_refl : forall i, ile i i.
Proof. intro i; unfold ile; lia. Qed.
Lemma ile_trans : forall i j k, ile i j -> ile j k -> ile i k.
Proof. unfold ile; intros i j k [??] [??]; lia. Qed.
Lemma inter_ile_l : forall i j, ile (inter i j) i.
Proof. intros i j; unfold ile, inter; cbn [lo hi]; lia. Qed.
Lemma ijoin_ile : forall i j k, ile i k -> ile j k -> ile (ijoin i j) k.
Proof. unfold ile, ijoin; cbn [lo hi]; intros i j k [??] [??]; lia. Qed.
Lemma sle_trans : forall a b c, sle a b -> sle b c -> sle a c.
Proof.
  unfold sle; intros a b c [Hx [Hy Hz]] [Hx' [Hy' Hz']];
  split; [|split]; eapply ile_trans; eassumption.
Qed.
Lemma ile_antisym : forall i j, ile i j -> ile j i -> i = j.
Proof. intros [il ih] [jl jh]; unfold ile; cbn [lo hi]; intros [??] [??]; f_equal; lia. Qed.
Lemma sle_antisym : forall a b, sle a b -> sle b a -> a = b.
Proof.
  intros [ax ay az] [bx byv bz]; unfold sle; cbn [sx sy sz];
  intros [Hx [Hy Hz]] [Hx' [Hy' Hz']].
  f_equal; apply ile_antisym; assumption.
Qed.

Lemma restrict_z_pos_ile : forall t, sle (restrict_z_pos t) t.
Proof.
  intro t; unfold restrict_z_pos, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply ile_refl | apply inter_ile_l]].
Qed.
Lemma restrict_z_neg_ile : forall t, sle (restrict_z_neg t) t.
Proof.
  intro t; unfold restrict_z_neg, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply ile_refl | apply inter_ile_l]].
Qed.
Lemma fdivxz_pos_ile : forall w, sle (fdivxz_pos w) w.
Proof.
  intro w. unfold fdivxz_pos; cbv zeta; unfold sle; cbn [sx sy sz].
  split; [ eapply ile_trans; apply inter_ile_l
         | split; [apply ile_refl | apply inter_ile_l] ].
Qed.
Lemma fdivxz_neg_ile : forall w, sle (fdivxz_neg w) w.
Proof.
  intro w. unfold fdivxz_neg; cbv zeta; unfold sle; cbn [sx sy sz].
  split; [ eapply ile_trans; apply inter_ile_l
         | split; [apply ile_refl | apply inter_ile_l] ].
Qed.
Lemma refine_y_ile : forall w, sle (refine_y w) w.
Proof.
  intro w; unfold refine_y, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply inter_ile_l | apply ile_refl]].
Qed.
Lemma sqcupbot_ile : forall a b t, sle a t -> sle b t -> sle (sqcupbot a b) t.
Proof.
  intros a b t Ha Hb. unfold sqcupbot.
  destruct (ne_store a), (ne_store b); cbn iota; try assumption.
  unfold sjoin, sle in *; cbn [sx sy sz].
  destruct Ha as [Hax [Hay Haz]]; destruct Hb as [Hbx [Hby Hbz]].
  split; [|split]; apply ijoin_ile; assumption.
Qed.
Lemma J_ile : forall t, sle (J t) t.
Proof.
  intro t. unfold J. apply sqcupbot_ile.
  - eapply sle_trans; [apply fdivxz_neg_ile | apply restrict_z_neg_ile].
  - eapply sle_trans; [apply fdivxz_pos_ile | apply restrict_z_pos_ile].
Qed.

(** The propagator is reductive. *)
Theorem propagator_reductive : forall s, sle (propagator s) s.
Proof.
  intro s. rewrite propagator_J.
  eapply sle_trans; [apply refine_y_ile | apply J_ile].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reduction: idempotency follows from the two "crux" equalities   *)
(*     that re-running [J] on the output reproduces its x and z.       *)
(* ------------------------------------------------------------------ *)

Lemma idem_from_crux : forall s,
  sx (J (refine_y (J s))) = sx (J s) ->
  sz (J (refine_y (J s))) = sz (J s) ->
  propagator (propagator s) = propagator s.
Proof.
  intros s Hx Hz.
  rewrite !propagator_J.
  set (u := J s) in *.
  (* Goal: refine_y (J (refine_y u)) = refine_y u *)
  assert (Hy : sy (J (refine_y u)) = inter (sy u)
                 (Itv (Ylo (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u)))
                      (Yhi (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u))))).
  { rewrite J_sy. unfold refine_y; cbn [sy]. reflexivity. }
  unfold refine_y at 1 3.
  rewrite Hx, Hz, Hy.
  f_equal. apply inter_reidem.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The remaining obligation (crux)                                 *)
(*                                                                     *)
(*  Re-running the branch/join stage [J] on the propagator's output    *)
(*  reproduces its x and z components.  This is a FIXPOINT / self-      *)
(*  consistency property of the composed interval operators -- after   *)
(*  [fnum] narrows y, the narrower y still divides back onto x         *)
(*  ([fdiv (fnum x z) z] contains x), and likewise [fden] is stable.    *)
(*  It is an algebraic identity on the bound formulas; it does NOT      *)
(*  refer to the concrete solution set, so it is *not* an optimality    *)
(*  (bound-consistency) statement -- idempotency is strictly weaker     *)
(*  than optimality (optimality would imply it, not conversely).        *)
(* ------------------------------------------------------------------ *)

(** A store is consistent when no component is an empty interval.  Exhaustive
    [vm_compute] over [-3..3]^6 (21952 stores) shows:
      - "idempotent OR both-bottom" holds for ALL stores (0 failures);
      - unconditional exact idempotency FAILS on 338 (empty) stores;
      - exact idempotency holds for EVERY store whose OUTPUT is consistent.
    Hence the correct statement conditions on consistency of the output. *)
Definition consistent (s : store) : Prop :=
  lo (sx s) <= hi (sx s) /\ lo (sy s) <= hi (sy s) /\ lo (sz s) <= hi (sz s).

(** The remaining crux, now a single inclusion: on a consistent output the
    branch/join stage [J] does not narrow (the expansive/fixpoint direction;
    the reductive direction [J_ile] is proved).  This is the pure fden/fdiv
    stability content. *)
(** The hard content, split by component.  The y-component is free ([J_sy]);
    [Jexp_x]/[Jexp_z] are the DIV/DEN stability inclusions (fden/fdiv do not
    narrow the output). *)
Lemma Jexp_x : forall s,
  consistent (propagator s) -> ile (sx (propagator s)) (sx (J (propagator s))).
Proof. Admitted.
Lemma Jexp_z : forall s,
  consistent (propagator s) -> ile (sz (propagator s)) (sz (J (propagator s))).
Proof. Admitted.

Lemma J_expansive : forall s,
  consistent (propagator s) -> sle (propagator s) (J (propagator s)).
Proof.
  intros s Hc. unfold sle.
  split; [ apply Jexp_x; exact Hc | ].
  split; [ | apply Jexp_z; exact Hc ].
  rewrite J_sy. apply ile_refl.
Qed.

(** Crux: on a consistent output, [J] is a fixpoint -- by antisymmetry from
    reductivity ([J_ile]) and non-narrowing ([J_expansive]). *)
Lemma J_fix : forall s, consistent (propagator s) -> J (propagator s) = propagator s.
Proof.
  intros s Hc. apply sle_antisym; [ apply J_ile | apply J_expansive; exact Hc ].
Qed.

(** Idempotency of the propagator on consistent outputs (modulo [J_fix]). *)
Theorem propagator_idem : forall s,
  consistent (propagator s) -> propagator (propagator s) = propagator s.
Proof.
  intros s Hc.
  rewrite (propagator_J (propagator s)), (J_fix s Hc), (propagator_J s).
  apply refine_y_idem.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Rigorous bounded idempotency (admit-free, by reflection)        *)
(*                                                                     *)
(*  A complete [vm_compute] proof that on every store in the           *)
(*  [-3..3]^6 grid (21952 stores), if the output is consistent then    *)
(*  the propagator is idempotent -- exactly the bounded instance of    *)
(*  [propagator_idem], with NO axioms.                                 *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import List. Import ListNotations.

Definition rng : list Z := (-3 :: -2 :: -1 :: 0 :: 1 :: 2 :: 3 :: nil)%Z.
Definition itvs : list itv :=
  flat_map (fun a => map (fun b => Itv a b) (filter (fun b => a <=? b) rng)) rng.
Definition ieqb (i j : itv) : bool := andb (lo i =? lo j) (hi i =? hi j).
Definition seqb (u v : store) : bool :=
  andb (andb (ieqb (sx u) (sx v)) (ieqb (sy u) (sy v))) (ieqb (sz u) (sz v)).
Definition bott (i : itv) : bool := hi i <? lo i.
Definition consistent_b (s : store) : bool :=
  andb (andb (negb (bott (sx s))) (negb (bott (sy s)))) (negb (bott (sz s))).
Definition idem_cons_ok (s : store) : bool :=
  implb (consistent_b (propagator s)) (seqb (propagator (propagator s)) (propagator s)).
Definition allstores : list store :=
  flat_map (fun ix => flat_map (fun iy => map (fun iz => St ix iy iz) itvs) itvs) itvs.

Theorem idem_grid : forallb idem_cons_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
