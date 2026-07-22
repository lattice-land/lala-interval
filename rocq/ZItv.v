(** * zitv: consolidated interval + division machinery

    Self-contained merge of the [zitv], [fdiv2] and [fdiv3] modules (finite
    interval infrastructure, the compressed finite floored-division
    propagator, and the infinity-aware division helpers).  Nothing here
    changed except that [fdiv3]'s qualified [fdiv2.cdiv]/[fdiv2.sol]
    references are now local.  Provided so that [div4] depends on a single
    module. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Export ZInf.
Open Scope Z_scope.

(* ================================================================== *)
(** Interval over extended integers (zinf) *)
(* ================================================================== *)

Record zitv := ZItv { lb : zinf ; ub : zinf }.

Definition bot_zitv : zitv := ZItv Pinf Ninf.

Definition in_zitv (i : zitv) (v : Z) : Prop :=
  leq_zinf (lb i) (Fin v) /\ leq_zinf (Fin v) (ub i).

(* [l, u] := [-u, -l] (bot maps to bot). *)
Definition neg_zitv (i : zitv) : zitv := ZItv (neg_zinf (ub i)) (neg_zinf (lb i)).

(* neq_zero: shave a zero bound *)
Definition neq0_zitv (i : zitv) : zitv :=
  ZItv (if iszero_zinf (lb i) then Fin 1 else lb i)
       (if iszero_zinf (ub i) then Fin (-1) else ub i).

(* 4-corner product hull *)
Definition mul_zitv (iy iz : zitv) : zitv :=
  ZItv (min_zinf (min_zinf (mul_zinf (lb iy) (lb iz)) (mul_zinf (lb iy) (ub iz)))
             (min_zinf (mul_zinf (ub iy) (lb iz)) (mul_zinf (ub iy) (ub iz))))
       (max_zinf (max_zinf (mul_zinf (lb iy) (lb iz)) (mul_zinf (lb iy) (ub iz)))
             (max_zinf (mul_zinf (ub iy) (lb iz)) (mul_zinf (ub iy) (ub iz)))).


(* Test for the bottom equivalence class (non-emptiness test of the interval) (l > u \/ l = +oo \/ u = -oo) *)
Definition isbot_zitv (i : zitv) : bool :=
  match lb i, ub i with
  | Pinf, _ => true
  | _, Ninf => true
  | Ninf, _ => false
  | _, Pinf => false
  | Fin a, Fin b => a >? b
  end.

Definition is_not_bot_zitv (i : zitv) : bool :=
  match lb i, ub i with
  | Pinf, _ => false
  | _, Ninf => false
  | Ninf, _ => true
  | _, Pinf => true
  | Fin a, Fin b => a <=? b
  end.

Definition leq_zitv (i j : zitv) : Prop :=
  is_not_bot_zitv i = false \/ (leq_zinf (lb j) (lb i) /\ leq_zinf (ub i) (ub j)).

Definition meet_zitv (i j : zitv) : zitv :=
  ZItv (max_zinf (lb i) (lb j)) (min_zinf (ub i) (ub j)).

Definition join_nobot_zitv (i j : zitv) : zitv :=
  ZItv (min_zinf (lb i) (lb j)) (max_zinf (ub i) (ub j)).

(* ---- intro / inversion helpers for the quotient order ---- *)
Lemma leq_zitv_intro : forall i j, leq_zinf (lb j) (lb i) -> leq_zinf (ub i) (ub j) -> leq_zitv i j.
Proof. intros i j Hl Hh; right; split; assumption. Qed.

Lemma bot_is_leq_all_zitv : forall i j, is_not_bot_zitv i = false -> leq_zitv i j.
Proof. intros i j H; left; exact H. Qed.

Lemma all_is_geq_bot_zitv : forall i j, is_not_bot_zitv i = true -> leq_zitv i j ->
  leq_zinf (lb j) (lb i) /\ leq_zinf (ub i) (ub j).
Proof. intros i j Hne [Hb | Hraw]; [ rewrite Hne in Hb; discriminate | exact Hraw ]. Qed.

Lemma contains_not_bot_implies_not_bot_zitv : forall i j, is_not_bot_zitv i = true ->
  leq_zinf (lb j) (lb i) -> leq_zinf (ub i) (ub j) -> is_not_bot_zitv j = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]]; cbn; intros Hne Hl Hh;
    try reflexivity; try discriminate; try (exfalso; exact Hl); try (exfalso; exact Hh);
    apply Z.leb_le in Hne; apply Z.leb_le; lia.
Qed.

(* ---- non-emptiness from membership ---- *)
Lemma nonempty_is_not_bot_zitv : forall i v, in_zitv i v -> is_not_bot_zitv i = true.
Proof.
  intros i v [Hlo Hhi]. unfold is_not_bot_zitv.
  destruct (lb i) as [a| |]; destruct (ub i) as [b| |]; cbn in *;
    try reflexivity; try contradiction. apply Z.leb_le; lia.
Qed.

Lemma not_bot_implies_lb_leq_ub_zitv : forall i, is_not_bot_zitv i = true -> leq_zinf (lb i) (ub i).
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; try exact I. apply Z.leb_le; exact H.
Qed.

(* TODO: lemmas not fully renamed from here. *)

Lemma ne_inter3 : forall i j, is_not_bot_zitv (meet_zitv i j) = true -> is_not_bot_zitv i = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]]; cbn; intros H; try reflexivity; try discriminate;
    apply Z.leb_le; apply Z.leb_le in H; lia.
Qed.

Lemma ne_inter_r : forall i j, is_not_bot_zitv (meet_zitv i j) = true -> is_not_bot_zitv j = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]]; cbn; intros H; try reflexivity; try discriminate;
    apply Z.leb_le; apply Z.leb_le in H; lia.
Qed.

(* Meet is monotone in BOTH arguments, unconditionally under the quotient
   order: if the meet is empty it is bottom, otherwise both inputs are
   non-empty and the raw bounds move monotonically. *)
Lemma inter_mono : forall i i' j j',
  leq_zitv i i' -> leq_zitv j j' -> leq_zitv (meet_zitv i j) (meet_zitv i' j').
Proof.
  intros i i' j j' Hii Hjj.
  destruct (is_not_bot_zitv (meet_zitv i j)) eqn:E; [ | apply bot_is_leq_all_zitv; exact E ].
  pose proof (ne_inter3 _ _ E) as Ei. pose proof (ne_inter_r _ _ E) as Ej.
  apply (all_is_geq_bot_zitv i i' Ei) in Hii as [Hli Hhi].
  apply (all_is_geq_bot_zitv j j' Ej) in Hjj as [Hlj Hhj].
  apply leq_zitv_intro; unfold meet_zitv; cbn [lb ub].
  - apply max_zinf_monotone; assumption.
  - apply min_zinf_monotone; assumption.
Qed.

Lemma contains_inter : forall i j v, in_zitv i v -> in_zitv j v -> in_zitv (meet_zitv i j) v.
Proof.
  intros [li ui] [lj uj] v [H1 H2] [H3 H4]; cbn in *; split; cbn.
  - destruct li as [x| |], lj as [y| |]; cbn in *; try easy; lia.
  - destruct ui as [x| |], uj as [y| |]; cbn in *; try easy; lia.
Qed.

Lemma leq_zitv_reflexivity : forall i, leq_zitv i i.
Proof. intro i; apply leq_zitv_intro; apply leq_zinf_refl. Qed.

Lemma leq_zitv_transitivity : forall i j k, leq_zitv i j -> leq_zitv j k -> leq_zitv i k.
Proof.
  intros i j k H1 H2.
  destruct (is_not_bot_zitv i) eqn:Ei; [ | apply bot_is_leq_all_zitv; exact Ei ].
  apply (all_is_geq_bot_zitv i j Ei) in H1 as [Hl1 Hh1].
  assert (Enj : is_not_bot_zitv j = true) by (apply (contains_not_bot_implies_not_bot_zitv i j Ei Hl1 Hh1)).
  apply (all_is_geq_bot_zitv j k Enj) in H2 as [Hl2 Hh2].
  apply leq_zitv_intro; eapply leq_zinf_trans; eassumption.
Qed.

Lemma inter_leq_zitv_l : forall i j, leq_zitv (meet_zitv i j) i.
Proof.
  intros i j; apply leq_zitv_intro; unfold meet_zitv; cbn [lb ub];
  [ apply leq_zinf_max_zinf_l | apply leq_zinf_min_zinf_l ].
Qed.

(* meet = [meet_zitv] is the greatest lower bound *)
Lemma inter_leq_zitv_r : forall i j, leq_zitv (meet_zitv i j) j.
Proof.
  intros i j; apply leq_zitv_intro; unfold meet_zitv; cbn [lb ub];
  [ apply leq_zinf_max_zinf_r | apply leq_zinf_min_zinf_r ].
Qed.

Lemma inter_glb : forall i j c, leq_zitv c i -> leq_zitv c j -> leq_zitv c (meet_zitv i j).
Proof.
  intros i j c Hci Hcj. destruct (is_not_bot_zitv c) eqn:Ec; [ | apply bot_is_leq_all_zitv; exact Ec ].
  apply (all_is_geq_bot_zitv c i Ec) in Hci as [Hli Hhi].
  apply (all_is_geq_bot_zitv c j Ec) in Hcj as [Hlj Hhj].
  apply leq_zitv_intro; unfold meet_zitv; cbn [lb ub].
  - apply max_zinf_lub; assumption.
  - apply leq_zinf_min_zinf_glb; assumption.
Qed.
