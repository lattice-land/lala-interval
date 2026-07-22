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

Definition contains (i : zitv) (v : Z) : Prop :=
  leq_zinf (lb i) (Fin v) /\ leq_zinf (Fin v) (ub i).

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

(* TODO: lemmas not renamed here. *)

Lemma ne_inter3_r : forall i j, is_not_bot_zitv (meet_zitv i j) = true -> is_not_bot_zitv j = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]]; cbn; intros H; try reflexivity; try discriminate;
    apply Z.leb_le; apply Z.leb_le in H; lia.
Qed.

(* Meet is monotone in BOTH arguments, unconditionally under the quotient
   order: if the meet is empty it is bottom, otherwise both inputs are
   non-empty and the raw bounds move monotonically. *)
Lemma inter3_mono : forall i i' j j',
  leq_zitv i i' -> leq_zitv j j' -> leq_zitv (meet_zitv i j) (meet_zitv i' j').
Proof.
  intros i i' j j' Hii Hjj.
  destruct (is_not_bot_zitv (meet_zitv i j)) eqn:E; [ | apply bot_is_leq_all_zitv; exact E ].
  pose proof (ne_inter3 _ _ E) as Ei. pose proof (ne_inter3_r _ _ E) as Ej.
  apply (all_is_geq_bot_zitv i i' Ei) in Hii as [Hli Hhi].
  apply (all_is_geq_bot_zitv j j' Ej) in Hjj as [Hlj Hhj].
  apply leq_zitv_intro; unfold meet_zitv; cbn [lb ub].
  - apply max_zinf_mono; assumption.
  - apply min_zinf_mono; assumption.
Qed.

Lemma contains_inter : forall i j v, contains i v -> contains j v -> contains (meet_zitv i j) v.
Proof.
  intros [li ui] [lj uj] v [H1 H2] [H3 H4]; cbn in *; split; cbn.
  - destruct li as [x| |], lj as [y| |]; cbn in *; try easy; lia.
  - destruct ui as [x| |], uj as [y| |]; cbn in *; try easy; lia.
Qed.
