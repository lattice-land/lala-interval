(* ========================================================================= *)
(* Claim 8:                                                                  *)
(* "The structure ⟨I, ⪯, ⋎, ⋏⟩ is a lattice", where I = Z∞ × Z∞ and          *)
(*    [a,b] ⪯ [c,d] ≜ a ≥ c ∧ b ≤ d                                          *)
(*    [a,b] ⋎ [c,d] ≜ [min{a,c}, max{b,d}]                                   *)
(*    [a,b] ⋏ [c,d] ≜ [max{a,c}, min{b,d}]                                   *)
(*                                                                           *)
(* This file also develops the ordered structure of the extended integers    *)
(* Z∞ = Z ∪ {-∞, +∞} (order, min, max), reused by all later claims.          *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia.
From Paper Require Import claim1 claim2.
Open Scope Z_scope.

(* ==================== The extended integers Z∞ ==================== *)

Inductive Zinf : Type := MInf | Fin (z : Z) | PInf.

Definition zle (a b : Zinf) : Prop :=
  match a, b with
  | MInf, _ => True
  | Fin _, MInf => False
  | Fin x, Fin y => x <= y
  | Fin _, PInf => True
  | PInf, PInf => True
  | PInf, _ => False
  end.

Definition zlt (a b : Zinf) : Prop :=
  match a, b with
  | MInf, MInf => False
  | MInf, _ => True
  | Fin _, MInf => False
  | Fin x, Fin y => x < y
  | Fin _, PInf => True
  | PInf, _ => False
  end.

Definition zleb (a b : Zinf) : bool :=
  match a, b with
  | MInf, _ => true
  | Fin _, MInf => false
  | Fin x, Fin y => x <=? y
  | Fin _, PInf => true
  | PInf, PInf => true
  | PInf, _ => false
  end.

Lemma zleb_le : forall a b, zleb a b = true <-> zle a b.
Proof.
  intros [|x|] [|y|]; simpl; try tauto;
    try (split; [discriminate | contradiction]).
  apply Z.leb_le.
Qed.

Lemma zle_refl : forall a, zle a a.
Proof. intros [|x|]; simpl; lia. Qed.

Lemma zle_trans : forall a b c, zle a b -> zle b c -> zle a c.
Proof. intros [|x|] [|y|] [|z|]; simpl; try tauto; lia. Qed.

Lemma zle_antisym : forall a b, zle a b -> zle b a -> a = b.
Proof. intros [|x|] [|y|]; simpl; try tauto; intros; f_equal; lia. Qed.

Lemma zle_total : forall a b, zle a b \/ zle b a.
Proof. intros [|x|] [|y|]; simpl; try tauto; lia. Qed.

Lemma zlt_le : forall a b, zlt a b -> zle a b.
Proof. intros [|x|] [|y|]; simpl; try tauto; lia. Qed.

Lemma znlt_le : forall a b, ~ zlt a b -> zle b a.
Proof. intros [|x|] [|y|]; simpl; try tauto; lia. Qed.

Lemma znle_lt : forall a b, ~ zle a b -> zlt b a.
Proof. intros [|x|] [|y|]; simpl; try tauto; lia. Qed.

Lemma zlt_nle : forall a b, zlt a b -> ~ zle b a.
Proof. intros [|x|] [|y|]; simpl; try tauto; lia. Qed.

Lemma zle_lt_trans : forall a b c, zle a b -> zlt b c -> zlt a c.
Proof. intros [|x|] [|y|] [|z|]; simpl; try tauto; lia. Qed.

Lemma zlt_le_trans : forall a b c, zlt a b -> zle b c -> zlt a c.
Proof. intros [|x|] [|y|] [|z|]; simpl; try tauto; lia. Qed.

(* min and max on Z∞ *)
Definition zmin (a b : Zinf) : Zinf := if zleb a b then a else b.
Definition zmax (a b : Zinf) : Zinf := if zleb a b then b else a.

Lemma zmin_case : forall a b,
  (zmin a b = a /\ zle a b) \/ (zmin a b = b /\ zle b a).
Proof.
  intros a b. unfold zmin. destruct (zleb a b) eqn:E.
  - left. split; [reflexivity | apply zleb_le, E].
  - right. split; [reflexivity |].
    destruct (zle_total a b) as [H|H]; [|exact H].
    apply zleb_le in H. congruence.
Qed.

Lemma zmax_case : forall a b,
  (zmax a b = b /\ zle a b) \/ (zmax a b = a /\ zle b a).
Proof.
  intros a b. unfold zmax. destruct (zleb a b) eqn:E.
  - left. split; [reflexivity | apply zleb_le, E].
  - right. split; [reflexivity |].
    destruct (zle_total a b) as [H|H]; [|exact H].
    apply zleb_le in H. congruence.
Qed.

Lemma zmin_le_l : forall a b, zle (zmin a b) a.
Proof.
  intros a b. destruct (zmin_case a b) as [[-> H]|[-> H]];
    [apply zle_refl | exact H].
Qed.

Lemma zmin_le_r : forall a b, zle (zmin a b) b.
Proof.
  intros a b. destruct (zmin_case a b) as [[-> H]|[-> H]];
    [exact H | apply zle_refl].
Qed.

Lemma zmin_glb : forall a b c, zle c a -> zle c b -> zle c (zmin a b).
Proof.
  intros a b c Ha Hb. destruct (zmin_case a b) as [[-> _]|[-> _]]; assumption.
Qed.

Lemma zmax_ge_l : forall a b, zle a (zmax a b).
Proof.
  intros a b. destruct (zmax_case a b) as [[-> H]|[-> H]];
    [exact H | apply zle_refl].
Qed.

Lemma zmax_ge_r : forall a b, zle b (zmax a b).
Proof.
  intros a b. destruct (zmax_case a b) as [[-> H]|[-> H]];
    [apply zle_refl | exact H].
Qed.

Lemma zmax_lub : forall a b c, zle a c -> zle b c -> zle (zmax a b) c.
Proof.
  intros a b c Ha Hb. destruct (zmax_case a b) as [[-> _]|[-> _]]; assumption.
Qed.

(* ==================== Intervals ==================== *)

Definition Itv : Type := (Zinf * Zinf)%type.

(* The order ⪯ and the join ⋎ / meet ⋏ operations of the paper. *)
Definition ile (i j : Itv) : Prop := zle (fst j) (fst i) /\ zle (snd i) (snd j).
Definition ijoin (i j : Itv) : Itv := (zmin (fst i) (fst j), zmax (snd i) (snd j)).
Definition imeet (i j : Itv) : Itv := (zmax (fst i) (fst j), zmin (snd i) (snd j)).

(* The ordered set ⟨I, ⪯⟩ (a plain order, no quotient: oeq is equality). *)
Definition Itv_OSet : OSet.
Proof.
  refine (MkOSet Itv eq ile _ _ _ _ _ _).
  - reflexivity.
  - intros x y H; symmetry; exact H.
  - intros x y z H1 H2; congruence.
  - intros x y ->. split; apply zle_refl.
  - intros x y z [H1 H2] [H3 H4]. split; eapply zle_trans; eauto.
  - intros [a b] [c d] [H1 H2] [H3 H4]. simpl in *.
    f_equal; apply zle_antisym; assumption.
Defined.

(* Lattices (binary joins and meets) over an ordered setoid. *)
Definition is_lattice (A : OSet)
  (join meet : oc A -> oc A -> oc A) : Prop :=
  (forall x y, ole x (join x y)) /\
  (forall x y, ole y (join x y)) /\
  (forall x y b, ole x b -> ole y b -> ole (join x y) b) /\
  (forall x y, ole (meet x y) x) /\
  (forall x y, ole (meet x y) y) /\
  (forall x y b, ole b x -> ole b y -> ole b (meet x y)).

(* ======================= CLAIM 8 ======================= *)
Theorem claim8 : is_lattice Itv_OSet ijoin imeet.
Proof.
  repeat split; simpl in *.
  - apply zmin_le_l.
  - apply zmax_ge_l.
  - apply zmin_le_r.
  - apply zmax_ge_r.
  - destruct H as [H1 H2]. destruct H0 as [H3 H4]. simpl.
    apply zmin_glb; assumption.
  - destruct H as [H1 H2]. destruct H0 as [H3 H4]. simpl.
    apply zmax_lub; assumption.
  - apply zmax_ge_l.
  - apply zmin_le_l.
  - apply zmax_ge_r.
  - apply zmin_le_r.
  - destruct H as [H1 H2]. destruct H0 as [H3 H4]. simpl.
    apply zmax_lub; assumption.
  - destruct H as [H1 H2]. destruct H0 as [H3 H4]. simpl.
    apply zmin_glb; assumption.
Qed.
