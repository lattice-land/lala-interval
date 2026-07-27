(* ========================================================================= *)
(* Claim 11:                                                                 *)
(* "The interval abstract domain is a lattice I = ⟨(X → Ĩ)/∼I, ⊑̇, ⊔̇, ⊓̇⟩      *)
(*  where all operations are lifted pointwise from Ĩ with special care for   *)
(*  the bottom equivalence class. ... I is a complete lattice."              *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical.
From Paper Require Import claim1 claim2 claim8 claim9.
Open Scope Z_scope.

(* Convenient forms of the Ĩ ordered-setoid laws. *)
Lemma ieq_refl : forall i, ieq i i.
Proof. intros i. right. reflexivity. Qed.

Lemma ieq_sym : forall i j, ieq i j -> ieq j i.
Proof. intros i j [[H1 H2]|H]; [left; tauto | right; congruence]. Qed.

Lemma ieq_trans : forall i j k, ieq i j -> ieq j k -> ieq i k.
Proof. exact (oeq_trans (o:=QItv_OSet)). Qed.

Lemma isle_refl : forall i, isle i i.
Proof. intros i. right. split; apply zle_refl. Qed.

Lemma isle_of_ieq : forall i j, ieq i j -> isle i j.
Proof. exact (ole_refl (o:=QItv_OSet)). Qed.

Lemma isle_trans : forall i j k, isle i j -> isle j k -> isle i k.
Proof. exact (ole_trans (o:=QItv_OSet)). Qed.

Lemma isle_antisym : forall i j, isle i j -> isle j i -> ieq i j.
Proof. exact (ole_antisym (o:=QItv_OSet)). Qed.

Lemma isle_isbot : forall i j, isle i j -> isbot j -> isbot i.
Proof.
  intros i j [H|H] Hb; [exact H | exact (ile_isbot i j H Hb)].
Qed.

Lemma ieq_isbot : forall i j, ieq i j -> isbot i -> isbot j.
Proof. intros i j [[H1 H2]|H] Hb; [exact H2 | congruence]. Qed.

(* ==================== The interval store domain I ==================== *)

Section IntervalStore.
  Context (X : Type).

  Definition istore : Type := X -> Itv.

  (* Failed stores. *)
  Definition isbotI (d : istore) : Prop := exists x, isbot (d x).

  Definition eqI (d d' : istore) : Prop :=
    (isbotI d /\ isbotI d') \/ (forall x, ieq (d x) (d' x)).
  Definition leI (d d' : istore) : Prop :=
    isbotI d \/ (forall x, isle (d x) (d' x)).

  Lemma isbotI_eq : forall d d',
    (forall x, ieq (d x) (d' x)) -> isbotI d -> isbotI d'.
  Proof.
    intros d d' Hiff [x Hx]. exists x. exact (ieq_isbot _ _ (Hiff x) Hx).
  Qed.

  Lemma isbotI_le : forall d d',
    (forall x, isle (d' x) (d x)) -> isbotI d -> isbotI d'.
  Proof.
    intros d d' Hsub [x Hx]. exists x. exact (isle_isbot _ _ (Hsub x) Hx).
  Qed.

  Definition I_OSet : OSet.
  Proof.
    refine (MkOSet istore eqI leI _ _ _ _ _ _).
    - intros d. right. intros x. apply ieq_refl.
    - intros d d' [[H1 H2]|H];
        [left; tauto | right; intros x; apply ieq_sym, H].
    - intros d d' d'' [[H1 H2]|H] [[H3 H4]|H'].
      + left; tauto.
      + left. split; [exact H1|]. eapply isbotI_eq; eauto.
      + left. split; [|exact H4].
        eapply isbotI_eq; [|exact H3]. intros x. apply ieq_sym, H.
      + right. intros x. eapply ieq_trans; [apply H | apply H'].
    - intros d d' [[H1 H2]|H];
        [left; exact H1 | right; intros x; apply isle_of_ieq, H].
    - intros d d' d'' [H|H] [H'|H'].
      + left; exact H.
      + left; exact H.
      + left. eapply isbotI_le; [intros x; apply H | exact H'].
      + right. intros x. eapply isle_trans; [apply H | apply H'].
    - intros d d' [H|H] [H'|H'].
      + left. split; assumption.
      + left. split; [exact H|]. eapply isbotI_le; [intros x; apply H'|exact H].
      + left. split; [eapply isbotI_le; [intros x; apply H|exact H']|exact H'].
      + right. intros x. apply isle_antisym; [apply H | apply H'].
  Defined.

  (* Supremum: pointwise hull of the non-failed members. *)
  Definition supI (S : istore -> Prop) : istore :=
    fun x => issup (fun itv => exists d, S d /\ ~ isbotI d /\ itv = d x).

  Definition I_CL : CompleteLattice.
  Proof.
    refine (MkCL I_OSet supI _ _).
    - (* upper bound *)
      intros S d HdS.
      destruct (classic (isbotI d)) as [Hbot|Hbot].
      + left; exact Hbot.
      + right. intros x.
        apply (csup_ub (c := QItv_CL)). exists d. auto.
    - (* least *)
      intros S b Hub. right. intros x.
      apply (csup_least (c := QItv_CL)).
      intros itv [d [HdS [Hnb ->]]].
      destruct (Hub d HdS) as [Hbot|Hle]; [contradiction | apply Hle].
  Defined.

End IntervalStore.

(* ======================= CLAIM 11 ======================= *)
Theorem claim11 : forall (X : Type), complete_lattice (I_OSet X).
Proof. intros X. exact (CompleteLattice_complete (I_CL X)). Qed.
