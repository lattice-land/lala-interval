(* ========================================================================= *)
(* Claim 10:                                                                 *)
(* "There is a Galois connection P(Z) ⇄(αi,γi) Ĩ defined by                  *)
(*    αi(S) ≜ [inf S, sup S]     γi([ℓ,u]) ≜ {v ∈ Z | ℓ ≤ v ≤ u}.            *)
(*  The pair ⟨αi, γi⟩ is a Galois connection."                               *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical.
From Paper Require Import claim1 claim2 claim3 claim8 claim9.
Open Scope Z_scope.

(* The embedding of a set of integers into Z∞. *)
Definition finset (S : powerset Z) : Zinf -> Prop :=
  fun x => exists z, S z /\ x = Fin z.

Definition alphai (S : powerset Z) : Itv :=
  (zinfS (finset S), zsup (finset S)).

Definition gammai (i : Itv) : powerset Z := fun v => imem v i.

(* ======================= CLAIM 10 ======================= *)

Theorem claim10 : forall (S : powerset Z) (i : Itv),
  isle (alphai S) i <-> subset S (gammai i).
Proof.
  intros S i. split.
  - intros Hle v Hv.
    assert (Hmem : finset S (Fin v)) by (exists v; auto).
    pose proof (zinfS_lb (finset S) _ Hmem) as Hlo.
    pose proof (zsup_ub (finset S) _ Hmem) as Hhi.
    destruct Hle as [Hbot|[H1 H2]].
    + (* α(S) empty contradicts v ∈ S *)
      exfalso. destruct i as [l u]. unfold alphai, isbot in Hbot. simpl in *.
      destruct Hbot as [H|[H|H]].
      * apply (zlt_nle _ _ H). eapply zle_trans; eauto.
      * rewrite H in Hlo. simpl in Hlo. exact Hlo.
      * rewrite H in Hhi. simpl in Hhi. exact Hhi.
    + (* fst i ≤ inf S ≤ v ≤ sup S ≤ snd i *)
      split.
      * eapply zle_trans; [exact H1 | exact Hlo].
      * eapply zle_trans; [exact Hhi | exact H2].
  - intros Hsub. right. split; unfold alphai; simpl.
    + apply zinfS_greatest. intros x [z [Hz ->]].
      destruct (Hsub z Hz) as [H1 _]. exact H1.
    + apply zsup_least. intros x [z [Hz ->]].
      destruct (Hsub z Hz) as [_ H2]. exact H2.
Qed.

(* Packaged as a Galois connection between the ordered setoids. *)
Definition GC_Interval : GaloisConnection (PowOSet Z) QItv_OSet :=
  MkGC (PowOSet Z) QItv_OSet alphai gammai claim10.
