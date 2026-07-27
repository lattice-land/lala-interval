(* ========================================================================= *)
(* Claim 12:                                                                 *)
(* "The Galois connection D ⇄(αI,γI) I formally shows the abstraction I is   *)
(*  overapproximating D:                                                     *)
(*    αI(P) ≜ x ∈ X ↦ αi(P(x))      γI(P̄) ≜ x ∈ X ↦ γi(P̄(x)).               *)
(*  The pair ⟨αI, γI⟩ is a Galois connection."                               *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical.
From Paper Require Import claim1 claim2 claim3 claim8 claim9 claim10 claim11.
Open Scope Z_scope.

(* An abstraction of the empty set of integers is an empty interval, and
   conversely. *)
Lemma alphai_bot_of_empty : forall (S : powerset Z),
  (forall v, ~ S v) -> isbot (alphai S).
Proof.
  intros S H. unfold alphai, isbot. simpl. right; left.
  apply zinfS_empty. intros x [z [Hz _]]. exact (H z Hz).
Qed.

Lemma alphai_empty_of_bot : forall (S : powerset Z),
  isbot (alphai S) -> forall v, ~ S v.
Proof.
  intros S Hb v Hv.
  assert (Hmem : finset S (Fin v)) by (exists v; auto).
  pose proof (zinfS_lb (finset S) _ Hmem) as Hlo.
  pose proof (zsup_ub (finset S) _ Hmem) as Hhi.
  unfold alphai, isbot in Hb. simpl in Hb.
  destruct Hb as [H|[H|H]].
  - apply (zlt_nle _ _ H). eapply zle_trans; eauto.
  - rewrite H in Hlo. simpl in Hlo. exact Hlo.
  - rewrite H in Hhi. simpl in Hhi. exact Hhi.
Qed.

(* ---------- The store-level abstraction ---------- *)

Section StoreGC.
  Context (X : Type).

  Definition alphaI (P : domfun X) : istore X := fun x => alphai (P x).
  Definition gammaI (d : istore X) : domfun X := fun x => gammai (d x).

  (* ======================= CLAIM 12 ======================= *)
  Theorem claim12 : forall (P : domfun X) (d : istore X),
    leI X (alphaI P) d <-> leD X P (gammaI d).
  Proof.
    intros P d. split.
    - intros [Hbot|Hle].
      + (* αI(P) failed: P is failed *)
        destruct Hbot as [x Hx]. left. exists x.
        exact (alphai_empty_of_bot (P x) Hx).
      + right. intros x v HP.
        destruct (claim10 (P x) (d x)) as [Hfwd _].
        exact (Hfwd (Hle x) v HP).
    - intros [Hbot|Hle].
      + left. destruct Hbot as [x Hx]. exists x.
        apply alphai_bot_of_empty. exact Hx.
      + right. intros x.
        apply (claim10 (P x) (d x)). intros v HP. exact (Hle x v HP).
  Qed.

  Definition GC_Store : GaloisConnection (D_OSet X) (I_OSet X) :=
    MkGC (D_OSet X) (I_OSet X) alphaI gammaI claim12.

End StoreGC.
