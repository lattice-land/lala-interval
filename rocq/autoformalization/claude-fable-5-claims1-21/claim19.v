(* ========================================================================= *)
(* Claim 19 (Theorem "Join preserves α-completeness"):                       *)
(* "Let C and A be lattices equipped with a Galois connection C ⇄(α,γ) A,    *)
(*  and p ∈ A → A a propagator of the form p1 ⊔̇ p2 given p1,p2 ∈ A → A with  *)
(*  ⊔̇ the pointwise join on A.  Then, p is α-complete iff both p1 and p2     *)
(*  are α-complete."                                                         *)
(*                                                                           *)
(* α-completeness of p for a concrete function f: p ≤̇ α ∘ f ∘ γ.             *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia.
From Paper Require Import claim1 claim2 claim3 claim6.

(* α-completeness (the reverse inclusion of soundness). *)
Definition alphacompleteP {C A : OSet} (G : GaloisConnection C A)
  (f : oc C -> oc C) (p : oc A -> oc A) : Prop :=
  forall a, ole (p a) (galpha G (f (ggamma G a))).

(* ======================= CLAIM 19 ======================= *)
Theorem claim19 :
  forall (C A : OSet) (G : GaloisConnection C A)
         (joinA : oc A -> oc A -> oc A),
    (forall x y, ole x (joinA x y)) ->
    (forall x y, ole y (joinA x y)) ->
    (forall x y b, ole x b -> ole y b -> ole (joinA x y) b) ->
    forall (f : oc C -> oc C) (p1 p2 : oc A -> oc A),
      alphacompleteP G f (fun a => joinA (p1 a) (p2 a))
      <-> (alphacompleteP G f p1 /\ alphacompleteP G f p2).
Proof.
  intros C A G joinA Hub_l Hub_r Hleast f p1 p2. split.
  - intros H. split; intros a.
    + eapply ole_trans; [apply Hub_l | apply (H a)].
    + eapply ole_trans; [apply Hub_r | apply (H a)].
  - intros [H1 H2] a. apply Hleast; [apply H1 | apply H2].
Qed.

(* A propagator is best iff it is sound and α-complete. *)
Lemma best_iff_sound_and_complete :
  forall (C A : OSet) (G : GaloisConnection C A)
         (f : oc C -> oc C) (p : oc A -> oc A),
    (forall a, oeq (galpha G (f (ggamma G a))) (p a))
    <-> (soundP G f p /\ alphacompleteP G f p).
Proof.
  intros C A G f p. split.
  - intros H. split; intros a.
    + apply ole_refl, H.
    + apply ole_refl, oeq_sym, H.
  - intros [Hs Hc] a. apply ole_antisym; [apply Hs | apply Hc].
Qed.
