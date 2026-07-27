(* ========================================================================= *)
(* Claim 13 (Theorem "Soundness commutation"):                               *)
(* "Let ⟨P(Asn), ⊆⟩ ⇄(α,γ) ⟨A, ≤⟩ ⇄(α',γ') ⟨B, ⊑⟩ be successive abstractions *)
(*  of the concrete domain and S_A[.] ∈ A → A and S_B[.] ∈ B → B.  Then, for *)
(*  every constraint c, if we have                                           *)
(*      α ∘ S[c] ∘ γ ≤̇ S_A[c]   and   α' ∘ S_A[c] ∘ γ' ⊑̇ S_B[c]              *)
(*  then                                                                     *)
(*      α' ∘ α ∘ S[c] ∘ γ ∘ γ' ⊑̇ S_B[c]."                                    *)
(*                                                                           *)
(* We prove it for arbitrary ordered setoids C ⇄ A ⇄ B and an arbitrary      *)
(* concrete function f : C → C (in the paper, f = S[c]); the paper statement *)
(* is the instance C = ⟨P(Asn), ⊆⟩.  We also record that the composition of  *)
(* Galois connections is a Galois connection, which makes the composite      *)
(* soundness statement meaningful.                                           *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia.
From Paper Require Import claim1 claim2 claim3 claim6.

(* Composing Galois connections. *)
Definition GC_compose {C A B : OSet}
  (G1 : GaloisConnection C A) (G2 : GaloisConnection A B)
  : GaloisConnection C B.
Proof.
  refine (MkGC C B
            (fun c => galpha G2 (galpha G1 c))
            (fun b => ggamma G1 (ggamma G2 b)) _).
  intros c b. split.
  - intros H. apply (gc_adj G1). apply (gc_adj G2). exact H.
  - intros H. apply (gc_adj G2). apply (gc_adj G1). exact H.
Defined.

(* ======================= CLAIM 13 ======================= *)
Theorem claim13 :
  forall (C A B : OSet)
         (G1 : GaloisConnection C A) (G2 : GaloisConnection A B)
         (f : oc C -> oc C) (SA : oc A -> oc A) (SB : oc B -> oc B),
    soundP G1 f SA ->
    soundP G2 SA SB ->
    soundP (GC_compose G1 G2) f SB.
Proof.
  intros C A B G1 G2 f SA SB Hs1 Hs2 b. simpl.
  eapply ole_trans; [|apply (Hs2 b)].
  apply (gc_alpha_monotone G2). apply Hs1.
Qed.
