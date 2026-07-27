(* ========================================================================= *)
(* Claim 14 (corollary of the soundness commutation theorem):                *)
(* "A corollary that the best and best on assignment properties also         *)
(*  commute: since we have ⊑̇, it also covers =."                             *)
(*                                                                           *)
(* (a) Best commutation: if S_A is the best abstraction of f w.r.t. (α,γ)    *)
(*     and S_B is the best abstraction of S_A w.r.t. (α',γ'), then S_B is    *)
(*     the best abstraction of f w.r.t. the composed Galois connection.      *)
(*                                                                           *)
(* (b) Best-on-assignment commutation: concretely, the concrete domain is a  *)
(*     powerset domain P(T) (in the paper T = Asn).  If S_A is best on all   *)
(*     abstract elements whose concretization is a singleton, and S_B is     *)
(*     best w.r.t. S_A on all elements whose composite concretization is a   *)
(*     singleton, then S_B is best-on-assignment w.r.t. the composed Galois  *)
(*     connection.                                                           *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia.
From Paper Require Import claim1 claim2 claim3 claim6 claim13.

(* The "best" property: p is the best abstraction of f (α ∘ f ∘ γ ≐ p). *)
Definition bestP {C A : OSet} (G : GaloisConnection C A)
  (f : oc C -> oc C) (p : oc A -> oc A) : Prop :=
  forall a, oeq (galpha G (f (ggamma G a))) (p a).

(* ======================= CLAIM 14 ======================= *)

(* (a) The best property commutes. *)
Theorem claim14_best :
  forall (C A B : OSet)
         (G1 : GaloisConnection C A) (G2 : GaloisConnection A B)
         (f : oc C -> oc C) (SA : oc A -> oc A) (SB : oc B -> oc B),
    bestP G1 f SA ->
    bestP G2 SA SB ->
    bestP (GC_compose G1 G2) f SB.
Proof.
  intros C A B G1 G2 f SA SB Hb1 Hb2 b. simpl.
  eapply oeq_trans; [|apply (Hb2 b)].
  apply (gc_alpha_proper G2). apply Hb1.
Qed.

(* (b) The best-on-assignment property commutes.  The concrete domain is a
   powerset domain ⟨P(T), ⊆⟩; γ(a) = {t} expresses that a is an abstract
   assignment. *)
Definition singleton {T : Type} (t : T) : powerset T := fun t' => t' = t.

Theorem claim14_best_on_assignment :
  forall (T : Type) (A B : OSet)
         (G1 : GaloisConnection (PowOSet T) A) (G2 : GaloisConnection A B)
         (f : powerset T -> powerset T) (SA : oc A -> oc A) (SB : oc B -> oc B),
    (* S_A is best on abstract assignments *)
    (forall (a : oc A) (t : T),
        set_eq (ggamma G1 a) (singleton t) ->
        oeq (galpha G1 (f (ggamma G1 a))) (SA a)) ->
    (* S_B is best w.r.t. S_A on elements concretizing to assignments *)
    (forall (b : oc B),
        (exists t : T, set_eq (ggamma G1 (ggamma G2 b)) (singleton t)) ->
        oeq (galpha G2 (SA (ggamma G2 b))) (SB b)) ->
    (* then S_B is best-on-assignment for f w.r.t. the composition *)
    forall (b : oc B) (t : T),
      set_eq (ggamma (GC_compose G1 G2) b) (singleton t) ->
      oeq (galpha (GC_compose G1 G2) (f (ggamma (GC_compose G1 G2) b))) (SB b).
Proof.
  intros T A B G1 G2 f SA SB H1 H2 b t Hsing. simpl in *.
  eapply oeq_trans; [|apply (H2 b); exists t; exact Hsing].
  apply (gc_alpha_proper G2).
  apply (H1 (ggamma G2 b) t Hsing).
Qed.
