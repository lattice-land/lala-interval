(* ========================================================================= *)
(* Claim 5 (Proposition "galois-closure-proposition"):                       *)
(* "For any Galois connection A ⇄(α,γ) B, if f ∈ A → A is a closure          *)
(*  operator, then so is α ∘ f ∘ γ."                                         *)
(*                                                                           *)
(* Closure operators follow the paper's convention: idempotent, monotone     *)
(* and reductive.  On ordered setoids, idempotency is up to the setoid       *)
(* equality oeq.                                                             *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia.
From Paper Require Import claim1 claim2 claim3.

(* ---------- Operators on ordered setoids ---------- *)

Definition monotoneO (A : OSet) (f : oc A -> oc A) : Prop :=
  forall x y, ole x y -> ole (f x) (f y).
Definition reductiveO (A : OSet) (f : oc A -> oc A) : Prop :=
  forall x, ole (f x) x.
Definition idempotentO (A : OSet) (f : oc A -> oc A) : Prop :=
  forall x, oeq (f (f x)) (f x).

Definition closure_opO (A : OSet) (f : oc A -> oc A) : Prop :=
  idempotentO A f /\ monotoneO A f /\ reductiveO A f.

(* ======================= CLAIM 5 ======================= *)

Theorem claim5 :
  forall (A B : OSet) (G : GaloisConnection A B) (f : oc A -> oc A),
    closure_opO A f ->
    closure_opO B (fun b => galpha G (f (ggamma G b))).
Proof.
  intros A B G f [Hid [Hmon Hred]].
  split; [|split].
  - (* idempotent *)
    intros b. apply ole_antisym.
    + (* g (g b) ≤ g b *)
      apply gc_alpha_monotone, Hmon.
      (* γ(α(f(γ b))) ≤ γ b *)
      apply gc_gamma_monotone.
      eapply ole_trans; [apply gc_alpha_monotone, Hred | apply gc_alpha_gamma_reductive].
    + (* g b ≤ g (g b) *)
      eapply ole_trans with
        (y := galpha G (f (f (ggamma G b)))).
      * apply gc_alpha_monotone. apply ole_refl. apply oeq_sym. apply Hid.
      * apply gc_alpha_monotone, Hmon, gc_gamma_alpha_extensive.
  - (* monotone *)
    intros b b' Hle.
    apply gc_alpha_monotone, Hmon, gc_gamma_monotone, Hle.
  - (* reductive *)
    intros b.
    eapply ole_trans; [apply gc_alpha_monotone, Hred | apply gc_alpha_gamma_reductive].
Qed.

(* ---------- Instantiation used in the paper ---------- *)
(* Each concrete propagator S[c] is a closure operator on ⟨P(Asn), ⊆⟩, hence
   S×[c] = α× ∘ S[c] ∘ γ× is a closure operator on D. *)

Lemma csem_closure_opO : forall (X : Type) (c : constraint X),
  closure_opO (ConcreteD X) (csem c).
Proof.
  intros X c. split; [|split].
  - intros P a. unfold csem, inter. simpl. tauto.
  - intros P Q H a. unfold csem, inter. simpl in *. firstorder.
  - intros P a. unfold csem, inter. simpl. tauto.
Qed.

Corollary claim5_cartesian_propagator :
  forall (X : Type) (c : constraint X),
    closure_opO (D_OSet X)
      (fun d => galpha (GC_Cartesian X) (csem c (ggamma (GC_Cartesian X) d))).
Proof.
  intros X c. apply claim5. apply csem_closure_opO.
Qed.
