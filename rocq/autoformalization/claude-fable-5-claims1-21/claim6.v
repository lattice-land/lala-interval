(* ========================================================================= *)
(* Claim 6:                                                                  *)
(* "The functional composition of monotone and sound propagators is sound:  *)
(*  this is important as it means it suffices to prove soundness            *)
(*  independently on each propagator."                                       *)
(*                                                                           *)
(* Given a Galois connection C ⇄(α,γ) A, a propagator p ∈ A → A is sound     *)
(* for a concrete function f ∈ C → C iff α ∘ f ∘ γ ≤̇ p.  We prove the        *)
(* binary composition statement in full generality, and instantiate it to    *)
(* the paper's setting: a finite family of constraints c1,…,cn with sound    *)
(* monotone propagators p1,…,pn, whose composition is sound for              *)
(* S[c1] ∘ … ∘ S[cn].                                                        *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia List.
From Paper Require Import claim1 claim2 claim3 claim5.
Import ListNotations.

(* Soundness of a propagator p for a concrete function f, w.r.t. a Galois
   connection G : C ⇄ A  (α ∘ f ∘ γ ≤̇ p). *)
Definition soundP {C A : OSet} (G : GaloisConnection C A)
  (f : oc C -> oc C) (p : oc A -> oc A) : Prop :=
  forall a, ole (galpha G (f (ggamma G a))) (p a).

(* ======================= CLAIM 6 ======================= *)
(* Binary version, in full generality. *)
Theorem claim6 :
  forall (C A : OSet) (G : GaloisConnection C A)
         (f1 f2 : oc C -> oc C) (p1 p2 : oc A -> oc A),
    monotoneO C f1 -> monotoneO A p1 ->
    soundP G f1 p1 -> soundP G f2 p2 ->
    soundP G (fun c => f1 (f2 c)) (fun a => p1 (p2 a)).
Proof.
  intros C A G f1 f2 p1 p2 Hf1 _ Hs1 Hs2 a.
  (* f2(γ a) ≤ γ(α(f2(γ a))) ≤ γ(p2 a) *)
  assert (H1 : ole (f2 (ggamma G a)) (ggamma G (p2 a))).
  { eapply ole_trans; [apply (gc_gamma_alpha_extensive G)|].
    apply (gc_gamma_monotone G), Hs2. }
  eapply ole_trans; [|apply (Hs1 (p2 a))].
  apply (gc_alpha_monotone G), Hf1, H1.
Qed.

(* ---------- Instantiation: composition of constraint propagators ---------- *)

(* Abstract composition p1 ∘ … ∘ pn. *)
Fixpoint compose_props {A : OSet} (ps : list (oc A -> oc A)) (a : oc A) : oc A :=
  match ps with
  | [] => a
  | p :: tl => p (compose_props tl a)
  end.

Lemma csem_monotoneO : forall (X : Type) (c : constraint X),
  monotoneO (ConcreteD X) (csem c).
Proof. intros X c P Q H a. unfold csem, inter. simpl in *. firstorder. Qed.

Lemma compose_all_monotoneO : forall (X : Type) (cs : list (constraint X)),
  monotoneO (ConcreteD X) (compose_all cs).
Proof.
  intros X cs P Q H a. rewrite !compose_all_spec. intuition auto.
Qed.

(* The n-ary paper statement: if each propagator p_i is sound for its
   constraint c_i (and monotone), then p1 ∘ … ∘ pn is sound for
   S[c1] ∘ … ∘ S[cn]. *)
Theorem claim6_constraints :
  forall (X : Type) (A : OSet) (G : GaloisConnection (ConcreteD X) A)
         (l : list (constraint X * (oc A -> oc A))),
    (forall cp, In cp l -> soundP G (csem (fst cp)) (snd cp) /\ monotoneO A (snd cp)) ->
    soundP G (compose_all (map fst l)) (compose_props (map snd l)).
Proof.
  intros X A G l Hl.
  induction l as [|[c p] tl IH]; simpl.
  - (* empty composition: identity is sound for identity *)
    intros a. apply (gc_alpha_gamma_reductive G).
  - destruct (Hl (c, p) (or_introl eq_refl)) as [Hs Hm].
    exact (claim6 (ConcreteD X) A G (csem c) (compose_all (map fst tl)) p
             (compose_props (map snd tl))
             (csem_monotoneO X c) Hm Hs
             (IH (fun cp Hin => Hl cp (or_intror Hin)))).
Qed.
