(* ========================================================================= *)
(* Claim 3:                                                                  *)
(* "The pair ⟨α×, γ×⟩ is a Galois connection", where                          *)
(*    α×(P) ≜ x ∈ X ↦ { asn(x) | asn ∈ P }                                   *)
(*    γ×(P̄) ≜ { asn ∈ Asn | ∀x ∈ X, asn(x) ∈ P̄(x) }                          *)
(* between the concrete domain ⟨P(Asn), ⊆⟩ and the Cartesian abstraction D.  *)
(*                                                                           *)
(* This file also introduces the general notion of Galois connection between *)
(* ordered setoids, together with its basic derived facts (monotonicity of   *)
(* α and γ, extensivity/reductivity of the round trips), reused later.       *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical.
From Paper Require Import claim1 claim2.

(* ---------- Galois connections between ordered setoids ---------- *)

Record GaloisConnection (C A : OSet) : Type := MkGC {
  galpha : oc C -> oc A;
  ggamma : oc A -> oc C;
  gc_adj : forall (c : oc C) (a : oc A),
      ole (galpha c) a <-> ole c (ggamma a)
}.

Arguments galpha {C A}.
Arguments ggamma {C A}.
Arguments gc_adj {C A}.

Section GCFacts.
  Context {C A : OSet} (G : GaloisConnection C A).

  Lemma gc_gamma_alpha_extensive : forall c, ole c (ggamma G (galpha G c)).
  Proof. intros c. apply (gc_adj G). apply ole_refl'. Qed.

  Lemma gc_alpha_gamma_reductive : forall a, ole (galpha G (ggamma G a)) a.
  Proof. intros a. apply (gc_adj G). apply ole_refl'. Qed.

  Lemma gc_alpha_monotone : forall c c',
    ole c c' -> ole (galpha G c) (galpha G c').
  Proof.
    intros c c' Hle. apply (gc_adj G).
    eapply ole_trans; [exact Hle | apply gc_gamma_alpha_extensive].
  Qed.

  Lemma gc_gamma_monotone : forall a a',
    ole a a' -> ole (ggamma G a) (ggamma G a').
  Proof.
    intros a a' Hle. apply (gc_adj G).
    eapply ole_trans; [apply gc_alpha_gamma_reductive | exact Hle].
  Qed.

  Lemma gc_alpha_proper : forall c c',
    oeq c c' -> oeq (galpha G c) (galpha G c').
  Proof.
    intros c c' He. apply ole_antisym; apply gc_alpha_monotone, ole_refl;
      [exact He | apply oeq_sym; exact He].
  Qed.

  Lemma gc_gamma_proper : forall a a',
    oeq a a' -> oeq (ggamma G a) (ggamma G a').
  Proof.
    intros a a' He. apply ole_antisym; apply gc_gamma_monotone, ole_refl;
      [exact He | apply oeq_sym; exact He].
  Qed.

  (* A left adjoint preserves all existing least upper bounds; instrumental
     for the "join of best propagators" decompositions used in claims 20-21. *)
  Lemma gc_alpha_preserves_lub : forall (S : oc C -> Prop) (l : oc C),
    is_lub C S l ->
    is_lub A (fun a => exists c, S c /\ oeq a (galpha G c)) (galpha G l).
  Proof.
    intros S l [Hub Hleast]. split.
    - intros a [c [HcS Heq]]. eapply ole_eq_l; [exact Heq|].
      apply gc_alpha_monotone, Hub, HcS.
    - intros b Hb. apply (gc_adj G). apply Hleast.
      intros c HcS. apply (gc_adj G). apply Hb.
      exists c. split; [exact HcS | apply oeq_refl].
  Qed.

End GCFacts.

(* ---------- The Cartesian abstraction and concretization ---------- *)

Section CartesianGC.
  Context (X : Type).

  (* The concrete domain: ⟨P(Asn), ⊆⟩. *)
  Definition ConcreteD : OSet := PowOSet (Asn X).

  Definition alphaX (P : powerset (Asn X)) : domfun X :=
    fun x => fun v => exists asn, P asn /\ asn x = v.

  Definition gammaX (d : domfun X) : powerset (Asn X) :=
    fun asn => forall x, d x (asn x).

  (* The adjunction property. *)
  Lemma alphaX_gammaX_adjunction :
    forall (P : powerset (Asn X)) (d : domfun X),
      leD X (alphaX P) d <-> subset P (gammaX d).
  Proof.
    intros P d. split.
    - intros [Hbot|Hle] asn HP.
      + (* α×(P) failed: P must be empty *)
        destruct Hbot as [x Hx].
        exfalso. apply (Hx (asn x)). exists asn. auto.
      + intros x. apply Hle. exists asn. auto.
    - intros Hsub. right. intros x v [asn [HP Heq]].
      subst v. apply (Hsub asn HP).
  Qed.

  (* ======================= CLAIM 3 ======================= *)
  Definition GC_Cartesian : GaloisConnection ConcreteD (D_OSet X) :=
    MkGC ConcreteD (D_OSet X) alphaX gammaX alphaX_gammaX_adjunction.

  Theorem claim3 :
    forall (P : powerset (Asn X)) (d : domfun X),
      leD X (alphaX P) d <-> subset P (gammaX d).
  Proof. exact alphaX_gammaX_adjunction. Qed.

End CartesianGC.
