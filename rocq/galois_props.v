(** * galois_props.v : Propositions 2 and 4 of the paper.

    General abstract-interpretation facts about a Galois connection
      C  <alpha, gamma>  A
    between two preorders.  (Prop 1, in cartesian_propagators.v, is the
    instance C = P(Asn), A = D, f = _ ∩ rel(c).)

    Prop 2 (closure-galois): if f : C -> C is a lower closure operator
      (reductive, monotone, idempotent), then g = alpha o f o gamma is a
      lower closure operator on A.

    Prop 4 (soundness & completeness compose on disjoint domains): the best
      transformer distributes over a concretization cover, and best-ness of
      a candidate propagator on the whole follows from best-ness on the
      covering pieces.  The completeness-only inequality [complete_composes]
      is the form used to factor case-split propagators (e.g. zdiv's
      positive/negative divisor slices joined by [join4]).

    (The paper's Prop 3 -- complete-on-singleton is obtained for free -- is
    a separate statement, not formalized here.)

    Everything is stated up to the order-equivalences [ceq]/[aeq] (mutual
    order), so no antisymmetry/quotient is assumed.  Axiom-free. *)

Section GaloisProps.

Context {C A : Type}.
Context (cle : C -> C -> Prop) (ale : A -> A -> Prop).
Context (alpha : C -> A) (gamma : A -> C).

(* the two orders are preorders *)
Hypothesis cle_refl  : forall c, cle c c.
Hypothesis cle_trans : forall x y z, cle x y -> cle y z -> cle x z.
Hypothesis ale_refl  : forall a, ale a a.
Hypothesis ale_trans : forall x y z, ale x y -> ale y z -> ale x z.

(* the Galois connection *)
Hypothesis galois : forall c a, ale (alpha c) a <-> cle c (gamma a).

Definition ceq (x y : C) : Prop := cle x y /\ cle y x.
Definition aeq (x y : A) : Prop := ale x y /\ ale y x.

Lemma aeq_refl  : forall a, aeq a a. Proof. split; apply ale_refl. Qed.
Lemma aeq_sym   : forall x y, aeq x y -> aeq y x. Proof. intros x y [H1 H2]; split; assumption. Qed.
Lemma aeq_trans : forall x y z, aeq x y -> aeq y z -> aeq x z.
Proof. intros x y z [H1 H2] [H3 H4]; split; eapply ale_trans; eassumption. Qed.

(* the four consequences of the adjunction *)
Lemma expand : forall c, cle c (gamma (alpha c)).
Proof. intro c. apply (proj1 (galois c (alpha c))). apply ale_refl. Qed.

Lemma reduce : forall a, ale (alpha (gamma a)) a.
Proof. intro a. apply (proj2 (galois (gamma a) a)). apply cle_refl. Qed.

Lemma alpha_mono : forall c c', cle c c' -> ale (alpha c) (alpha c').
Proof.
  intros c c' H. apply (proj2 (galois c (alpha c'))).
  eapply cle_trans; [ exact H | apply expand ].
Qed.

Lemma gamma_mono : forall a a', ale a a' -> cle (gamma a) (gamma a').
Proof.
  intros a a' H. apply (proj1 (galois (gamma a) a')).
  eapply ale_trans; [ apply reduce | exact H ].
Qed.

(* ================================================================== *)
(** ** Proposition 2 : alpha o f o gamma is a lower closure operator    *)
(* ================================================================== *)

Section Prop2.
Context (f : C -> C).
Hypothesis f_red  : forall c, cle (f c) c.                 (* reductive  *)
Hypothesis f_mono : forall c c', cle c c' -> cle (f c) (f c').  (* monotone   *)
Hypothesis f_idem : forall c, ceq (f (f c)) (f c).         (* idempotent *)

Definition g (a : A) : A := alpha (f (gamma a)).

Theorem g_reductive : forall a, ale (g a) a.
Proof. intro a. eapply ale_trans; [ apply alpha_mono; apply f_red | apply reduce ]. Qed.

Theorem g_monotone : forall a a', ale a a' -> ale (g a) (g a').
Proof. intros a a' H. apply alpha_mono, f_mono, gamma_mono, H. Qed.

Theorem g_idempotent : forall a, aeq (g (g a)) (g a).
Proof.
  intro a. split.
  - apply g_reductive.
  - unfold g. apply alpha_mono.
    eapply cle_trans; [ apply (proj2 (f_idem (gamma a))) | ].
    apply f_mono. apply expand.
Qed.

Theorem Prop2_closure :
  (forall a, ale (g a) a)
  /\ (forall a a', ale a a' -> ale (g a) (g a'))
  /\ (forall a, aeq (g (g a)) (g a)).
Proof. split; [ apply g_reductive | split; [ apply g_monotone | apply g_idempotent ] ]. Qed.

End Prop2.

(* ================================================================== *)
(** ** Proposition 4 : soundness & completeness compose on disjoint
       domains.  [gbest = alpha o f o gamma] is the best transformer of
       the concrete map [f] (e.g. [_ ∩ rel(c)]). *)
(* ================================================================== *)

Section Prop3.
Context (f : C -> C).
Hypothesis f_mono : forall c c', cle c c' -> cle (f c) (f c').
Context (cjoin : C -> C -> C) (ajoin : A -> A -> A).
(* [f] distributes over the concrete union (true for [_ ∩ rel(c)]) *)
Hypothesis f_add     : forall c c', ceq (f (cjoin c c')) (cjoin (f c) (f c')).
(* [alpha], a lower adjoint, preserves joins *)
Hypothesis alpha_add : forall c c', aeq (alpha (cjoin c c')) (ajoin (alpha c) (alpha c')).
(* the abstract join is monotone (it is a lub) *)
Hypothesis ajoin_mono : forall x x' y y', ale x x' -> ale y y' -> ale (ajoin x y) (ajoin x' y').

Definition gbest (a : A) : A := alpha (f (gamma a)).

(* congruence helpers *)
Lemma f_resp : forall c c', ceq c c' -> ceq (f c) (f c').
Proof. intros c c' [H1 H2]; split; apply f_mono; assumption. Qed.
Lemma alpha_resp : forall c c', ceq c c' -> aeq (alpha c) (alpha c').
Proof. intros c c' [H1 H2]; split; apply alpha_mono; assumption. Qed.
Lemma ajoin_resp : forall x x' y y', aeq x x' -> aeq y y' -> aeq (ajoin x y) (ajoin x' y').
Proof. intros x x' y y' [H1 H2] [H3 H4]; split; apply ajoin_mono; assumption. Qed.

(* the best transformer distributes over a concretization cover
   gamma(a) = gamma(a1) ∪ gamma(a2). *)
Theorem gbest_distributes : forall a a1 a2,
  ceq (gamma a) (cjoin (gamma a1) (gamma a2)) ->
  aeq (gbest a) (ajoin (gbest a1) (gbest a2)).
Proof.
  intros a a1 a2 Hcov. unfold gbest.
  eapply aeq_trans; [ apply alpha_resp, f_resp, Hcov | ].
  eapply aeq_trans; [ apply alpha_resp, f_add | apply alpha_add ].
Qed.

(* If a candidate propagator [p] distributes over covers, then being best
   (= agreeing with [gbest]) on each covering piece implies best on the whole:
   this is how optimality of a case-split propagator is proved piecewise. *)
Context (p : A -> A).
Hypothesis p_distributes : forall a a1 a2,
  ceq (gamma a) (cjoin (gamma a1) (gamma a2)) -> aeq (p a) (ajoin (p a1) (p a2)).

Theorem best_composes : forall a a1 a2,
  ceq (gamma a) (cjoin (gamma a1) (gamma a2)) ->
  aeq (p a1) (gbest a1) -> aeq (p a2) (gbest a2) ->
  aeq (p a) (gbest a).
Proof.
  intros a a1 a2 Hcov H1 H2.
  eapply aeq_trans; [ apply (p_distributes a a1 a2 Hcov) | ].
  eapply aeq_trans; [ apply ajoin_resp; [ exact H1 | exact H2 ] | ].
  apply aeq_sym, gbest_distributes, Hcov.
Qed.

(* Completeness-only version (a single inequality): if [p] is complete on
   each covering piece ([p ai <= gbest ai]) and [p] sub-distributes over the
   cover, then [p] is complete on the whole ([p a <= gbest a]).  This is the
   abstract shape of zdiv's [join4_sle_cases]: there [p a = pos ⊔ neg] and the
   join is a lub, so [ale (p a) t] follows from [ale pos t] and [ale neg t]. *)
Theorem complete_composes : forall a a1 a2,
  ceq (gamma a) (cjoin (gamma a1) (gamma a2)) ->
  ale (p a1) (gbest a1) -> ale (p a2) (gbest a2) ->
  ale (p a) (gbest a).
Proof.
  intros a a1 a2 Hcov H1 H2.
  eapply ale_trans; [ apply (proj1 (p_distributes a a1 a2 Hcov)) | ].
  eapply ale_trans; [ apply ajoin_mono; [ exact H1 | exact H2 ] | ].
  apply (proj2 (gbest_distributes a a1 a2 Hcov)).
Qed.

End Prop3.

End GaloisProps.
