(** * cartesian_propagators.v

    Proposition (paper, Interval Bound Propagation section):
      For any constraint c, the Cartesian propagator
          S^x[[c]]  =  alpha_x o S[[c]] o gamma_x
      (where S[[c]]P = P ∩ rel(c) is the concrete propagator) is a PROPAGATOR
      (reductive, monotone, sound, complete-on-singleton) and a CLOSURE
      OPERATOR (reductive, monotone, idempotent).

    This is a purely structural fact about the Galois connection
      P(Asn)  <alpha_x, gamma_x>  D          (D = X -> P(Val), pointwise)
    together with the fact that S[[c]] is a concrete lower closure operator.
    We model subsets as predicates.  Only [complete-on-singleton] needs a
    variable to sample (X inhabited) and functional extensionality. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import FunctionalExtensionality.

Section CartesianPropagators.

Context {X : Type}.          (* variables *)
Context {Val : Type}.        (* values (Z in the paper; nothing Z-specific is used) *)

Definition Asn := X -> Val.        (* assignments *)
Definition Con := Asn -> Prop.     (* concrete elements: sets of assignments *)
Definition Dom := X -> Val -> Prop. (* abstract: domain functions X -> P(Val) *)

(* orders (subset / pointwise inclusion) and their symmetric closures *)
Definition csub (P Q : Con) : Prop := forall a, P a -> Q a.
Definition ceq  (P Q : Con) : Prop := csub P Q /\ csub Q P.
Definition dle  (d d' : Dom) : Prop := forall x v, d x v -> d' x v.
Definition deq  (d d' : Dom) : Prop := dle d d' /\ dle d' d.

(* the Cartesian Galois connection *)
Definition alpha (P : Con) : Dom := fun x v => exists a, P a /\ a x = v.
Definition gamma (d : Dom) : Con := fun a => forall x, d x (a x).

(* concrete propagator S[[c]]P = P ∩ rel(c), and its Cartesian abstraction *)
Definition Sconc (rel : Con) (P : Con) : Con := fun a => P a /\ rel a.
Definition Sabs  (rel : Con) (d : Dom) : Dom := alpha (Sconc rel (gamma d)).

(* ------------------------------------------------------------------ *)
(** ** Galois connection and monotonicity building blocks              *)
(* ------------------------------------------------------------------ *)

Lemma galois : forall (P : Con) (d : Dom), dle (alpha P) d <-> csub P (gamma d).
Proof.
  intros P d. split.
  - intros H a Ha x. apply H. exists a. split; [exact Ha | reflexivity].
  - intros H x v [a [Ha Hax]]. subst v. apply H. exact Ha.
Qed.

Lemma alpha_mono : forall P Q, csub P Q -> dle (alpha P) (alpha Q).
Proof. intros P Q H x v [a [Ha Hax]]. exists a. split; [apply H; exact Ha | exact Hax]. Qed.

Lemma gamma_mono : forall d d', dle d d' -> csub (gamma d) (gamma d').
Proof. intros d d' H a Ha x. apply H. apply Ha. Qed.

(* the concrete closure is extensive: P is contained in gamma (alpha P) *)
Lemma extensive : forall P, csub P (gamma (alpha P)).
Proof. intros P a Ha x. exists a. split; [exact Ha | reflexivity]. Qed.

Lemma Sconc_mono : forall rel P Q, csub P Q -> csub (Sconc rel P) (Sconc rel Q).
Proof. intros rel P Q H a [HP Hr]. split; [apply H; exact HP | exact Hr]. Qed.

(* ------------------------------------------------------------------ *)
(** ** Propagator and closure-operator properties                      *)
(* ------------------------------------------------------------------ *)

Definition Reductive (p : Dom -> Dom) : Prop := forall d, dle (p d) d.
Definition Monotone  (p : Dom -> Dom) : Prop := forall d d', dle d d' -> dle (p d) (p d').
(* soundness: every solution of c in d survives  (sol(d,{c}) ⊆ sol(p d,{})) *)
Definition Sound (rel : Con) (p : Dom -> Dom) : Prop :=
  forall d a, rel a -> gamma d a -> gamma (p d) a.
Definition Idempotent (p : Dom -> Dom) : Prop := forall d, deq (p (p d)) (p d).
Definition singleton_dom (d : Dom) : Prop := forall x, exists v, forall w, d x w <-> w = v.
(* complete on singleton: on a singleton domain, p d detects the solutions *)
Definition CompleteSingleton (rel : Con) (p : Dom -> Dom) : Prop :=
  forall d, singleton_dom d -> forall a, gamma (p d) a -> (rel a /\ gamma d a).

Theorem Sabs_reductive : forall rel, Reductive (Sabs rel).
Proof. intros rel d x v [a [[Hgd Hrel] Hax]]. subst v. apply Hgd. Qed.

Theorem Sabs_monotone : forall rel, Monotone (Sabs rel).
Proof.
  intros rel d d' Hdd' x v [a [[Hgd Hrel] Hax]].
  exists a. split; [ split; [ apply (gamma_mono d d' Hdd'); exact Hgd | exact Hrel ] | exact Hax ].
Qed.

Theorem Sabs_sound : forall rel, Sound rel (Sabs rel).
Proof.
  intros rel d a Hrel Hgd x.
  exists a. split; [ split; [ exact Hgd | exact Hrel ] | reflexivity ].
Qed.

Theorem Sabs_idempotent : forall rel, Idempotent (Sabs rel).
Proof.
  intros rel d. split.
  - apply (Sabs_reductive rel (Sabs rel d)).
  - intros x v Hv. destruct Hv as [a [HP Hax]].
    exists a. split; [ split | exact Hax ].
    + exact (extensive (Sconc rel (gamma d)) a HP).
    + exact (proj2 HP).
Qed.

Theorem Sabs_complete_singleton : forall (x0 : X) rel, CompleteSingleton rel (Sabs rel).
Proof.
  intros x0 rel d Hsingle a Hga.
  assert (Hgd : gamma d a).
  { intro x. specialize (Hga x). destruct Hga as [a' [[Hgda' Hrela'] Ha'x]].
    rewrite <- Ha'x. apply Hgda'. }
  split; [ | exact Hgd ].
  specialize (Hga x0). destruct Hga as [a' [[Hgda' Hrela'] Ha'x0]].
  assert (Heq : a' = a).
  { apply functional_extensionality. intro x.
    destruct (Hsingle x) as [v Hv].
    assert (a' x = v) by (apply (proj1 (Hv (a' x))); apply Hgda').
    assert (a x = v) by (apply (proj1 (Hv (a x))); apply Hgd).
    congruence. }
  rewrite <- Heq. exact Hrela'.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Proposition 3 : complete-on-singleton is obtained for free.

    (Paper: "Let C, A be lattices with a Galois connection C <a,g> A and
     f in C -> C complete on singleton.  Any g in A -> A complete w.r.t. C,
     i.e. alpha o f o gamma >= g, is also complete on singleton.")

    We render it in the concrete Cartesian instance.  [singleton_con] is a
    singleton concrete element {rho}; [CompleteSingletonC] is the
    complete-on-singleton property of a map on the concrete lattice C = Con.
    The concrete propagator [Sconc rel] satisfies it trivially.

    [Prop3_general] proves the transfer for an ARBITRARY complete-on-singleton
    [f], choice-free (funext only), using the packaged singleton hypothesis
    [singleton_dom'] (= the point-domain of some assignment).
    [Prop3_complete_singleton_for_free] is the corollary actually used: with
    f = the concrete propagator, every g below the best transformer [Sabs rel]
    is complete on singleton, reusing [Sabs_complete_singleton] and the
    original [singleton_dom]. *)
(* ------------------------------------------------------------------ *)

(* a concrete element is a singleton iff it is the set {rho} *)
Definition singleton_con (P : Con) : Prop := exists rho, forall a, P a <-> a = rho.
(* a domain is a singleton iff it is the point-domain of some assignment *)
Definition singleton_dom' (d : Dom) : Prop := exists rho, forall x w, d x w <-> w = rho x.
(* complete-on-singleton for a map on the concrete lattice C *)
Definition CompleteSingletonC (rel : Con) (f : Con -> Con) : Prop :=
  forall P, singleton_con P -> forall a, f P a -> (rel a /\ P a).

(* the concretization of a singleton domain is a singleton set *)
Lemma singleton_con_gamma : forall d, singleton_dom' d -> singleton_con (gamma d).
Proof.
  intros d [rho Hrho]. exists rho. intro a. split.
  - intro Hga. apply functional_extensionality. intro x.
    apply (proj1 (Hrho x (a x))). apply Hga.
  - intro Ha. subst a. intro x. apply (proj2 (Hrho x (rho x))). reflexivity.
Qed.

(* the concrete propagator [Sconc rel] is trivially complete on singleton *)
Lemma Sconc_complete_singletonC : forall rel, CompleteSingletonC rel (Sconc rel).
Proof. intros rel P _ a [HP Hrel]. split; [ exact Hrel | exact HP ]. Qed.

(* Proposition 3, general f: complete-on-singleton transfers for free to any
   g below the best transformer [alpha o f o gamma].  Choice-free. *)
Theorem Prop3_general :
  forall (x0 : X) (rel : Con) (f : Con -> Con) (g : Dom -> Dom),
    CompleteSingletonC rel f ->
    (forall d, dle (g d) (alpha (f (gamma d)))) ->
    forall d, singleton_dom' d -> forall a, gamma (g d) a -> (rel a /\ gamma d a).
Proof.
  intros x0 rel f g Hf Hg d Hsingle a Hga.
  assert (Hsc : singleton_con (gamma d)) by (apply singleton_con_gamma; exact Hsingle).
  destruct Hsingle as [rho Hrho].
  (* push [a] through gamma_mono into gamma (alpha (f (gamma d))) *)
  assert (Halpha : gamma (alpha (f (gamma d))) a)
    by (apply (gamma_mono (g d) (alpha (f (gamma d))) (Hg d)); exact Hga).
  (* rho is the unique member of gamma d *)
  assert (Hrho_uniq : forall c, gamma d c -> c = rho).
  { intros c Hgc. apply functional_extensionality. intro x.
    apply (proj1 (Hrho x (c x))). apply Hgc. }
  assert (Hgrho : gamma d rho)
    by (intro x; apply (proj2 (Hrho x (rho x))); reflexivity).
  (* a = rho, extracted componentwise from Halpha via f's completeness *)
  assert (Harho : a = rho).
  { apply functional_extensionality. intro x.
    destruct (Halpha x) as [b [Hfb Hbx]].
    destruct (Hf (gamma d) Hsc b Hfb) as [_ Hgb].
    rewrite <- Hbx. rewrite (Hrho_uniq b Hgb). reflexivity. }
  subst a. split; [ | exact Hgrho ].
  (* rel rho : sample any f-witness (needs X inhabited) *)
  destruct (Halpha x0) as [b [Hfb _]].
  destruct (Hf (gamma d) Hsc b Hfb) as [Hrelb Hgb].
  rewrite (Hrho_uniq b Hgb) in Hrelb. exact Hrelb.
Qed.

(* Corollary (the paper's application): every g complete w.r.t. C -- i.e.
   below the best transformer [Sabs rel] -- is complete on singleton. *)
Theorem Prop3_complete_singleton_for_free :
  forall (x0 : X) (rel : Con) (g : Dom -> Dom),
    (forall d, dle (g d) (Sabs rel d)) -> CompleteSingleton rel g.
Proof.
  intros x0 rel g Hg d Hsingle a Hga.
  apply (Sabs_complete_singleton x0 rel d Hsingle a).
  apply (gamma_mono (g d) (Sabs rel d) (Hg d)). exact Hga.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The proposition: the Cartesian propagator is a propagator AND a
       closure operator (variables assumed inhabited for singleton case). *)
(* ------------------------------------------------------------------ *)

Theorem Sabs_propagator_and_closure : forall (x0 : X) rel,
  (* a propagator (Def. 1) *)
  (Reductive (Sabs rel) /\ Monotone (Sabs rel) /\ Sound rel (Sabs rel)
   /\ CompleteSingleton rel (Sabs rel))
  /\ (* a closure operator *)
  (Reductive (Sabs rel) /\ Monotone (Sabs rel) /\ Idempotent (Sabs rel)).
Proof.
  intros x0 rel. split.
  - split; [ apply Sabs_reductive
           | split; [ apply Sabs_monotone
                    | split; [ apply Sabs_sound | apply (Sabs_complete_singleton x0) ] ] ].
  - split; [ apply Sabs_reductive | split; [ apply Sabs_monotone | apply Sabs_idempotent ] ].
Qed.

End CartesianPropagators.
