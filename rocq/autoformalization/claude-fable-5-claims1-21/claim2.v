(* ========================================================================= *)
(* Claim 2:                                                                  *)
(* "The structure D = ⟨(X → P(Z))/∼×, ≤⟩ is a complete lattice where the     *)
(*  order is defined pointwise with care for the bottom equivalence class    *)
(*  (d ≤ d' ≜ isbot×(d) ∨ ∀x ∈ X, d(x) ⊆ d'(x))."                            *)
(*                                                                           *)
(* We formalize quotient lattices as ordered setoids: a carrier equipped     *)
(* with an equivalence relation oeq (the quotient identification) and an     *)
(* order ole which is reflexive w.r.t. oeq, transitive, and antisymmetric    *)
(* up to oeq.  A complete lattice is an ordered setoid where every subset    *)
(* of the carrier has a least upper bound and a greatest lower bound.        *)
(*                                                                           *)
(* This file also provides the generic lattice-theoretic infrastructure     *)
(* (ordered setoids, complete lattices, existence of infima from suprema)   *)
(* used by the later claims.                                                 *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical.
From Paper Require Import claim1.

(* ---------- Ordered setoids ---------- *)

Record OSet : Type := MkOSet {
  oc : Type;
  oeq : oc -> oc -> Prop;
  ole : oc -> oc -> Prop;
  oeq_refl : forall x, oeq x x;
  oeq_sym : forall x y, oeq x y -> oeq y x;
  oeq_trans : forall x y z, oeq x y -> oeq y z -> oeq x z;
  ole_refl : forall x y, oeq x y -> ole x y;
  ole_trans : forall x y z, ole x y -> ole y z -> ole x z;
  ole_antisym : forall x y, ole x y -> ole y x -> oeq x y
}.

Arguments oeq {o}.
Arguments ole {o}.
Arguments oeq_refl {o}.
Arguments oeq_sym {o}.
Arguments oeq_trans {o}.
Arguments ole_refl {o}.
Arguments ole_trans {o}.
Arguments ole_antisym {o}.

Lemma ole_refl' : forall (A : OSet) (x : oc A), ole x x.
Proof. intros A x. apply ole_refl, oeq_refl. Qed.

(* Rewriting along oeq on both sides of ole. *)
Lemma ole_eq_l : forall (A : OSet) (x x' y : oc A),
  oeq x x' -> ole x' y -> ole x y.
Proof. intros A x x' y He Hl. eapply ole_trans; [apply ole_refl; exact He|exact Hl]. Qed.

Lemma ole_eq_r : forall (A : OSet) (x y y' : oc A),
  oeq y y' -> ole x y' -> ole x y.
Proof.
  intros A x y y' He Hl. eapply ole_trans; [exact Hl|apply ole_refl; apply oeq_sym; exact He].
Qed.

(* ---------- Least upper bounds / greatest lower bounds ---------- *)

Definition upper_bound (A : OSet) (S : oc A -> Prop) (b : oc A) : Prop :=
  forall x, S x -> ole x b.
Definition lower_bound (A : OSet) (S : oc A -> Prop) (b : oc A) : Prop :=
  forall x, S x -> ole b x.
Definition is_lub (A : OSet) (S : oc A -> Prop) (l : oc A) : Prop :=
  upper_bound A S l /\ forall b, upper_bound A S b -> ole l b.
Definition is_glb (A : OSet) (S : oc A -> Prop) (g : oc A) : Prop :=
  lower_bound A S g /\ forall b, lower_bound A S b -> ole b g.

(* A complete lattice, as a property of an ordered setoid. *)
Definition complete_lattice (A : OSet) : Prop :=
  forall S : oc A -> Prop, (exists l, is_lub A S l) /\ (exists g, is_glb A S g).

(* Least upper bounds are unique up to oeq. *)
Lemma is_lub_unique : forall (A : OSet) S l l',
  is_lub A S l -> is_lub A S l' -> oeq l l'.
Proof.
  intros A S l l' [Hub Hl] [Hub' Hl'].
  apply ole_antisym; [apply Hl, Hub' | apply Hl', Hub].
Qed.

(* ---------- Complete lattices as structures (sup only) ---------- *)
(* Every subset has a lub; the existence of glbs is a theorem
   (glb S = lub of the lower bounds of S). *)

Record CompleteLattice : Type := MkCL {
  cl_os : OSet;
  csup : (oc cl_os -> Prop) -> oc cl_os;
  csup_ub : forall S x, S x -> ole x (csup S);
  csup_least : forall S b, upper_bound cl_os S b -> ole (csup S) b
}.

Arguments csup {c}.
Arguments csup_ub {c}.
Arguments csup_least {c}.

Definition cinf (L : CompleteLattice) (S : oc (cl_os L) -> Prop) : oc (cl_os L) :=
  csup (lower_bound (cl_os L) S).

Lemma cinf_lb : forall (L : CompleteLattice) S, lower_bound (cl_os L) S (cinf L S).
Proof.
  intros L S x Hx. apply csup_least. intros y Hy. apply Hy. exact Hx.
Qed.

Lemma cinf_greatest : forall (L : CompleteLattice) S b,
  lower_bound (cl_os L) S b -> ole b (cinf L S).
Proof. intros L S b Hb. apply csup_ub. exact Hb. Qed.

Lemma csup_is_lub : forall (L : CompleteLattice) S, is_lub (cl_os L) S (csup S).
Proof. intros L S. split; [intros x Hx; apply csup_ub; exact Hx | apply csup_least]. Qed.

Lemma cinf_is_glb : forall (L : CompleteLattice) S, is_glb (cl_os L) S (cinf L S).
Proof. intros L S. split; [apply cinf_lb | apply cinf_greatest]. Qed.

(* Any CompleteLattice structure witnesses the complete_lattice property. *)
Theorem CompleteLattice_complete : forall (L : CompleteLattice),
  complete_lattice (cl_os L).
Proof.
  intros L S. split.
  - exists (csup S). apply csup_is_lub.
  - exists (cinf L S). apply cinf_is_glb.
Qed.

(* Top and bottom. *)
Definition ctop (L : CompleteLattice) : oc (cl_os L) := csup (fun _ => True).
Definition cbot (L : CompleteLattice) : oc (cl_os L) := csup (fun _ => False).

Lemma ctop_greatest : forall (L : CompleteLattice) x, ole x (ctop L).
Proof. intros L x. apply csup_ub. exact I. Qed.

Lemma cbot_least : forall (L : CompleteLattice) x, ole (cbot L) x.
Proof. intros L x. apply csup_least. intros y []. Qed.

(* ---------- The powerset ordered setoid ---------- *)

Definition PowOSet (T : Type) : OSet.
Proof.
  refine (MkOSet (powerset T) set_eq subset _ _ _ _ _ _).
  - intros P t; tauto.
  - intros P Q H t. specialize (H t); tauto.
  - intros P Q R H1 H2 t. specialize (H1 t); specialize (H2 t); tauto.
  - intros P Q H t. specialize (H t); tauto.
  - intros P Q R H1 H2 t HP. auto.
  - intros P Q H1 H2 t. split; auto.
Defined.

(* The powerset complete lattice (used for the concrete domain P(Asn)). *)
Definition PowCL (T : Type) : CompleteLattice.
Proof.
  refine (MkCL (PowOSet T)
            (fun S => fun t => exists P, S P /\ P t) _ _).
  - intros S P HP t Ht. exists P. auto.
  - intros S b Hub t [P [HP Ht]]. exact (Hub P HP t Ht).
Defined.

(* ================= The Cartesian domain D ================= *)

Section CartesianDomain.
  Context (X : Type).

  Definition domfun : Type := X -> powerset Z.

  (* Failed domain functions: some variable has an empty domain. *)
  Definition isbotx (d : domfun) : Prop := exists x, forall v, ~ d x v.

  (* The quotient identification ∼× and the order of the paper. *)
  Definition eqD (d d' : domfun) : Prop :=
    (isbotx d /\ isbotx d') \/ (forall x v, d x v <-> d' x v).
  Definition leD (d d' : domfun) : Prop :=
    isbotx d \/ (forall x v, d x v -> d' x v).

  Lemma isbotx_eq : forall d d',
    (forall x v, d x v <-> d' x v) -> isbotx d -> isbotx d'.
  Proof.
    intros d d' Hiff [x Hx]. exists x. intros v Hv. apply (Hx v), Hiff, Hv.
  Qed.

  Lemma isbotx_le : forall d d',
    (forall x v, d' x v -> d x v) -> isbotx d -> isbotx d'.
  Proof.
    intros d d' Hsub [x Hx]. exists x. intros v Hv. apply (Hx v), Hsub, Hv.
  Qed.

  Definition D_OSet : OSet.
  Proof.
    refine (MkOSet domfun eqD leD _ _ _ _ _ _).
    - intros d. right. tauto.
    - intros d d' [[H1 H2]|H]; [left; tauto | right; intros x v; specialize (H x v); tauto].
    - intros d d' d'' [[H1 H2]|H] [[H3 H4]|H'].
      + left; tauto.
      + left. split; [exact H1|]. eapply isbotx_eq; eauto.
      + left. split; [|exact H4].
        eapply isbotx_eq; [|exact H3]. intros x v. specialize (H x v); tauto.
      + right. intros x v. specialize (H x v); specialize (H' x v); tauto.
    - intros d d' [[H1 H2]|H]; [left; exact H1 | right; intros x v; apply H].
    - intros d d' d'' [H|H] [H'|H'].
      + left; exact H.
      + left; exact H.
      + left. eapply isbotx_le; [|exact H']. intros x v; apply H.
      + right. intros x v Hv. apply H', H, Hv.
    - intros d d' [H|H] [H'|H'].
      + left. split; assumption.
      + left. split; [exact H|]. eapply isbotx_le; [intros x v; apply H'|exact H].
      + left. split; [eapply isbotx_le; [intros x v; apply H|exact H']|exact H'].
      + right. intros x v. split; [apply H|apply H'].
  Defined.

  (* Supremum: pointwise union over the non-failed members. *)
  Definition supD (S : domfun -> Prop) : domfun :=
    fun x v => exists d, S d /\ ~ isbotx d /\ d x v.

  Definition D_CL : CompleteLattice.
  Proof.
    refine (MkCL D_OSet supD _ _).
    - (* upper bound *)
      intros S d HdS.
      destruct (classic (isbotx d)) as [Hbot|Hbot].
      + left; exact Hbot.
      + right. intros x v Hv. exists d. auto.
    - (* least *)
      intros S b Hub. right.
      intros x v [d [HdS [Hnb Hv]]].
      destruct (Hub d HdS) as [Hbot|Hle]; [contradiction | apply Hle, Hv].
  Defined.

End CartesianDomain.

(* ======================= CLAIM 2 ======================= *)
(* D = ⟨(X → P(Z))/∼×, ≤⟩ is a complete lattice. *)
Theorem claim2 : forall (X : Type), complete_lattice (D_OSet X).
Proof.
  intros X. exact (CompleteLattice_complete (D_CL X)).
Qed.
