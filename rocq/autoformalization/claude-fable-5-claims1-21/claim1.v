(* ========================================================================= *)
(* Claim 1:                                                                  *)
(* "Note that because each constraint removes all unsatisfiable assignments, *)
(*  we reach the fixpoint after one iteration, that is, the composition     *)
(*  S[c1] ∘ ... ∘ S[cn] is itself a closure operator."                       *)
(*                                                                           *)
(* This file also introduces the base definitions shared by later claims:   *)
(* the concrete domain P(Asn), the constraint language of the paper         *)
(* (x = y ⊙ z with ⊙ ∈ {+,-,*,fdiv,cdiv,tdiv,ediv}), the solution sets      *)
(* rel(c), and the concrete propagators S[c]P = P ∩ rel(c).                  *)
(*                                                                           *)
(* Closure operators here follow the paper's convention: idempotent,        *)
(* monotone and *reductive* (S[c]P ⊆ P).                                     *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia List FunctionalExtensionality PropExtensionality.
Import ListNotations.
Open Scope Z_scope.

(* ---------- Sets ---------- *)

Definition powerset (T : Type) := T -> Prop.
Definition subset {T : Type} (P Q : powerset T) : Prop := forall t, P t -> Q t.
Definition set_eq {T : Type} (P Q : powerset T) : Prop := forall t, P t <-> Q t.
Definition inter {T : Type} (P Q : powerset T) : powerset T := fun t => P t /\ Q t.

Lemma set_ext {T : Type} (P Q : powerset T) : set_eq P Q -> P = Q.
Proof.
  intros H. apply functional_extensionality; intro t.
  apply propositional_extensionality, H.
Qed.

Lemma subset_refl {T : Type} (P : powerset T) : subset P P.
Proof. intros t H; exact H. Qed.

Lemma subset_trans {T : Type} (P Q R : powerset T) :
  subset P Q -> subset Q R -> subset P R.
Proof. intros H1 H2 t H; auto. Qed.

Lemma subset_antisym {T : Type} (P Q : powerset T) :
  subset P Q -> subset Q P -> P = Q.
Proof. intros H1 H2. apply set_ext; intro t; split; auto. Qed.

(* ---------- Assignments ---------- *)

Definition Asn (X : Type) := X -> Z.

(* ---------- The four integer divisions ---------- *)
(* fdivZ is the floor division (rounding toward -∞): this is exactly Coq's
   Z.div.  cdivZ is the ceiling division, tdivZ the truncated division
   (floor of the real quotient when y/z >= 0, i.e. when y*z >= 0, and
   ceiling otherwise), and edivZ the Euclidean division (floor when z > 0,
   ceiling when z < 0). *)

Definition fdivZ (y z : Z) : Z := y / z.
Definition cdivZ (y z : Z) : Z := - ((- y) / z).
Definition tdivZ (y z : Z) : Z := if 0 <=? y * z then fdivZ y z else cdivZ y z.
Definition edivZ (y z : Z) : Z := if 0 <? z then fdivZ y z else cdivZ y z.

(* Sanity check: tdivZ coincides with Coq's truncated division Z.quot. *)
Lemma tdivZ_quot : forall y z, z <> 0 -> tdivZ y z = Z.quot y z.
Proof.
  intros y z Hz. unfold tdivZ, fdivZ, cdivZ.
  destruct (Z.leb_spec 0 (y * z)) as [H|H].
  - (* same signs: quot = div *)
    destruct (Z.lt_trichotomy y 0) as [Hy|[Hy|Hy]].
    + (* y < 0, hence z < 0 since y*z >= 0 *)
      assert (Hz' : z < 0) by nia.
      rewrite <- (Z.opp_involutive y), <- (Z.opp_involutive z).
      rewrite Z.quot_opp_opp, Z.div_opp_opp by lia.
      symmetry; apply Z.quot_div_nonneg; lia.
    + subst y. rewrite Z.quot_0_l, Z.div_0_l by lia. reflexivity.
    + assert (Hz' : z > 0) by nia.
      symmetry; apply Z.quot_div_nonneg; lia.
  - (* opposite signs: quot = ceiling division *)
    destruct (Z.lt_trichotomy y 0) as [Hy|[Hy|Hy]].
    + assert (Hz' : z > 0) by nia.
      rewrite <- (Z.opp_involutive y) at 2.
      rewrite Z.quot_opp_l by lia.
      f_equal. symmetry; apply Z.quot_div_nonneg; lia.
    + subst y. nia.
    + assert (Hz' : z < 0) by nia.
      rewrite <- (Z.opp_involutive z) at 2.
      rewrite Z.quot_opp_r by lia.
      f_equal.
      rewrite Z.quot_div_nonneg by lia.
      rewrite <- (Z.div_opp_opp y (- z)) by lia.
      rewrite Z.opp_involutive. reflexivity.
Qed.

(* ---------- Constraints of the paper: x = y ⊙ z ---------- *)

Inductive op : Type := OAdd | OSub | OMul | OFdiv | OCdiv | OTdiv | OEdiv.

Record constraint (X : Type) : Type := MkC { cx : X; cy : X; cz : X; cop : op }.
Arguments MkC {X}.
Arguments cx {X}.
Arguments cy {X}.
Arguments cz {X}.
Arguments cop {X}.

Definition op_rel (o : op) (vx vy vz : Z) : Prop :=
  match o with
  | OAdd => vx = vy + vz
  | OSub => vx = vy - vz
  | OMul => vx = vy * vz
  | OFdiv => vz <> 0 /\ vx = fdivZ vy vz
  | OCdiv => vz <> 0 /\ vx = cdivZ vy vz
  | OTdiv => vz <> 0 /\ vx = tdivZ vy vz
  | OEdiv => vz <> 0 /\ vx = edivZ vy vz
  end.

(* The solution set of a constraint. *)
Definition rel {X : Type} (c : constraint X) : powerset (Asn X) :=
  fun a => op_rel (cop c) (a (cx c)) (a (cy c)) (a (cz c)).

(* ---------- Concrete propagators ---------- *)

Definition csem {X : Type} (c : constraint X) (P : powerset (Asn X))
  : powerset (Asn X) := inter P (rel c).

(* ---------- Closure operators (paper convention: reductive) ---------- *)

Section Closure.
  Context {T : Type}.

  Definition monotoneS (f : powerset T -> powerset T) : Prop :=
    forall P Q, subset P Q -> subset (f P) (f Q).
  Definition reductiveS (f : powerset T -> powerset T) : Prop :=
    forall P, subset (f P) P.
  Definition idempotentS (f : powerset T -> powerset T) : Prop :=
    forall P, f (f P) = f P.

  Definition closure_operatorS (f : powerset T -> powerset T) : Prop :=
    idempotentS f /\ monotoneS f /\ reductiveS f.
End Closure.

(* Each individual concrete propagator is a closure operator. *)
Lemma csem_closure : forall (X : Type) (c : constraint X),
  closure_operatorS (csem c).
Proof.
  intros X c. split; [|split].
  - intro P. apply set_ext; intro a. unfold csem, inter. tauto.
  - intros P Q H a [HP Hr]. split; auto.
  - intros P a [HP _]. exact HP.
Qed.

(* Composition S[c1] ∘ ... ∘ S[cn]. *)
Fixpoint compose_all {X : Type} (cs : list (constraint X))
  (P : powerset (Asn X)) : powerset (Asn X) :=
  match cs with
  | [] => P
  | c :: tl => csem c (compose_all tl P)
  end.

Lemma compose_all_spec :
  forall (X : Type) (cs : list (constraint X)) (P : powerset (Asn X)) a,
    compose_all cs P a <-> P a /\ (forall c, In c cs -> rel c a).
Proof.
  intros X cs P a. induction cs as [|c tl IH]; simpl.
  - tauto.
  - unfold csem, inter. rewrite IH. split.
    + intros [[HP Hall] Hc]. split; [exact HP|].
      intros c' [->|Hin]; auto.
    + intros [HP Hall]. repeat split; auto.
Qed.

(* ======================= CLAIM 1 ======================= *)
Theorem claim1 : forall (X : Type) (cs : list (constraint X)),
  closure_operatorS (compose_all cs).
Proof.
  intros X cs. split; [|split].
  - (* idempotent: fixpoint reached after one iteration *)
    intro P. apply set_ext; intro a.
    rewrite !compose_all_spec. tauto.
  - (* monotone *)
    intros P Q H a. rewrite !compose_all_spec. intuition auto.
  - (* reductive *)
    intros P a. rewrite compose_all_spec. tauto.
Qed.

(* The paper phrases "the fixpoint is reached after one iteration" as the
   composed operator being idempotent; we also record it explicitly. *)
Corollary claim1_one_iteration :
  forall (X : Type) (cs : list (constraint X)) (P : powerset (Asn X)),
    compose_all cs (compose_all cs P) = compose_all cs P.
Proof. intros X cs P. destruct (claim1 X cs) as [Hid _]. apply Hid. Qed.
