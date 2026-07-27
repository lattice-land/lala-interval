(* ========================================================================= *)
(* Claim 4:                                                                  *)
(* The example Cartesian propagator for the multiplication constraint        *)
(*   S×'[x = y·z]d ≜ d[x ↦ X, y ↦ Y, z ↦ Z]                                  *)
(*     X = {a ∈ d(x) | ∃b ∈ d(y), ∃c ∈ d(z), a = b·c}                        *)
(*     Y = {b ∈ d(y) | ∃a ∈ d(x), ∃c ∈ d(z), a = b·c}                        *)
(*     Z = {c ∈ d(z) | ∃a ∈ d(x), ∃b ∈ d(y), a = b·c}                        *)
(* is equivalent (in the quotient D, i.e. up to ∼×) to the best Cartesian    *)
(* propagator S×[x = y·z] = α× ∘ S[x = y·z] ∘ γ×.                            *)
(*                                                                           *)
(* We use a three-variable set X = {x, y, z} (the scope of the constraint),  *)
(* the variables being pairwise distinct.                                    *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia.
From Paper Require Import claim1 claim2 claim3.
Open Scope Z_scope.

(* The three variables of a constraint x = y ⊙ z. *)
Inductive V3 : Type := Vx | Vy | Vz.

Definition V3_eq_dec : forall (a b : V3), {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* Building an assignment over V3 from three values. *)
Definition asn3 (vx vy vz : Z) : Asn V3 :=
  fun w => match w with Vx => vx | Vy => vy | Vz => vz end.

(* The multiplication constraint x = y·z over V3. *)
Definition cmul : constraint V3 := MkC Vx Vy Vz OMul.

(* The best Cartesian propagator: S×[c] = α× ∘ S[c] ∘ γ×. *)
Definition bestX (c : constraint V3) (d : domfun V3) : domfun V3 :=
  alphaX V3 (csem c (gammaX V3 d)).

(* The example propagator S×' of the paper. *)
Definition mulpropX (d : domfun V3) : domfun V3 :=
  fun w => match w with
  | Vx => fun a => d Vx a /\ exists b c, d Vy b /\ d Vz c /\ a = b * c
  | Vy => fun b => d Vy b /\ exists a c, d Vx a /\ d Vz c /\ a = b * c
  | Vz => fun c => d Vz c /\ exists a b, d Vx a /\ d Vy b /\ a = b * c
  end.

(* ======================= CLAIM 4 ======================= *)
(* The example propagator and the best propagator are equivalent, i.e. they
   denote the same element of the quotient lattice D.  (In fact they agree
   pointwise.) *)
Theorem claim4 : forall (d : domfun V3),
  eqD V3 (mulpropX d) (bestX cmul d).
Proof.
  intros d. right. intros w v.
  destruct w; simpl; unfold bestX, alphaX, csem, inter, gammaX, rel; simpl.
  - (* w = Vx *)
    split.
    + intros [Hx [b [c [Hy [Hz Hv]]]]].
      exists (asn3 v b c). repeat split; simpl.
      * intros w; destruct w; simpl; assumption.
      * exact Hv.
    + intros [asn [[Hbox Hrel] Heq]].
      subst v. split; [apply Hbox|].
      exists (asn Vy), (asn Vz). repeat split; try apply Hbox. exact Hrel.
  - (* w = Vy *)
    split.
    + intros [Hy [a [c [Hx [Hz Hv]]]]].
      exists (asn3 a v c). repeat split; simpl.
      * intros w; destruct w; simpl; assumption.
      * exact Hv.
    + intros [asn [[Hbox Hrel] Heq]].
      subst v. split; [apply Hbox|].
      exists (asn Vx), (asn Vz). repeat split; try apply Hbox. exact Hrel.
  - (* w = Vz *)
    split.
    + intros [Hz [a [b [Hx [Hy Hv]]]]].
      exists (asn3 a b v). repeat split; simpl.
      * intros w; destruct w; simpl; assumption.
      * exact Hv.
    + intros [asn [[Hbox Hrel] Heq]].
      subst v. split; [apply Hbox|].
      exists (asn Vx), (asn Vy). repeat split; try apply Hbox. exact Hrel.
Qed.
