From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.
From LalaInterval Require Import Concrete.

(** I. Z with infinities with lattice operations. *)

Inductive zinf : Type := Fin (v : Z) | Pinf | Ninf.

Definition leq_zinf (a b : zinf) : Prop :=
  match a, b with
  | Ninf, _ => True
  | _, Pinf => True
  | Fin x, Fin y => x <= y
  | _, _ => False
  end.

Definition leqb_zinf (a b : zinf) : bool :=
  match a, b with
  | Ninf, _ => true
  | _, Pinf => true
  | Fin x, Fin y => x <=? y
  | _, _ => false
  end.

Lemma leq_zinf_prop_bool_equiv : forall a b, leqb_zinf a b = true <-> leq_zinf a b.
Proof.
  intros [x| |] [y| |]; cbn; try (split; auto; discriminate).
  apply Z.leb_le.
Qed.

Definition min_zinf (a b : zinf) : zinf :=
  match a, b with
  | Ninf, _ | _, Ninf => Ninf
  | Pinf, x => x
  | x, Pinf => x
  | Fin x, Fin y => Fin (Z.min x y)
  end.

Definition max_zinf (a b : zinf) : zinf :=
  match a, b with
  | Pinf, _ | _, Pinf => Pinf
  | Ninf, x => x
  | x, Ninf => x
  | Fin x, Fin y => Fin (Z.max x y)
  end.

(** II. Infinity-aware arithmetic *)

Definition add_zinf (a b : zinf) : zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x + y)
  | Pinf, _ => Pinf
  | Ninf, _ => Ninf
  | _, Pinf => Pinf
  | _, Ninf => Ninf
  end.

Definition sub_zinf (a b : zinf) : zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x - y)
  | Pinf, _ => Pinf
  | Ninf, _ => Ninf
  | _, Pinf => Ninf
  | _, Ninf => Pinf
  end.

(* saturating addition of a finite shift *)
Definition addk_zinf (a : zinf) (k : Z) : zinf :=
  match a with Fin v => Fin (v + k) | x => x end.

(* multiplication: sign rule with 0 * oo = 0 *)
Definition mul_zinf (a b : zinf) : zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x * y)
  | Pinf, Fin y => if y =? 0 then Fin 0 else if 0 <? y then Pinf else Ninf
  | Ninf, Fin y => if y =? 0 then Fin 0 else if 0 <? y then Ninf else Pinf
  | Fin x, Pinf => if x =? 0 then Fin 0 else if 0 <? x then Pinf else Ninf
  | Fin x, Ninf => if x =? 0 then Fin 0 else if 0 <? x then Ninf else Pinf
  | Pinf, Pinf => Pinf
  | Ninf, Ninf => Pinf
  | Pinf, Ninf => Ninf
  | Ninf, Pinf => Ninf
  end.

(* floor(n/m) with limit semantics (precondition of use: m <> Fin 0).
   Infinite divisor: the eventual value of floor(n/z) -- 0 if the signs
   agree, -1 otherwise; uniformly safe in every corner min/max. *)
Definition fdiv_zinf (n m : zinf) : zinf :=
  match m with
  | Pinf => match n with
            | Fin v => Fin (if v <? 0 then -1 else 0)
            | Pinf => Fin 0
            | Ninf => Fin (-1)
            end
  | Ninf => match n with
            | Fin v => Fin (if 0 <? v then -1 else 0)
            | Pinf => Fin (-1)
            | Ninf => Fin 0
            end
  | Fin w => match n with
             | Fin v => Fin (v / w)
             | Pinf => if 0 <? w then Pinf else Ninf
             | Ninf => if 0 <? w then Ninf else Pinf
             end
  end.

(* ceil(n/m) with limit semantics (precondition of use: m <> Fin 0). *)
Definition cdiv_zinf (n m : zinf) : zinf :=
  match m with
  | Pinf => match n with
            | Fin v => Fin (if 0 <? v then 1 else 0)
            | Pinf => Fin 1
            | Ninf => Fin 0
            end
  | Ninf => match n with
            | Fin v => Fin (if v <? 0 then 1 else 0)
            | Pinf => Fin 0
            | Ninf => Fin 1
            end
  | Fin w => match n with
             | Fin v => Fin (cdiv v w)
             | Pinf => if 0 <? w then Pinf else Ninf
             | Ninf => if 0 <? w then Ninf else Pinf
             end
  end.

(* sign tests on zinf *)

Definition ispos_zinf (a : zinf) : bool :=
  match a with Fin v => 0 <? v | Pinf => true | Ninf => false end.
Definition isneg_zinf (a : zinf) : bool :=
  match a with Fin v => v <? 0 | Pinf => false | Ninf => true end.
Definition iszero_zinf (a : zinf) : bool :=
  match a with Fin v => v =? 0 | _ => false end.
Definition geq0_zinf (a : zinf) : bool :=
  match a with Fin v => 0 <=? v | Pinf => true | Ninf => false end.
Definition leq0_zinf (a : zinf) : bool :=
  match a with Fin v => v <=? 0 | Pinf => false | Ninf => true end.

(* ------------------------------------------------------------------ *)
(** ** Order and arithmetic lemmas                                     *)
(* ------------------------------------------------------------------ *)

Lemma leq_zinf_refl : forall a, leq_zinf a a.
Proof. intros [v| |]; cbn; try exact I; lia. Qed.

Lemma leq_zinf_trans : forall a b c, leq_zinf a b -> leq_zinf b c -> leq_zinf a c.
Proof. intros [x| |] [y| |] [z| |]; cbn; try tauto; lia. Qed.

Lemma leq_zinf_max_zinf_l : forall a b, leq_zinf a (max_zinf a b).
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.

Lemma leq_zinf_min_zinf_l : forall a b, leq_zinf (min_zinf a b) a.
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.

Lemma leq_zinf_min_zinf_glb : forall a b c, leq_zinf c a -> leq_zinf c b -> leq_zinf c (min_zinf a b).
Proof. intros [x| |] [y| |] [z| |]; cbn; try tauto; lia. Qed.

Lemma max_zinf_lub : forall a b c, leq_zinf a c -> leq_zinf b c -> leq_zinf (max_zinf a b) c.
Proof. intros [x| |] [y| |] [z| |]; cbn; try tauto; lia. Qed.

Lemma add_zinf_ub : forall a b u v,
  leq_zinf a (Fin u) -> leq_zinf b (Fin v) -> leq_zinf (add_zinf a b) (Fin (u + v)).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma add_zinf_lb : forall a b u v,
  leq_zinf (Fin u) a -> leq_zinf (Fin v) b -> leq_zinf (Fin (u + v)) (add_zinf a b).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma sub_zinf_ub : forall a b u v,
  leq_zinf a (Fin u) -> leq_zinf (Fin v) b -> leq_zinf (sub_zinf a b) (Fin (u - v)).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma sub_zinf_lb : forall a b u v,
  leq_zinf (Fin u) a -> leq_zinf b (Fin v) -> leq_zinf (Fin (u - v)) (sub_zinf a b).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma max_zinf_mono : forall a b c d, leq_zinf a b -> leq_zinf c d -> leq_zinf (max_zinf a c) (max_zinf b d).
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma min_zinf_mono : forall a b c d, leq_zinf a b -> leq_zinf c d -> leq_zinf (min_zinf a c) (min_zinf b d).
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma add_zinf_monotone : forall a a' b b',
  leq_zinf a a' -> leq_zinf b b' -> leq_zinf (add_zinf a b) (add_zinf a' b').
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma sub_zinf_monotone : forall a a' b b',
  leq_zinf a a' -> leq_zinf b' b -> leq_zinf (sub_zinf a b) (sub_zinf a' b').
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.
