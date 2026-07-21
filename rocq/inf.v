From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.
From LalaInterval Require Import Lemmas.



(* ------------------------------------------------------------------ *)
(** ** Z with infinities                                                *)
(* ------------------------------------------------------------------ *)

Inductive Zinf : Type := Fin (v : Z) | Pinf | Ninf.

Definition zle (a b : Zinf) : Prop :=
  match a, b with
  | Ninf, _ => True
  | _, Pinf => True
  | Fin x, Fin y => x <= y
  | _, _ => False
  end.

Definition zleb (a b : Zinf) : bool :=
  match a, b with
  | Ninf, _ => true
  | _, Pinf => true
  | Fin x, Fin y => x <=? y
  | _, _ => false
  end.

Lemma zleb_zle : forall a b, zleb a b = true <-> zle a b.
Proof.
  intros [x| |] [y| |]; cbn; try (split; auto; discriminate).
  apply Z.leb_le.
Qed.

Definition zmin (a b : Zinf) : Zinf :=
  match a, b with
  | Ninf, _ | _, Ninf => Ninf
  | Pinf, x => x
  | x, Pinf => x
  | Fin x, Fin y => Fin (Z.min x y)
  end.

Definition zmax (a b : Zinf) : Zinf :=
  match a, b with
  | Pinf, _ | _, Pinf => Pinf
  | Ninf, x => x
  | x, Ninf => x
  | Fin x, Fin y => Fin (Z.max x y)
  end.

(* ------------------------------------------------------------------ *)
(** ** Infinity-aware arithmetic (mirrors the C++ helpers)             *)
(* ------------------------------------------------------------------ *)

(* saturating addition of a finite shift *)
Definition sadd3 (a : Zinf) (k : Z) : Zinf :=
  match a with Fin v => Fin (v + k) | x => x end.

(* multiplication: sign rule with 0 * oo = 0 *)
Definition imul3 (a b : Zinf) : Zinf :=
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
Definition idivf3 (n m : Zinf) : Zinf :=
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
Definition idivc3 (n m : Zinf) : Zinf :=
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




(* sign tests on Zinf *)
Definition zpos (a : Zinf) : bool :=
  match a with Fin v => 0 <? v | Pinf => true | Ninf => false end.
Definition zneg (a : Zinf) : bool :=
  match a with Fin v => v <? 0 | Pinf => false | Ninf => true end.
Definition ziszero (a : Zinf) : bool :=
  match a with Fin v => v =? 0 | _ => false end.
Definition zge0 (a : Zinf) : bool :=
  match a with Fin v => 0 <=? v | Pinf => true | Ninf => false end.
Definition zle0 (a : Zinf) : bool :=
  match a with Fin v => v <=? 0 | Pinf => false | Ninf => true end.



(* ------------------------------------------------------------------ *)
(** ** Helper lemmas for reductivity                                    *)
(* ------------------------------------------------------------------ *)

Lemma zle_refl : forall a, zle a a.
Proof. intros [v| |]; cbn; try exact I; lia. Qed.

Lemma zle_trans : forall a b c, zle a b -> zle b c -> zle a c.
Proof. intros [x| |] [y| |] [z| |]; cbn; try tauto; lia. Qed.

Lemma zle_zmax_l : forall a b, zle a (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.

Lemma zmin_zle_l : forall a b, zle (zmin a b) a.
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.

Lemma zle_zmin_glb : forall a b c, zle c a -> zle c b -> zle c (zmin a b).
Proof. intros [x| |] [y| |] [z| |]; cbn; try tauto; lia. Qed.

Lemma zmax_lub : forall a b c, zle a c -> zle b c -> zle (zmax a b) c.
Proof. intros [x| |] [y| |] [z| |]; cbn; try tauto; lia. Qed.