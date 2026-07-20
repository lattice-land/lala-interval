(** * equivcpp.v : C++-faithful rendering of the infinity-aware helpers.

    The lala C++ code defines extended-integer multiplication compactly as
      imul(a, b) :=
        if a,b both finite         : a * b
        else if a = 0 or b = 0     : 0
        else                       : same_sign(a, b) ? +oo : -oo
      same_sign(x, y) := (x < 0) == (y < 0)
    over a machine type where +oo/-oo are sentinel values.

    [itv.v]'s [imul3] instead spells out all nine constructor pairs, which
    reduces cleanly under [cbn] in the propagator proofs.  Here we give the
    compact rendering [imul3'] (matching the C++ line for line, using the
    [zneg] "< 0" test since [Zinf] is not a single numeric type) and prove it
    is extensionally the SAME function as [imul3]. *)

From Stdlib Require Import ZArith Bool Lia.
From LalaInterval Require Import itv zdiv.
Open Scope Z_scope.

(* [itv.v] already provides the extended tests [zpos] ("> 0"), [zneg] ("< 0")
   and [ziszero] ("= 0"); we reuse them here. *)

(* same_sign(x, y) := (x < 0) == (y < 0) *)
Definition same_sign3 (a b : Zinf) : bool := Bool.eqb (zneg a) (zneg b).

(* compact, C++-faithful extended multiplication *)
Definition imul3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x * y)                     (* both finite *)
  | _, _ => if ziszero a || ziszero b then Fin 0    (* 0 * oo = 0  *)
            else if same_sign3 a b then Pinf else Ninf
  end.

(* one-Z-variable mixed cases (finite x infinite): after ruling out the finite
   zero, split its sign both ways; [cbn] then reduces the boolean [eqb]s and the
   RHS sign tests, and the two impossible sign combinations die by [lia]. *)
Ltac mix_case v :=
  destruct (Z.eqb_spec v 0) as [->|?]; cbn; [reflexivity|];
  unfold same_sign3, zneg; cbn;
  destruct (Z.ltb_spec v 0) as [?|?];
  destruct (Z.ltb_spec 0 v) as [?|?];
  cbn; first [ reflexivity | exfalso; lia ].

(* the compact version is exactly [itv.v]'s [imul3] *)
Theorem imul3'_eq : forall a b, imul3' a b = imul3 a b.
Proof.
  intros [x| |] [y| |]; cbn; try reflexivity.
  - mix_case x.
  - mix_case x.
  - mix_case y.
  - mix_case y.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Truncated corner division                                       *)
(* ------------------------------------------------------------------ *)

(** The C++ compact form (precondition: b <> 0):
      idiv_t(a, b) :=
        if a,b both finite   : tdiv(a, b)          (* battery::tdiv = round toward 0 *)
        else if b = +/-oo    : 0
        else                 : b > 0 ? a : ineg2(a)
    where [tdiv] is truncated division ([Z.quot]) and [ineg2] is the extended
    negation ([ineg3] from [zdiv.v], +oo <-> -oo).

    [zdiv.v]'s [idivt3] spells out the constructor pairs; here we give the
    compact rendering and prove it is the SAME function. *)

Definition idivt3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (Z.quot x y)             (* both finite: tdiv(a, b) *)
  | _, (Pinf | Ninf) => Fin 0                     (* b = +/-oo               *)
  | _, Fin w => if 0 <? w then a else ineg3 a     (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [zdiv.v]'s [idivt3] (unconditionally, even
   at the excluded b = 0 where both sides agree via [Z.quot _ 0 = 0]) *)
Theorem idivt3'_eq : forall a b, idivt3' a b = idivt3 a b.
Proof. intros [x| |] [y| |]; cbn; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Ceiling corner division                                         *)
(* ------------------------------------------------------------------ *)

(** The C++ compact form (precondition: b <> 0):
      idiv_c(a, b) :=
        if a,b both finite   : cdiv(a, b)           (* battery::cdiv = round up *)
        else if b = +oo      : a > 0 ? 1 : 0
        else if b = -oo      : a < 0 ? 1 : 0
        else                 : b > 0 ? a : ineg2(a)
    where [cdiv] is ceiling division and [ineg2] is [ineg3] (+oo <-> -oo).
    The "a > 0"/"a < 0" tests are [itv.v]'s extended [zpos]/[zneg].

    [itv.v]'s [idivc3] spells out the constructor pairs; here we prove the
    compact rendering is the SAME function. *)

Definition idivc3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (cdiv x y)                 (* both finite: cdiv(a, b) *)
  | _, Pinf => if zpos a then Fin 1 else Fin 0     (* b = +oo : a > 0 ? 1 : 0 *)
  | _, Ninf => if zneg a then Fin 1 else Fin 0     (* b = -oo : a < 0 ? 1 : 0 *)
  | _, Fin w => if 0 <? w then a else ineg3 a      (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [itv.v]'s [idivc3]; the finite/infinite
   corners need to move [Fin] across the [if] (zpos/zneg vs a folded [Fin]). *)
Theorem idivc3'_eq : forall a b, idivc3' a b = idivc3 a b.
Proof.
  intros [x| |] [y| |]; cbn; try reflexivity;
  first [ solve [ destruct (0 <? x); reflexivity ]
        | solve [ destruct (x <? 0); reflexivity ] ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Floor corner division                                           *)
(* ------------------------------------------------------------------ *)

(** The C++ compact form (precondition: b <> 0):
      idiv_f(a, b) :=
        if a,b both finite   : fdiv(a, b)           (* battery::fdiv = round down *)
        else if b = +oo      : a < 0 ? -1 : 0
        else if b = -oo      : a > 0 ? -1 : 0
        else                 : b > 0 ? a : ineg2(a)
    where [fdiv] is floor division ([Z.div]) and [ineg2] is [ineg3].
    The "a < 0"/"a > 0" tests are [itv.v]'s extended [zneg]/[zpos].

    [itv.v]'s [idivf3] spells out the constructor pairs; here we prove the
    compact rendering is the SAME function. *)

Definition idivf3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x / y)                     (* both finite: fdiv(a, b) *)
  | _, Pinf => if zneg a then Fin (-1) else Fin 0   (* b = +oo : a < 0 ? -1 : 0 *)
  | _, Ninf => if zpos a then Fin (-1) else Fin 0   (* b = -oo : a > 0 ? -1 : 0 *)
  | _, Fin w => if 0 <? w then a else ineg3 a       (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [itv.v]'s [idivf3] *)
Theorem idivf3'_eq : forall a b, idivf3' a b = idivf3 a b.
Proof.
  intros [x| |] [y| |]; cbn; try reflexivity;
  first [ solve [ destruct (x <? 0); reflexivity ]
        | solve [ destruct (0 <? x); reflexivity ] ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Floor via ceil : floor(x/y) = -ceil(-x/y)                        *)
(* ------------------------------------------------------------------ *)

(* the classic identity floor(a) = -ceil(-a), here on the extended integers
   ([ineg3] = extended negation).  Holds unconditionally (even at y = 0). *)
Lemma idivf3_neg_idivc3 : forall x y, idivf3 x y = ineg3 (idivc3 (ineg3 x) y).
Proof.
  intros [v| |] [w| |]; cbn; try reflexivity.
  - (* Fin v, Fin w : v / w = - cdiv (-v) w *)
    f_equal. unfold cdiv. rewrite !Z.opp_involutive. reflexivity.
  - (* Fin v, Pinf : (v<0 ? -1 : 0) = -(0 < -v ? 1 : 0) *)
    destruct (Z.ltb_spec v 0); destruct (Z.ltb_spec 0 (- v)); cbn;
      first [ reflexivity | exfalso; lia ].
  - (* Fin v, Ninf : (0<v ? -1 : 0) = -(-v<0 ? 1 : 0) *)
    destruct (Z.ltb_spec 0 v); destruct (Z.ltb_spec (- v) 0); cbn;
      first [ reflexivity | exfalso; lia ].
  - (* Pinf, Fin w *) destruct (0 <? w); reflexivity.
  - (* Ninf, Fin w *) destruct (0 <? w); reflexivity.
Qed.
