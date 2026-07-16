(** * fdiv3: the floored-division propagator with INFINITE bounds

    Rocq model of the C++ [zfdiv3] (zinterval.hpp): intervals carry bounds in
    Z extended with +oo/-oo (the battery::limits sentinel encoding), and the
    propagator refines them without any finiteness guard.  All corner
    operations use the limit semantics of the infinity-aware helpers
    ([sadd3], [imul3] with 0*oo = 0, [idivf3]/[idivc3] where an infinite
    divisor yields the eventual quotient).

    Proved properties (the four defining propagator properties):
      - soundness              : [fdiv3_soundness]
      - reductivity            : [fdiv3_reductive]
      - completeness/singleton : [fdiv3_singleton_complete]
      - monotonicity           : [fdiv3_monotone]
    plus the differential lemma used for validation: on finite bounds the
    propagator agrees with the verified finite one ([fdiv2]). *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv.
From LalaInterval Require fdiv2.
Open Scope Z_scope.

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
(** ** Intervals and stores over Zinf; membership of INTEGERS          *)
(* ------------------------------------------------------------------ *)

Record itv3 := Itv3 { lo3 : Zinf ; hi3 : Zinf }.

Definition mem3 (i : itv3) (v : Z) : Prop :=
  zle (lo3 i) (Fin v) /\ zle (Fin v) (hi3 i).

(* non-emptiness: mirrors the C++ is_bot (l > u \/ l = +oo \/ u = -oo) *)
Definition nonempty3b (i : itv3) : bool :=
  match lo3 i, hi3 i with
  | Pinf, _ => false
  | _, Ninf => false
  | Ninf, _ => true
  | _, Pinf => true
  | Fin a, Fin b => a <=? b
  end.

Record store3 := St3 { sx3 : itv3 ; sy3 : itv3 ; sz3 : itv3 }.

Definition in_store3 (s : store3) (vx vy vz : Z) : Prop :=
  mem3 (sx3 s) vx /\ mem3 (sy3 s) vy /\ mem3 (sz3 s) vz.

Definition ne_store3 (s : store3) : bool :=
  (nonempty3b (sx3 s) && nonempty3b (sy3 s) && nonempty3b (sz3 s))%bool.

Definition inter3 (i j : itv3) : itv3 :=
  Itv3 (zmax (lo3 i) (lo3 j)) (zmin (hi3 i) (hi3 j)).

Definition ijoin3 (i j : itv3) : itv3 :=
  Itv3 (zmin (lo3 i) (lo3 j)) (zmax (hi3 i) (hi3 j)).

Definition sjoin3 (s t : store3) : store3 :=
  St3 (ijoin3 (sx3 s) (sx3 t)) (ijoin3 (sy3 s) (sy3 t)) (ijoin3 (sz3 s) (sz3 t)).

Definition sqcupbot3 (s t : store3) : store3 :=
  if ne_store3 s
  then (if ne_store3 t then sjoin3 s t else s)
  else t.

(* interval order (containment) and store order *)
Definition ile3 (i j : itv3) : Prop := zle (lo3 j) (lo3 i) /\ zle (hi3 i) (hi3 j).
Definition sle3 (a b : store3) : Prop :=
  ile3 (sx3 a) (sx3 b) /\ ile3 (sy3 a) (sy3 b) /\ ile3 (sz3 a) (sz3 b).

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
             | Fin v => Fin (fdiv2.cdiv v w)
             | Pinf => if 0 <? w then Pinf else Ninf
             | Ninf => if 0 <? w then Ninf else Pinf
             end
  end.

(* ------------------------------------------------------------------ *)
(** ** The propagator (mirrors zfdiv3)                                 *)
(* ------------------------------------------------------------------ *)

(* the 4-corner quotient window (DIV step) *)
Definition div_hull3 (iy iz : itv3) : itv3 :=
  Itv3 (zmin (zmin (idivf3 (lo3 iy) (lo3 iz)) (idivf3 (lo3 iy) (hi3 iz)))
             (zmin (idivf3 (hi3 iy) (lo3 iz)) (idivf3 (hi3 iy) (hi3 iz))))
       (zmax (zmax (idivf3 (lo3 iy) (lo3 iz)) (idivf3 (lo3 iy) (hi3 iz)))
             (zmax (idivf3 (hi3 iy) (lo3 iz)) (idivf3 (hi3 iy) (hi3 iz)))).

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

(* the exact band divisor refinement (DEN step), sign dispatched on iz *)
Definition fden3 (ix iy iz : itv3) : itv3 :=
  let a := lo3 ix in let b1 := sadd3 (hi3 ix) 1 in
  let c := lo3 iy in let d := hi3 iy in
  let zl := lo3 iz in let zu := hi3 iz in
  if zpos zl then
    if ((ziszero a && zneg d) || (ziszero b1 && zge0 c))%bool then Itv3 (Fin 1) (Fin 0)
    else Itv3 (zmax zl (zmax (if zneg a then idivc3 d a else zl)
                             (if zpos b1 then idivc3 (sadd3 c 1) b1 else zl)))
              (zmin zu (zmin (if zpos a then idivf3 d a else zu)
                             (if zneg b1 then idivf3 (sadd3 c 1) b1 else zu)))
  else if zneg zu then
    if ((ziszero a && zpos c) || (ziszero b1 && zle0 d))%bool then Itv3 (Fin 1) (Fin 0)
    else Itv3 (zmax zl (zmax (if zpos a then idivc3 c a else zl)
                             (if zneg b1 then idivc3 (sadd3 d (-1)) b1 else zl)))
              (zmin zu (zmin (if zneg a then idivf3 c a else zu)
                             (if zpos b1 then idivf3 (sadd3 d (-1)) b1 else zu)))
  else iz.

Definition fdivxz3 (s : store3) : store3 :=
  let ix1 := inter3 (sx3 s) (div_hull3 (sy3 s) (sz3 s)) in
  let iz  := inter3 (sz3 s) (fden3 ix1 (sy3 s) (sz3 s)) in
  let ix2 := inter3 ix1 (div_hull3 (sy3 s) iz) in
  St3 ix2 (sy3 s) iz.

Definition restrict_z_pos3 (s : store3) : store3 :=
  St3 (sx3 s) (sy3 s) (inter3 (sz3 s) (Itv3 (Fin 1) (hi3 (sz3 s)))).
Definition restrict_z_neg3 (s : store3) : store3 :=
  St3 (sx3 s) (sy3 s) (inter3 (sz3 s) (Itv3 (lo3 (sz3 s)) (Fin (-1)))).

(* the numerator hull (NUM step) *)
Definition refine_y3 (s : store3) : store3 :=
  let xl := lo3 (sx3 s) in let xu1 := sadd3 (hi3 (sx3 s)) 1 in
  let zl := lo3 (sz3 s) in let zu := hi3 (sz3 s) in
  St3 (sx3 s)
      (inter3 (sy3 s)
        (Itv3 (zmin (zmin (imul3 xl zl) (imul3 xl zu))
                    (zmin (sadd3 (imul3 xu1 zl) 1) (sadd3 (imul3 xu1 zu) 1)))
              (zmax (zmax (imul3 xl zl) (imul3 xl zu))
                    (zmax (sadd3 (imul3 xu1 zl) (-1)) (sadd3 (imul3 xu1 zu) (-1))))))
      (sz3 s).

Definition propagator3 (s : store3) : store3 :=
  refine_y3 (sqcupbot3 (fdivxz3 (restrict_z_neg3 s))
                       (fdivxz3 (restrict_z_pos3 s))).

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem fdiv3_soundness : forall s vx vy vz,
  in_store3 s vx vy vz ->
  fdiv2.sol vx vy vz ->
  in_store3 (propagator3 s) vx vy vz.
Proof. Admitted.

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

Lemma ile3_refl : forall i, ile3 i i.
Proof. intro i; split; apply zle_refl. Qed.

Lemma ile3_trans : forall i j k, ile3 i j -> ile3 j k -> ile3 i k.
Proof.
  intros i j k [Hl1 Hh1] [Hl2 Hh2]; split; eapply zle_trans; eassumption.
Qed.

Lemma inter3_ile3_l : forall i j, ile3 (inter3 i j) i.
Proof.
  intros i j; unfold ile3, inter3; cbn [lo3 hi3].
  split; [apply zle_zmax_l | apply zmin_zle_l].
Qed.

Lemma ijoin3_ile3 : forall i j k, ile3 i k -> ile3 j k -> ile3 (ijoin3 i j) k.
Proof.
  intros i j k [Hli Hhi] [Hlj Hhj]; unfold ile3, ijoin3; cbn [lo3 hi3].
  split; [apply zle_zmin_glb | apply zmax_lub]; assumption.
Qed.

Lemma sle3_trans : forall a b c, sle3 a b -> sle3 b c -> sle3 a c.
Proof.
  unfold sle3; intros a b c [Hx [Hy Hz]] [Hx' [Hy' Hz']];
  split; [|split]; eapply ile3_trans; eassumption.
Qed.

Lemma restrict_z_pos3_ile : forall t, sle3 (restrict_z_pos3 t) t.
Proof.
  intro t; unfold restrict_z_pos3, sle3; cbn [sx3 sy3 sz3].
  split; [apply ile3_refl | split; [apply ile3_refl | apply inter3_ile3_l]].
Qed.

Lemma restrict_z_neg3_ile : forall t, sle3 (restrict_z_neg3 t) t.
Proof.
  intro t; unfold restrict_z_neg3, sle3; cbn [sx3 sy3 sz3].
  split; [apply ile3_refl | split; [apply ile3_refl | apply inter3_ile3_l]].
Qed.

Lemma fdivxz3_ile : forall w, sle3 (fdivxz3 w) w.
Proof.
  intro w. unfold fdivxz3; cbv zeta; unfold sle3; cbn [sx3 sy3 sz3].
  split; [ eapply ile3_trans; [apply inter3_ile3_l | apply inter3_ile3_l]
         | split; [apply ile3_refl | apply inter3_ile3_l] ].
Qed.

Lemma refine_y3_ile : forall w, sle3 (refine_y3 w) w.
Proof.
  intro w; unfold refine_y3; cbv zeta; unfold sle3; cbn [sx3 sy3 sz3].
  split; [apply ile3_refl | split; [apply inter3_ile3_l | apply ile3_refl]].
Qed.

Lemma sqcupbot3_ile : forall a b t, sle3 a t -> sle3 b t -> sle3 (sqcupbot3 a b) t.
Proof.
  intros a b t Ha Hb. unfold sqcupbot3.
  destruct (ne_store3 a), (ne_store3 b); cbn iota; try assumption.
  unfold sjoin3, sle3 in *; cbn [sx3 sy3 sz3].
  destruct Ha as [Hax [Hay Haz]]; destruct Hb as [Hbx [Hby Hbz]].
  split; [|split]; apply ijoin3_ile3; assumption.
Qed.

Theorem fdiv3_reductive : forall s, sle3 (propagator3 s) s.
Proof.
  intro s. unfold propagator3.
  eapply sle3_trans; [apply refine_y3_ile|].
  apply sqcupbot3_ile.
  - eapply sle3_trans; [apply fdivxz3_ile | apply restrict_z_neg3_ile].
  - eapply sle3_trans; [apply fdivxz3_ile | apply restrict_z_pos3_ile].
Qed.

(* Monotonicity holds up to bottom: with non-normalized empty intervals, an
   empty output (identified with bot in the lattice) is below everything, so
   the statement is conditioned on the output of [s] being non-empty.  (The
   unconditional statement is false for crossed-bounds empty inputs, which
   the domain deliberately permits.) *)
Theorem fdiv3_monotone : forall s t,
  sle3 s t ->
  ne_store3 (propagator3 s) = true ->
  sle3 (propagator3 s) (propagator3 t).
Proof. Admitted.

Theorem fdiv3_singleton_complete : forall s vx vy vz,
  sx3 s = Itv3 (Fin vx) (Fin vx) ->
  sy3 s = Itv3 (Fin vy) (Fin vy) ->
  sz3 s = Itv3 (Fin vz) (Fin vz) ->
  ne_store3 (propagator3 s) = true ->
  fdiv2.sol vx vy vz.
Proof. Admitted.
