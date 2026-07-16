(** * zmul3: the multiplication propagator with INFINITE bounds

    Rocq model of the C++ [zmul3] (zinterval.hpp): x = y * z over Zinf
    intervals.  Constant-time structure: 4-corner product hull, zero-shaving
    of the factors when 0 is not in x, division-back by the cdiv/fdiv corner
    hull when the co-factor is sign-definite (on solutions y = x / z exactly),
    and the absolute-value bound |factor| <= |x| when it straddles zero.

    The four defining propagator properties:
      - soundness              : [zmul3_soundness]
      - reductivity            : [zmul3_reductive]
      - monotonicity           : [zmul3_monotone]  (up to bottom)
      - completeness/singleton : [zmul3_singleton_complete] *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv3 zadd3.
From LalaInterval Require fdiv2.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Auxiliary operations (mirror the C++)                           *)
(* ------------------------------------------------------------------ *)

Definition zneg3 (a : Zinf) : Zinf :=
  match a with Fin v => Fin (- v) | Pinf => Ninf | Ninf => Pinf end.

(* neq_zero: shave a zero bound *)
Definition neqz3 (i : itv3) : itv3 :=
  Itv3 (if ziszero (lo3 i) then Fin 1 else lo3 i)
       (if ziszero (hi3 i) then Fin (-1) else hi3 i).

(* 4-corner product hull *)
Definition mul_hull3 (iy iz : itv3) : itv3 :=
  Itv3 (zmin (zmin (imul3 (lo3 iy) (lo3 iz)) (imul3 (lo3 iy) (hi3 iz)))
             (zmin (imul3 (hi3 iy) (lo3 iz)) (imul3 (hi3 iy) (hi3 iz))))
       (zmax (zmax (imul3 (lo3 iy) (lo3 iz)) (imul3 (lo3 iy) (hi3 iz)))
             (zmax (imul3 (hi3 iy) (lo3 iz)) (imul3 (hi3 iy) (hi3 iz)))).

(* division-back corner hull (sound for EXACT quotients: y = x / z on
   solutions); only used on sign-definite ib *)
Definition div_back3 (ix ib : itv3) : itv3 :=
  Itv3 (zmin (zmin (idivc3 (lo3 ix) (lo3 ib)) (idivc3 (lo3 ix) (hi3 ib)))
             (zmin (idivc3 (hi3 ix) (lo3 ib)) (idivc3 (hi3 ix) (hi3 ib))))
       (zmax (zmax (idivf3 (lo3 ix) (lo3 ib)) (idivf3 (lo3 ix) (hi3 ib)))
             (zmax (idivf3 (hi3 ix) (lo3 ib)) (idivf3 (hi3 ix) (hi3 ib)))).

(* |target| <= |x| window (used when the co-factor straddles 0 but 0 notin x,
   so the co-factor is a non-zero integer: |b| >= 1) *)
Definition absb3 (ix : itv3) : itv3 :=
  Itv3 (zmin (lo3 ix) (zneg3 (hi3 ix))) (zmax (zneg3 (lo3 ix)) (hi3 ix)).

Definition sgndefb (i : itv3) : bool := (zpos (lo3 i) || zneg (hi3 i))%bool.
Definition xnzb (i : itv3) : bool := sgndefb i.

(* ------------------------------------------------------------------ *)
(** ** The propagator (mirrors zmul3)                                  *)
(* ------------------------------------------------------------------ *)

Definition zmul3 (s : store3) : store3 :=
  (* MUL *)
  let x := inter3 (sx3 s) (mul_hull3 (sy3 s) (sz3 s)) in
  let xnz := xnzb x in
  (* z.mul_back_zero(x) *)
  let z0 := if xnz then neqz3 (sz3 s) else sz3 s in
  (* y.mul_back_nz(x, z) *)
  let y0 := if sgndefb z0 then inter3 (sy3 s) (div_back3 x z0)
            else if xnz then inter3 (sy3 s) (absb3 x)
            else sy3 s in
  (* y.mul_back_zero(x) *)
  let y1 := if xnz then neqz3 y0 else y0 in
  (* z.mul_back_nz(x, y) *)
  let z1 := if sgndefb y1 then inter3 z0 (div_back3 x y1)
            else if xnz then inter3 z0 (absb3 x)
            else z0 in
  (* MUL *)
  let x2 := inter3 x (mul_hull3 y1 z1) in
  St3 x2 y1 z1.

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(** ** Helper lemmas for soundness                                      *)
(* ------------------------------------------------------------------ *)

Lemma zmin_zle_r3 : forall a b, zle (zmin a b) b.
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma zmax_zle_r3 : forall a b, zle b (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

(* the 4-corner min is below any element that one corner is below *)
Lemma zle_zmin4 : forall m1 m2 m3 m4 t,
  zle m1 t \/ zle m2 t \/ zle m3 t \/ zle m4 t ->
  zle (zmin (zmin m1 m2) (zmin m3 m4)) t.
Proof.
  intros m1 m2 m3 m4 t [H|[H|[H|H]]].
  - eapply zle_trans; [apply zle_zmin_l|]. eapply zle_trans; [apply zle_zmin_l|]. exact H.
  - eapply zle_trans; [apply zle_zmin_l|]. eapply zle_trans; [apply zmin_zle_r3|]. exact H.
  - eapply zle_trans; [apply zmin_zle_r3|]. eapply zle_trans; [apply zle_zmin_l|]. exact H.
  - eapply zle_trans; [apply zmin_zle_r3|]. eapply zle_trans; [apply zmin_zle_r3|]. exact H.
Qed.

Lemma zle_zmax4 : forall m1 m2 m3 m4 t,
  zle t m1 \/ zle t m2 \/ zle t m3 \/ zle t m4 ->
  zle t (zmax (zmax m1 m2) (zmax m3 m4)).
Proof.
  intros m1 m2 m3 m4 t [H|[H|[H|H]]].
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zle_zmax_l|]. apply zle_zmax_l.
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zmax_zle_r3|]. apply zle_zmax_l.
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zle_zmax_l|]. apply zmax_zle_r3.
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zmax_zle_r3|]. apply zmax_zle_r3.
Qed.

(* stage 1: collapse the second factor's interval onto the point vz *)
Lemma imul3_z_lb : forall A lz hz vz,
  zle lz (Fin vz) -> zle (Fin vz) hz ->
  zle (zmin (imul3 A lz) (imul3 A hz)) (imul3 A (Fin vz)).
Proof.
  intros [a| |] [c| |] [d| |] vz Hc Hd; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 a); nia).
Qed.

Lemma imul3_z_ub : forall A lz hz vz,
  zle lz (Fin vz) -> zle (Fin vz) hz ->
  zle (imul3 A (Fin vz)) (zmax (imul3 A lz) (imul3 A hz)).
Proof.
  intros [a| |] [c| |] [d| |] vz Hc Hd; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 a); nia).
Qed.

(* stage 2: collapse the first factor's interval onto the point vy *)
Lemma imul3_point_lb : forall ly hy vy vz,
  zle ly (Fin vy) -> zle (Fin vy) hy ->
  zle (zmin (imul3 ly (Fin vz)) (imul3 hy (Fin vz))) (Fin (vy * vz)).
Proof.
  intros [a| |] [b| |] vy vz Ha Hb; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 vz); nia).
Qed.

Lemma imul3_point_ub : forall ly hy vy vz,
  zle ly (Fin vy) -> zle (Fin vy) hy ->
  zle (Fin (vy * vz)) (zmax (imul3 ly (Fin vz)) (imul3 hy (Fin vz))).
Proof.
  intros [a| |] [b| |] vy vz Ha Hb; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 vz); nia).
Qed.

Lemma mul_hull3_sound : forall iy iz vy vz,
  mem3 iy vy -> mem3 iz vz -> mem3 (mul_hull3 iy iz) (vy * vz).
Proof.
  intros [ly hy] [lz hz] vy vz [Hy1 Hy2] [Hz1 Hz2]; cbn [lo3 hi3] in *.
  unfold mul_hull3, mem3; cbn [lo3 hi3].
  split.
  - apply zle_trans with (b := zmin (imul3 ly (Fin vz)) (imul3 hy (Fin vz))).
    + apply zmin_mono; apply imul3_z_lb; assumption.
    + apply imul3_point_lb; assumption.
  - apply zle_trans with (b := zmax (imul3 ly (Fin vz)) (imul3 hy (Fin vz))).
    + apply imul3_point_ub; assumption.
    + apply zmax_mono; apply imul3_z_ub; assumption.
Qed.

Lemma neqz3_sound : forall i v, mem3 i v -> v <> 0 -> mem3 (neqz3 i) v.
Proof.
  intros [l u] v [H1 H2] Hv; unfold neqz3, mem3 in *; cbn [lo3 hi3] in *; split.
  - destruct l as [a| |]; cbn in *; try easy.
    destruct (Z.eqb_spec a 0); cbn; lia.
  - destruct u as [b| |]; cbn in *; try easy.
    destruct (Z.eqb_spec b 0); cbn; lia.
Qed.

(* a sign-definite interval contains only strictly-signed values *)
Lemma sgndefb_sign : forall i v, sgndefb i = true -> mem3 i v -> v < 0 \/ 0 < v.
Proof.
  intros [l u] v Hs [H1 H2]; unfold sgndefb in Hs; cbn [lo3 hi3] in *.
  apply Bool.orb_true_iff in Hs; destruct Hs as [Hs|Hs].
  - destruct l as [a| |]; cbn in *; try easy.
    apply Z.ltb_lt in Hs; lia.
  - destruct u as [b| |]; cbn in *; try easy.
    apply Z.ltb_lt in Hs; lia.
Qed.

(* division-back soundness on exact quotients, sign-definite divisor *)
Lemma div_back3_sound : forall ix ib vx vb vq,
  mem3 ix vx -> mem3 ib vb -> sgndefb ib = true -> vx = vq * vb ->
  mem3 (div_back3 ix ib) vq.
Proof.
  intros [lx hx] [lb hb] vx vb vq [Hx1 Hx2] [Hb1 Hb2] Hsgn Heq.
  unfold sgndefb in Hsgn; cbn [lo3 hi3] in *.
  apply Bool.orb_true_iff in Hsgn.
  unfold div_back3, mem3; cbn [lo3 hi3].
  destruct Hsgn as [Hp|Hn].
  - (* positive divisor: lb = Fin l, 0 < l <= vb *)
    destruct lb as [l| |]; cbn in Hb1, Hp; [|destruct Hb1|discriminate].
    apply Z.ltb_lt in Hp.
    split.
    + (* lower bound with idivc3 corners *)
      apply zle_zmin4.
      destruct lx as [a| |]; cbn in Hx1;
        [|destruct Hx1
         |left; cbn; destruct (Z.ltb_spec 0 l); [exact I|lia]].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * (* vq >= 0: corner (lx, hb) *)
        right; left.
        destruct hb as [u| |]; cbn in Hb2; [|cbn|destruct Hb2].
        -- cbn. apply fdiv2.cdiv_ub; nia.
        -- destruct (Z.ltb_spec 0 a); cbn; nia.
      * (* vq < 0: corner (lx, lb) *)
        left. cbn. apply fdiv2.cdiv_ub; nia.
    + (* upper bound with idivf3 corners *)
      apply zle_zmax4.
      destruct hx as [B| |]; cbn in Hx2;
        [|right; right; left; cbn; destruct (Z.ltb_spec 0 l); [exact I|lia]
         |destruct Hx2].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * (* vq >= 0: corner (hx, lb) *)
        right; right; left. cbn. apply Z.div_le_lower_bound; nia.
      * (* vq < 0: corner (hx, hb) *)
        right; right; right.
        destruct hb as [u| |]; cbn in Hb2; [|cbn|destruct Hb2].
        -- cbn. apply Z.div_le_lower_bound; nia.
        -- destruct (Z.ltb_spec B 0); cbn; lia.
  - (* negative divisor: hb = Fin u, vb <= u < 0 *)
    destruct hb as [u| |]; cbn in Hb2, Hn; [|discriminate|destruct Hb2].
    apply Z.ltb_lt in Hn.
    split.
    + apply zle_zmin4.
      destruct hx as [B| |]; cbn in Hx2;
        [|right; right; right; cbn; destruct (Z.ltb_spec 0 u); [lia|exact I]
         |destruct Hx2].
      destruct (Z.le_gt_cases vq 0) as [Hq|Hq].
      * (* vq <= 0: corner (hx, hb) *)
        right; right; right. cbn. apply fdiv2.cdiv_ub_neg; nia.
      * (* vq > 0: corner (hx, lb) *)
        right; right; left.
        destruct lb as [l| |]; cbn in Hb1; [|destruct Hb1|cbn].
        -- cbn. apply fdiv2.cdiv_ub_neg; nia.
        -- destruct (Z.ltb_spec B 0); cbn; lia.
    + apply zle_zmax4.
      destruct lx as [a| |]; cbn in Hx1;
        [|destruct Hx1
         |right; left; cbn; destruct (Z.ltb_spec 0 u); [lia|exact I]].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * (* vq >= 0: corner (lx, hb) *)
        right; left. cbn. apply fdiv2.fdiv_lb_neg; nia.
      * (* vq < 0: corner (lx, lb) *)
        left.
        destruct lb as [l| |]; cbn in Hb1; [|destruct Hb1|cbn].
        -- cbn. apply fdiv2.fdiv_lb_neg; nia.
        -- destruct (Z.ltb_spec 0 a); cbn; lia.
Qed.

(* |vq| <= |vx| window: vx = vq * vb with a non-zero integer vb *)
Lemma absb3_sound : forall ix vx vb vq,
  mem3 ix vx -> vx = vq * vb -> vb <> 0 -> mem3 (absb3 ix) vq.
Proof.
  intros [lx hx] vx vb vq [H1 H2] Heq Hb; cbn [lo3 hi3] in *.
  unfold absb3, mem3, zneg3; cbn [lo3 hi3].
  assert (Hd : vb <= -1 \/ 1 <= vb) by lia.
  split.
  - destruct lx as [a| |]; destruct hx as [B| |]; cbn in *; try easy;
    destruct Hd as [Hd|Hd]; destruct (Z.le_gt_cases 0 vq); nia.
  - destruct lx as [a| |]; destruct hx as [B| |]; cbn in *; try easy;
    destruct Hd as [Hd|Hd]; destruct (Z.le_gt_cases 0 vq); nia.
Qed.

Theorem zmul3_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> vx = vy * vz ->
  in_store3 (zmul3 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Heq.
  assert (Heq' : vx = vz * vy) by (rewrite Heq; apply Z.mul_comm).
  unfold zmul3; cbv zeta.
  set (X := inter3 (sx3 s) (mul_hull3 (sy3 s) (sz3 s))).
  assert (HX : mem3 X vx).
  { apply mem3_inter; [exact Hx|]. rewrite Heq. apply mul_hull3_sound; assumption. }
  destruct (xnzb X) eqn:Exnz; cbv iota.
  - (* 0 not in x: factors are non-zero *)
    unfold xnzb in Exnz.
    assert (Hsign : vx < 0 \/ 0 < vx) by (eapply sgndefb_sign; eassumption).
    assert (Hvy : vy <> 0) by (destruct Hsign; nia).
    assert (Hvz : vz <> 0) by (destruct Hsign; nia).
    assert (HZ0 : mem3 (neqz3 (sz3 s)) vz) by (apply neqz3_sound; assumption).
    destruct (sgndefb (neqz3 (sz3 s))) eqn:Ez0; cbv iota.
    + assert (HY1 : mem3 (neqz3 (inter3 (sy3 s) (div_back3 X (neqz3 (sz3 s))))) vy).
      { apply neqz3_sound; [|assumption].
        apply mem3_inter; [assumption|].
        eapply div_back3_sound; [exact HX|exact HZ0|exact Ez0|exact Heq]. }
      destruct (sgndefb (neqz3 (inter3 (sy3 s) (div_back3 X (neqz3 (sz3 s)))))) eqn:Ey1; cbv iota.
      * assert (HZ1 : mem3 (inter3 (neqz3 (sz3 s))
                   (div_back3 X (neqz3 (inter3 (sy3 s) (div_back3 X (neqz3 (sz3 s))))))) vz).
        { apply mem3_inter; [assumption|].
          eapply div_back3_sound; [exact HX|exact HY1|exact Ey1|exact Heq']. }
        unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
      * assert (HZ1 : mem3 (inter3 (neqz3 (sz3 s)) (absb3 X)) vz).
        { apply mem3_inter; [assumption|].
          eapply absb3_sound; [exact HX|exact Heq'|exact Hvy]. }
        unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
    + assert (HY1 : mem3 (neqz3 (inter3 (sy3 s) (absb3 X))) vy).
      { apply neqz3_sound; [|assumption].
        apply mem3_inter; [assumption|].
        eapply absb3_sound; [exact HX|exact Heq|exact Hvz]. }
      destruct (sgndefb (neqz3 (inter3 (sy3 s) (absb3 X)))) eqn:Ey1; cbv iota.
      * assert (HZ1 : mem3 (inter3 (neqz3 (sz3 s))
                   (div_back3 X (neqz3 (inter3 (sy3 s) (absb3 X))))) vz).
        { apply mem3_inter; [assumption|].
          eapply div_back3_sound; [exact HX|exact HY1|exact Ey1|exact Heq']. }
        unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
      * assert (HZ1 : mem3 (inter3 (neqz3 (sz3 s)) (absb3 X)) vz).
        { apply mem3_inter; [assumption|].
          eapply absb3_sound; [exact HX|exact Heq'|exact Hvy]. }
        unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
  - (* x may contain 0 *)
    destruct (sgndefb (sz3 s)) eqn:Ez0; cbv iota.
    + assert (HY1 : mem3 (inter3 (sy3 s) (div_back3 X (sz3 s))) vy).
      { apply mem3_inter; [assumption|].
        eapply div_back3_sound; [exact HX|exact Hz|exact Ez0|exact Heq]. }
      destruct (sgndefb (inter3 (sy3 s) (div_back3 X (sz3 s)))) eqn:Ey1; cbv iota.
      * assert (HZ1 : mem3 (inter3 (sz3 s)
                   (div_back3 X (inter3 (sy3 s) (div_back3 X (sz3 s))))) vz).
        { apply mem3_inter; [assumption|].
          eapply div_back3_sound; [exact HX|exact HY1|exact Ey1|exact Heq']. }
        unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
      * unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
    + destruct (sgndefb (sy3 s)) eqn:Ey1; cbv iota.
      * assert (HZ1 : mem3 (inter3 (sz3 s) (div_back3 X (sy3 s))) vz).
        { apply mem3_inter; [assumption|].
          eapply div_back3_sound; [exact HX|exact Hy|exact Ey1|exact Heq']. }
        unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
      * unfold in_store3; cbn [sx3 sy3 sz3]; split; [|split];
          [apply mem3_inter; [exact HX|]; rewrite Heq; apply mul_hull3_sound; assumption
          |assumption|assumption].
Qed.

(* the zero-shave only moves bounds inward *)
Lemma neqz3_ile3 : forall i, ile3 (neqz3 i) i.
Proof.
  intros [l u]; split; cbn [lo3 hi3].
  - destruct l as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
  - destruct u as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
Qed.

Theorem zmul3_reductive : forall s, sle3 (zmul3 s) s.
Proof.
  intro s. unfold zmul3; cbv zeta. unfold sle3; cbn [sx3 sy3 sz3].
  repeat (match goal with |- context[if ?b then _ else _] => destruct b end).
  all: split; [|split].
  all: repeat (first [ apply ile3_refl
                | apply neqz3_ile3
                | apply inter3_ile3_l
                | eapply ile3_trans; [apply neqz3_ile3|]
                | eapply ile3_trans; [apply inter3_ile3_l|] ]).
Qed.

Theorem zmul3_monotone : forall s t,
  sle3 s t ->
  ne_store3 (zmul3 s) = true ->
  sle3 (zmul3 s) (zmul3 t).
Proof. Admitted.

Theorem zmul3_singleton_complete : forall s vx vy vz,
  sx3 s = Itv3 (Fin vx) (Fin vx) ->
  sy3 s = Itv3 (Fin vy) (Fin vy) ->
  sz3 s = Itv3 (Fin vz) (Fin vz) ->
  ne_store3 (zmul3 s) = true ->
  vx = vy * vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold zmul3 in Hne; cbv zeta in Hne.
  rewrite Hx, Hy, Hz in Hne.
  unfold ne_store3 in Hne.
  apply Bool.andb_true_iff in Hne as [Hne _].
  apply Bool.andb_true_iff in Hne as [Hnex _].
  (* the x-component is nested inter3s of the singleton hull *)
  apply ne_inter3 in Hnex.
  cbn in Hnex. apply Z.leb_le in Hnex. lia.
Qed.
