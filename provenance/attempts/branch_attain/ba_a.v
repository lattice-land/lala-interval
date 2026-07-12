From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* helper: quotient of a value in [c,d] stays between the endpoint quotients *)
Lemma div_in_range : forall c d z y,
  c <= y <= d ->
  Z.min (c / z) (d / z) <= y / z <= Z.max (c / z) (d / z).
Proof.
  intros c d z y [Hcy Hyd].
  destruct (Z.lt_trichotomy z 0) as [Hz|[Hz|Hz]].
  - (* z < 0 *)
    assert (d / z <= y / z) by (apply div_le_mono_num_neg; lia).
    assert (y / z <= c / z) by (apply div_le_mono_num_neg; lia).
    lia.
  - (* z = 0 *)
    subst z. rewrite !Zdiv_0_r. lia.
  - (* z > 0 *)
    assert (c / z <= y / z) by (apply Z.div_le_mono; lia).
    assert (y / z <= d / z) by (apply Z.div_le_mono; lia).
    lia.
Qed.

(* helper: fden output is included in the incoming z-interval (when nonempty) *)
Lemma fden_bounds : forall ix iy iz,
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  lo iz <= lo (fden ix iy iz) /\ hi (fden ix iy iz) <= hi iz.
Proof.
  intros ix iy iz.
  unfold fden; cbv zeta.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end;
          cbn iota).
  all: cbn [lo hi]; lia.
Qed.

(* helpers: if a value below the whole [P] column but still inside the union of
   the two corner columns [P] and [Q], then it lies in the [Q] column. *)
Lemma min_gap_lo : forall a P1 P2 Q1 Q2,
  Z.min (Z.min P1 Q1) (Z.min P2 Q2) <= a ->
  a < Z.min P1 P2 ->
  Z.min Q1 Q2 <= a.
Proof. intros; lia. Qed.

Lemma max_gap_hi : forall a P1 P2 Q1 Q2,
  a <= Z.max (Z.max P1 Q1) (Z.max P2 Q2) ->
  Z.max P1 P2 < a ->
  a <= Z.max Q1 Q2.
Proof. intros; lia. Qed.

Lemma branch_attain : forall w,
  (0 < lo (sz w) \/ hi (sz w) < 0) ->
  lo (sy w) <= hi (sy w) ->
  lo (sx (fdivxz_pos w)) <= hi (sx (fdivxz_pos w)) ->
  lo (sz (fdivxz_pos w)) <= hi (sz (fdivxz_pos w)) ->
  (exists y z, in_store w (lo (sx (fdivxz_pos w))) y z /\ sol (lo (sx (fdivxz_pos w))) y z) /\
  (exists y z, in_store w (hi (sx (fdivxz_pos w))) y z /\ sol (hi (sx (fdivxz_pos w))) y z) /\
  (exists x y, in_store w x y (lo (sz (fdivxz_pos w))) /\ sol x y (lo (sz (fdivxz_pos w)))) /\
  (exists x y, in_store w x y (hi (sz (fdivxz_pos w))) /\ sol x y (hi (sz (fdivxz_pos w)))).
Proof.
  intros w Hsign Hy Hnx Hnz.
  unfold fdivxz_pos in *; cbv zeta in *.
  cbn [sx sy sz] in *.
  set (yl := lo (sy w)) in *. set (yu := hi (sy w)) in *.
  set (zl := lo (sz w)) in *. set (zu := hi (sz w)) in *.
  set (I1 := Itv (Xlo yl yu zl zu) (Xhi yl yu zl zu)) in *.
  set (ix1 := inter (sx w) I1) in *.
  set (iz := inter (sz w) (fden ix1 (sy w) (sz w))) in *.
  set (I2 := Itv (Xlo yl yu (lo iz) (hi iz)) (Xhi yl yu (lo iz) (hi iz))) in *.
  set (ix2 := inter ix1 I2) in *.
  (* --- shared facts --- *)
  assert (Hab : lo ix1 <= hi ix1).
  { unfold ix2, inter in Hnx; cbn [lo hi] in Hnx; lia. }
  set (f := fden ix1 (sy w) (sz w)) in *.
  assert (Hfdne : lo f <= hi f).
  { unfold iz, inter in Hnz; cbn [lo hi] in Hnz; lia. }
  destruct (fden_bounds ix1 (sy w) (sz w) Hfdne) as [Hfb_lo Hfb_hi]. fold f in Hfb_lo, Hfb_hi.
  assert (Heqlo : lo iz = lo f).
  { unfold iz, inter; cbn [lo hi]. fold f. lia. }
  assert (Heqhi : hi iz = hi f).
  { unfold iz, inter; cbn [lo hi]. fold f. lia. }
  assert (Hmemlo : lo (sz w) <= lo iz <= hi (sz w)) by lia.
  assert (Hmemhi : lo (sz w) <= hi iz <= hi (sz w)) by lia.
  assert (Hznel : lo iz <> 0) by (destruct Hsign; lia).
  assert (Hzneh : hi iz <> 0) by (destruct Hsign; lia).
  assert (Hile1 : ile ix1 (Cx (sy w) (sz w))).
  { unfold ile, Cx, ix1, inter, I1; cbn [lo hi]. fold yl yu zl zu. lia. }
  destruct (fden_opt ix1 (sy w) (sz w) Hsign Hab Hy Hile1 Hfdne) as
    [[xL [yL (MxL & MyL & SL)]] [xU [yU (MxU & MyU & SU)]]].
  fold f in SL, SU.
  unfold mem in MxL, MyL, MxU, MyU.
  destruct SL as [SLne SLeq]. destruct SU as [SUne SUeq].
  rewrite <- Heqlo in SLeq. rewrite <- Heqhi in SUeq.
  assert (Hix1_sx : lo (sx w) <= lo ix1 /\ hi ix1 <= hi (sx w))
    by (unfold ix1, inter; cbn [lo hi]; lia).
  assert (HcolL : Z.min (yl / lo iz) (yu / lo iz) <= xL <= Z.max (yl / lo iz) (yu / lo iz)).
  { rewrite SLeq. apply div_in_range. lia. }
  assert (HcolU : Z.min (yl / hi iz) (yu / hi iz) <= xU <= Z.max (yl / hi iz) (yu / hi iz)).
  { rewrite SUeq. apply div_in_range. lia. }
  set (p1 := yl / lo iz) in *. set (p2 := yu / lo iz) in *.
  set (q1 := yl / hi iz) in *. set (q2 := yu / hi iz) in *.
  assert (Hbl_b : Z.min p1 p2 <= hi ix1) by lia.
  assert (Ha_tl : lo ix1 <= Z.max p1 p2) by lia.
  assert (Hbu_b : Z.min q1 q2 <= hi ix1) by lia.
  assert (Ha_tu : lo ix1 <= Z.max q1 q2) by lia.
  assert (Hlo2 : lo ix2 = Z.max (lo ix1) (Xlo yl yu (lo iz) (hi iz)))
    by (unfold ix2, inter, I2; cbn [lo hi]; reflexivity).
  assert (Hhi2 : hi ix2 = Z.min (hi ix1) (Xhi yl yu (lo iz) (hi iz)))
    by (unfold ix2, inter, I2; cbn [lo hi]; reflexivity).
  assert (HXlo : Xlo yl yu (lo iz) (hi iz) = Z.min (Z.min p1 q1) (Z.min p2 q2))
    by (unfold Xlo, p1, p2, q1, q2; reflexivity).
  assert (HXhi : Xhi yl yu (lo iz) (hi iz) = Z.max (Z.max p1 q1) (Z.max p2 q2))
    by (unfold Xhi, p1, p2, q1, q2; reflexivity).
  assert (HhiXhi : hi ix2 <= Z.max (Z.max p1 q1) (Z.max p2 q2))
    by (rewrite Hhi2, HXhi; apply Z.le_min_r).
  assert (Blv_l : Z.min p1 p2 <= hi ix2).
  { rewrite Hhi2, HXhi. apply Z.min_glb; [exact Hbl_b|].
    apply Z.le_trans with p1; [apply Z.le_min_l|].
    apply Z.le_trans with (Z.max p1 q1); [apply Z.le_max_l|apply Z.le_max_l]. }
  assert (Blv_u : Z.min q1 q2 <= hi ix2).
  { rewrite Hhi2, HXhi. apply Z.min_glb; [exact Hbu_b|].
    apply Z.le_trans with q1; [apply Z.le_min_l|].
    apply Z.le_trans with (Z.max p1 q1); [apply Z.le_max_r|apply Z.le_max_l]. }
  assert (HloXlo : Z.min (Z.min p1 q1) (Z.min p2 q2) <= lo ix2)
    by (rewrite Hlo2, HXlo; apply Z.le_max_r).
  assert (Tlv_l : lo ix2 <= Z.max p1 p2).
  { rewrite Hlo2, HXlo. apply Z.max_lub; [exact Ha_tl|].
    apply Z.le_trans with p1; [|apply Z.le_max_l].
    apply Z.le_trans with (Z.min p1 q1); [apply Z.le_min_l|apply Z.le_min_l]. }
  assert (Tlv_u : lo ix2 <= Z.max q1 q2).
  { rewrite Hlo2, HXlo. apply Z.max_lub; [exact Ha_tu|].
    apply Z.le_trans with q1; [|apply Z.le_max_l].
    apply Z.le_trans with (Z.min p1 q1); [apply Z.le_min_l|apply Z.le_min_r]. }
  assert (Hsx_lo2 : lo (sx w) <= lo ix2 <= hi (sx w)).
  { split.
    - rewrite Hlo2. apply Z.le_trans with (lo ix1); [apply Hix1_sx|apply Z.le_max_l].
    - apply Z.le_trans with (hi ix2); [exact Hnx|].
      apply Z.le_trans with (hi ix1); [rewrite Hhi2; apply Z.le_min_l|apply Hix1_sx]. }
  assert (Hsx_hi2 : lo (sx w) <= hi ix2 <= hi (sx w)).
  { split.
    - apply Z.le_trans with (lo ix2); [apply Hsx_lo2|exact Hnx].
    - apply Z.le_trans with (hi ix1); [rewrite Hhi2; apply Z.le_min_l|apply Hix1_sx]. }
  assert (HxLsx : lo (sx w) <= xL <= hi (sx w)).
  { split.
    - apply Z.le_trans with (lo ix1); [exact (proj1 Hix1_sx)|exact (proj1 MxL)].
    - apply Z.le_trans with (hi ix1); [exact (proj2 MxL)|exact (proj2 Hix1_sx)]. }
  assert (HxUsx : lo (sx w) <= xU <= hi (sx w)).
  { split.
    - apply Z.le_trans with (lo ix1); [exact (proj1 Hix1_sx)|exact (proj1 MxU)].
    - apply Z.le_trans with (hi ix1); [exact (proj2 MxU)|exact (proj2 Hix1_sx)]. }
  (* --- assemble the four attainment witnesses --- *)
  split; [| split; [| split]].
  - (* lo (sx (fdivxz_pos w)) = lo ix2 *)
    destruct (Z_le_gt_dec (Z.min p1 p2) (lo ix2)) as [Hle|Hgt].
    + destruct (div_1d yl yu (lo iz) (lo ix2) Hznel Hy Hle Tlv_l) as [y [Hyr Hyd]].
      exists y, (lo iz). split.
      * unfold in_store, mem. split; [exact Hsx_lo2|split;[exact Hyr|exact Hmemlo]].
      * unfold sol. split; [exact Hznel|symmetry; exact Hyd].
    + assert (Hle2 : Z.min q1 q2 <= lo ix2) by exact (min_gap_lo (lo ix2) p1 p2 q1 q2 HloXlo (Z.gt_lt _ _ Hgt)).
      destruct (div_1d yl yu (hi iz) (lo ix2) Hzneh Hy Hle2 Tlv_u) as [y [Hyr Hyd]].
      exists y, (hi iz). split.
      * unfold in_store, mem. split; [exact Hsx_lo2|split;[exact Hyr|exact Hmemhi]].
      * unfold sol. split; [exact Hzneh|symmetry; exact Hyd].
  - (* hi (sx (fdivxz_pos w)) = hi ix2 *)
    destruct (Z_le_gt_dec (hi ix2) (Z.max p1 p2)) as [Hle|Hgt].
    + destruct (div_1d yl yu (lo iz) (hi ix2) Hznel Hy Blv_l Hle) as [y [Hyr Hyd]].
      exists y, (lo iz). split.
      * unfold in_store, mem. split; [exact Hsx_hi2|split;[exact Hyr|exact Hmemlo]].
      * unfold sol. split; [exact Hznel|symmetry; exact Hyd].
    + assert (Hle2 : hi ix2 <= Z.max q1 q2) by exact (max_gap_hi (hi ix2) p1 p2 q1 q2 HhiXhi (Z.gt_lt _ _ Hgt)).
      destruct (div_1d yl yu (hi iz) (hi ix2) Hzneh Hy Blv_u Hle2) as [y [Hyr Hyd]].
      exists y, (hi iz). split.
      * unfold in_store, mem. split; [exact Hsx_hi2|split;[exact Hyr|exact Hmemhi]].
      * unfold sol. split; [exact Hzneh|symmetry; exact Hyd].
  - (* lo (sz (fdivxz_pos w)) = lo iz *)
    exists xL, yL. split.
    + unfold in_store, mem. split; [exact HxLsx|split;[exact MyL|exact Hmemlo]].
    + unfold sol. split; [exact Hznel|exact SLeq].
  - (* hi (sz (fdivxz_pos w)) = hi iz *)
    exists xU, yU. split.
    + unfold in_store, mem. split; [exact HxUsx|split;[exact MyU|exact Hmemhi]].
    + unfold sol. split; [exact Hzneh|exact SUeq].
Qed.
