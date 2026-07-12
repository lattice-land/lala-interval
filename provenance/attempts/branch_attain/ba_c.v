From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* fden output is contained in the incoming z-interval (when nonempty). *)
Lemma fden_sub : forall ix iy iz,
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  lo iz <= lo (fden ix iy iz) /\ hi (fden ix iy iz) <= hi iz.
Proof.
  intros ix iy iz. unfold fden; cbv zeta.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end; cbn iota).
  all: cbn [lo hi]; intro Hne; split;
       solve [ lia | apply Z.le_max_l | apply Z.le_min_l ].
Qed.

(* y/z lies between the two corner quotients yl/z and yu/z. *)
Lemma div_between : forall yl yu y z, z <> 0 -> yl <= y <= yu ->
  Z.min (yl/z) (yu/z) <= y/z /\ y/z <= Z.max (yl/z) (yu/z).
Proof.
  intros yl yu y z Hz [Hl Hu].
  destruct (Z.lt_ge_cases z 0) as [Hn|Hp].
  - assert (yu/z <= y/z) by (apply div_le_mono_num_neg; lia).
    assert (y/z <= yl/z) by (apply div_le_mono_num_neg; lia).
    split; [ eapply Z.le_trans; [apply Z.le_min_r|eassumption]
           | eapply Z.le_trans; [eassumption|apply Z.le_max_l] ].
  - assert (0 < z) by lia.
    assert (yl/z <= y/z) by (apply Z.div_le_mono; lia).
    assert (y/z <= yu/z) by (apply Z.div_le_mono; lia).
    split; [ eapply Z.le_trans; [apply Z.le_min_l|eassumption]
           | eapply Z.le_trans; [eassumption|apply Z.le_max_r] ].
Qed.

(* corner 1D-max is below the 2D max Xhi *)
Lemma le_Xhi : forall yl yu zl zu z, (z = zl \/ z = zu) ->
  Z.max (yl/z) (yu/z) <= Xhi yl yu zl zu.
Proof.
  intros yl yu zl zu z H. unfold Xhi. destruct H; subst z; apply Z.max_lub.
  - eapply Z.le_trans; [apply Z.le_max_l|apply Z.le_max_l].
  - eapply Z.le_trans; [apply Z.le_max_l|apply Z.le_max_r].
  - eapply Z.le_trans; [apply Z.le_max_r|apply Z.le_max_l].
  - eapply Z.le_trans; [apply Z.le_max_r|apply Z.le_max_r].
Qed.

Lemma Xlo_le : forall yl yu zl zu z, (z = zl \/ z = zu) ->
  Xlo yl yu zl zu <= Z.min (yl/z) (yu/z).
Proof.
  intros yl yu zl zu z H. unfold Xlo. destruct H; subst z; apply Z.min_glb.
  - eapply Z.le_trans; [apply Z.le_min_l|apply Z.le_min_l].
  - eapply Z.le_trans; [apply Z.le_min_r|apply Z.le_min_l].
  - eapply Z.le_trans; [apply Z.le_min_l|apply Z.le_min_r].
  - eapply Z.le_trans; [apply Z.le_min_r|apply Z.le_min_r].
Qed.

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
  unfold fdivxz_pos in *; cbv zeta in *; cbn [sx sy sz] in *.
  set (I1 := Itv (Xlo (lo (sy w)) (hi (sy w)) (lo (sz w)) (hi (sz w)))
                 (Xhi (lo (sy w)) (hi (sy w)) (lo (sz w)) (hi (sz w)))) in *.
  set (ix1 := inter (sx w) I1) in *.
  set (iz := inter (sz w) (fden ix1 (sy w) (sz w))) in *.
  set (I2 := Itv (Xlo (lo (sy w)) (hi (sy w)) (lo iz) (hi iz))
                 (Xhi (lo (sy w)) (hi (sy w)) (lo iz) (hi iz))) in *.
  set (ix2 := inter ix1 I2) in *.
  set (FD := fden ix1 (sy w) (sz w)) in *.
  (* --- structural facts about the nested intersections --- *)
  assert (Hlz : lo iz = Z.max (lo (sz w)) (lo FD)) by reflexivity.
  assert (Hhz : hi iz = Z.min (hi (sz w)) (hi FD)) by reflexivity.
  assert (Hfdne : lo FD <= hi FD).
  { rewrite Hlz in Hnz; rewrite Hhz in Hnz.
    pose proof (Z.le_max_r (lo (sz w)) (lo FD)).
    pose proof (Z.le_min_r (hi (sz w)) (hi FD)). lia. }
  destruct (fden_sub ix1 (sy w) (sz w) Hfdne) as [Hsub_lo Hsub_hi].
  fold FD in Hsub_lo, Hsub_hi.
  assert (Hloiz : lo iz = lo FD) by (rewrite Hlz; apply Z.max_r; exact Hsub_lo).
  assert (Hhiiz : hi iz = hi FD) by (rewrite Hhz; apply Z.min_r; exact Hsub_hi).
  assert (Hizsl : lo (sz w) <= lo iz) by (rewrite Hlz; apply Z.le_max_l).
  assert (Hizsh : hi iz <= hi (sz w)) by (rewrite Hhz; apply Z.le_min_l).
  assert (Hlx1 : lo ix1 = Z.max (lo (sx w)) (lo I1)) by reflexivity.
  assert (Hhx1 : hi ix1 = Z.min (hi (sx w)) (hi I1)) by reflexivity.
  assert (Hlx2 : lo ix2 = Z.max (lo ix1) (lo I2)) by reflexivity.
  assert (Hhx2 : hi ix2 = Z.min (hi ix1) (hi I2)) by reflexivity.
  assert (HI1l : lo I1 = Xlo (lo (sy w)) (hi (sy w)) (lo (sz w)) (hi (sz w))) by reflexivity.
  assert (HI1h : hi I1 = Xhi (lo (sy w)) (hi (sy w)) (lo (sz w)) (hi (sz w))) by reflexivity.
  assert (HI2l : lo I2 = Xlo (lo (sy w)) (hi (sy w)) (lo iz) (hi iz)) by reflexivity.
  assert (HI2h : hi I2 = Xhi (lo (sy w)) (hi (sy w)) (lo iz) (hi iz)) by reflexivity.
  assert (Hix1ne : lo ix1 <= hi ix1).
  { pose proof (Z.le_max_l (lo ix1) (lo I2)). pose proof (Z.le_min_l (hi ix1) (hi I2)).
    rewrite <- Hlx2 in *; rewrite <- Hhx2 in *; lia. }
  assert (Hlznz : lo iz <> 0) by lia.
  assert (Hhznz : hi iz <> 0) by lia.
  assert (Hile : ile ix1 (Cx (sy w) (sz w))).
  { unfold ile, Cx; cbn [lo hi]. split.
    - rewrite Hlx1. apply Z.le_max_r.
    - rewrite Hhx1. apply Z.le_min_r. }
  (* --- the shared fden_opt witnesses (drive both z-bounds and x-bounds) --- *)
  destruct (fden_opt ix1 (sy w) (sz w) Hsign Hix1ne Hy Hile Hfdne)
    as [ [xl [yl_ [Mxl [Myl Sl]]]] [xh [yh_ [Mxh [Myh Sh]]]] ].
  fold FD in Sl, Sh.
  rewrite <- Hloiz in Sl. rewrite <- Hhiiz in Sh.
  unfold mem in Mxl, Myl, Mxh, Myh.
  unfold sol in Sl, Sh. destruct Sl as [Slnz Sleq]. destruct Sh as [Shnz Sheq].
  assert (Hx1sl : lo (sx w) <= lo ix1) by (rewrite Hlx1; apply Z.le_max_l).
  assert (Hx1sh : hi ix1 <= hi (sx w)) by (rewrite Hhx1; apply Z.le_min_l).
  assert (Hx2x1l : lo ix1 <= lo ix2) by (rewrite Hlx2; apply Z.le_max_l).
  assert (Hx2x1h : hi ix2 <= hi ix1) by (rewrite Hhx2; apply Z.le_min_l).
  assert (Hx2I2l : lo I2 <= lo ix2) by (rewrite Hlx2; apply Z.le_max_r).
  assert (Hx2I2h : hi ix2 <= hi I2) by (rewrite Hhx2; apply Z.le_min_r).
  assert (Msxlo2 : lo (sx w) <= lo ix2 <= hi (sx w)) by lia.
  assert (Msxhi2 : lo (sx w) <= hi ix2 <= hi (sx w)) by lia.
  assert (Mszlo : lo (sz w) <= lo iz <= hi (sz w)) by lia.
  assert (Mszhi : lo (sz w) <= hi iz <= hi (sz w)) by lia.
  split; [| split; [| split]].
  - (* ===== x lower bound ===== *)
    destruct (div_between (lo (sy w)) (hi (sy w)) yl_ (lo iz) Slnz Myl) as [DBl1 DBl2].
    destruct (div_between (lo (sy w)) (hi (sy w)) yh_ (hi iz) Shnz Myh) as [DBh1 DBh2].
    rewrite <- Sleq in DBl1, DBl2. rewrite <- Sheq in DBh1, DBh2.
    pose proof (Xlo_le (lo (sy w)) (hi (sy w)) (lo iz) (hi iz) (lo iz) (or_introl eq_refl)) as XLl.
    pose proof (Xlo_le (lo (sy w)) (hi (sy w)) (lo iz) (hi iz) (hi iz) (or_intror eq_refl)) as XLh.
    assert (Hvlo : Xlo (lo (sy w)) (hi (sy w)) (lo iz) (hi iz) <= lo ix2)
      by (rewrite <- HI2l; exact Hx2I2l).
    assert (HxlI2 : lo I2 <= xl) by (rewrite HI2l; eapply Z.le_trans; [exact XLl|exact DBl1]).
    assert (HxhI2 : lo I2 <= xh) by (rewrite HI2l; eapply Z.le_trans; [exact XLh|exact DBh1]).
    assert (Hxlv : lo ix2 <= xl)
      by (rewrite Hlx2; apply Z.max_lub; [exact (proj1 Mxl) | exact HxlI2]).
    assert (Hxhv : lo ix2 <= xh)
      by (rewrite Hlx2; apply Z.max_lub; [exact (proj1 Mxh) | exact HxhI2]).
    destruct (Z.le_gt_cases (Z.min (lo (sy w) / lo iz) (hi (sy w) / lo iz)) (lo ix2)) as [B1|B1].
    + destruct (div_1d (lo (sy w)) (hi (sy w)) (lo iz) (lo ix2) Slnz Hy B1
                ltac:(eapply Z.le_trans; [exact Hxlv|exact DBl2])) as [y0 [Hy0 Hdiv0]].
      exists y0, (lo iz). split;
        [ unfold in_store, mem; repeat split; try (exact (proj1 Msxlo2)); try lia
        | split; [exact Slnz | symmetry; exact Hdiv0] ].
    + destruct (Z.le_gt_cases (Z.min (lo (sy w) / hi iz) (hi (sy w) / hi iz)) (lo ix2)) as [B2|B2].
      * destruct (div_1d (lo (sy w)) (hi (sy w)) (hi iz) (lo ix2) Shnz Hy B2
                  ltac:(eapply Z.le_trans; [exact Hxhv|exact DBh2])) as [y0 [Hy0 Hdiv0]].
        exists y0, (hi iz). split;
          [ unfold in_store, mem; repeat split; try (exact (proj1 Msxlo2)); try lia
          | split; [exact Shnz | symmetry; exact Hdiv0] ].
      * exfalso.
        assert (Ha : lo ix2 < lo (sy w) / lo iz)
          by (eapply Z.lt_le_trans; [exact B1|apply Z.le_min_l]).
        assert (Hc : lo ix2 < hi (sy w) / lo iz)
          by (eapply Z.lt_le_trans; [exact B1|apply Z.le_min_r]).
        assert (Hb : lo ix2 < lo (sy w) / hi iz)
          by (eapply Z.lt_le_trans; [exact B2|apply Z.le_min_l]).
        assert (Hd : lo ix2 < hi (sy w) / hi iz)
          by (eapply Z.lt_le_trans; [exact B2|apply Z.le_min_r]).
        assert (Hlt : lo ix2 < Xlo (lo (sy w)) (hi (sy w)) (lo iz) (hi iz))
          by (unfold Xlo; apply Z.min_glb_lt; apply Z.min_glb_lt; assumption).
        apply (Z.lt_irrefl (lo ix2)); eapply Z.lt_le_trans; [exact Hlt|exact Hvlo].
  - (* ===== x upper bound ===== *)
    destruct (div_between (lo (sy w)) (hi (sy w)) yl_ (lo iz) Slnz Myl) as [DBl1 DBl2].
    destruct (div_between (lo (sy w)) (hi (sy w)) yh_ (hi iz) Shnz Myh) as [DBh1 DBh2].
    rewrite <- Sleq in DBl1, DBl2. rewrite <- Sheq in DBh1, DBh2.
    pose proof (le_Xhi (lo (sy w)) (hi (sy w)) (lo iz) (hi iz) (lo iz) (or_introl eq_refl)) as LXl.
    pose proof (le_Xhi (lo (sy w)) (hi (sy w)) (lo iz) (hi iz) (hi iz) (or_intror eq_refl)) as LXh.
    assert (Hvhi : hi ix2 <= Xhi (lo (sy w)) (hi (sy w)) (lo iz) (hi iz))
      by (rewrite <- HI2h; exact Hx2I2h).
    assert (HxlI2 : xl <= hi I2) by (rewrite HI2h; eapply Z.le_trans; [exact DBl2 | exact LXl]).
    assert (HxhI2 : xh <= hi I2) by (rewrite HI2h; eapply Z.le_trans; [exact DBh2 | exact LXh]).
    assert (Hxlv : xl <= hi ix2)
      by (rewrite Hhx2; apply Z.min_glb; [exact (proj2 Mxl) | exact HxlI2]).
    assert (Hxhv : xh <= hi ix2)
      by (rewrite Hhx2; apply Z.min_glb; [exact (proj2 Mxh) | exact HxhI2]).
    destruct (Z.le_gt_cases (hi ix2) (Z.max (lo (sy w) / lo iz) (hi (sy w) / lo iz))) as [B1|B1].
    + destruct (div_1d (lo (sy w)) (hi (sy w)) (lo iz) (hi ix2) Slnz Hy
                ltac:(eapply Z.le_trans; [exact DBl1|exact Hxlv]) B1) as [y0 [Hy0 Hdiv0]].
      exists y0, (lo iz). split;
        [ unfold in_store, mem; repeat split; try (exact (proj1 Msxhi2)); try lia
        | split; [exact Slnz | symmetry; exact Hdiv0] ].
    + destruct (Z.le_gt_cases (hi ix2) (Z.max (lo (sy w) / hi iz) (hi (sy w) / hi iz))) as [B2|B2].
      * destruct (div_1d (lo (sy w)) (hi (sy w)) (hi iz) (hi ix2) Shnz Hy
                  ltac:(eapply Z.le_trans; [exact DBh1|exact Hxhv]) B2) as [y0 [Hy0 Hdiv0]].
        exists y0, (hi iz). split;
          [ unfold in_store, mem; repeat split; try (exact (proj1 Msxhi2)); try lia
          | split; [exact Shnz | symmetry; exact Hdiv0] ].
      * exfalso.
        assert (Hcontra : Xhi (lo (sy w)) (hi (sy w)) (lo iz) (hi iz) < hi ix2).
        { pose proof (Z.le_max_l (lo (sy w) / lo iz) (hi (sy w) / lo iz)) as H.
          pose proof (Z.le_max_r (lo (sy w) / lo iz) (hi (sy w) / lo iz)) as H0.
          pose proof (Z.le_max_l (lo (sy w) / hi iz) (hi (sy w) / hi iz)) as H1.
          pose proof (Z.le_max_r (lo (sy w) / hi iz) (hi (sy w) / hi iz)) as H2.
          unfold Xhi.
          assert (Ha : lo (sy w) / lo iz < hi ix2) by (eapply Z.le_lt_trans; [exact H|exact B1]).
          assert (Hc : hi (sy w) / lo iz < hi ix2) by (eapply Z.le_lt_trans; [exact H0|exact B1]).
          assert (Hb : lo (sy w) / hi iz < hi ix2) by (eapply Z.le_lt_trans; [exact H1|exact B2]).
          assert (Hd : hi (sy w) / hi iz < hi ix2) by (eapply Z.le_lt_trans; [exact H2|exact B2]).
          apply Z.max_lub_lt; apply Z.max_lub_lt; assumption. }
        apply (Z.lt_irrefl (hi ix2)); eapply Z.le_lt_trans; [exact Hvhi|exact Hcontra].
  - (* ===== z lower bound ===== *)
    exists xl, yl_. split;
      [ unfold in_store, mem; repeat split; try lia
      | split; [exact Slnz | exact Sleq] ].
  - (* ===== z upper bound ===== *)
    exists xh, yh_. split;
      [ unfold in_store, mem; repeat split; try lia
      | split; [exact Shnz | exact Sheq] ].
Qed.
