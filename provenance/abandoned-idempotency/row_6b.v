From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_6b : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 = 0 -> 0 < hi ix2 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2 ->
  Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gx2lo Gx2hi Gbool Gy2hi Gy2lo.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  assert (Hdy : 0 < hi iy) by (rewrite Eiy2hi in Gy2hi; lia).
  assert (Hb1 : 0 < hi ix1).
  { pose proof Gx2hi as H. rewrite Eix2hi in H. lia. }
  assert (Hkey : Z.max 1 (lo iy2) < (hi ix2 + 1) * lo iz).
  { rewrite Eiy2lo. apply Z.max_lub_lt; [ | apply Z.max_lub_lt ].
    - apply Z.lt_le_trans with (2 * 1); [lia | apply Z.mul_le_mono_nonneg; lia].
    - rewrite Eix2hi.
      destruct (Z.min_spec (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
      + destruct (Z_le_gt_dec (lo iy) 0) as [Hyle|Hygt].
        * apply Z.le_lt_trans with 0; [lia | apply Z.mul_pos_pos; lia].
        * assert (Hx1nn : 0 <= lo ix1).
          { apply Z.le_trans with (Xlo (lo iy) (hi iy) (lo iz0) (hi iz0)); [| exact Htp].
            unfold Xlo; repeat apply Z.min_glb; apply Z.div_pos; lia. }
          pose proof (fden_loiy_pos ix1 iy iz0 Hx1nn Hne_ix1 Hz0 ltac:(lia) Hne_iy) as Hlt2.
          assert (Hm : (hi ix1 + 1) * lo (fden ix1 iy iz0) <= (hi ix1 + 1) * lo iz)
            by (apply Z.mul_le_mono_nonneg_l; [lia|exact He1]).
          lia.
      + assert (HdX : hi iy / lo iz <= Xhi (lo iy) (hi iy) (lo iz) (hi iz)).
        { unfold Xhi. apply Z.le_trans with (Z.max (hi iy / lo iz) (hi iy / hi iz)); [apply Z.le_max_l | apply Z.le_max_r]. }
        assert (Hsucc : hi iy < lo iz * (hi iy / lo iz + 1)) by (apply Z.mul_succ_div_gt; lia).
        clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
        nia.
    - assert (HYc : Ylo (lo ix2) (hi ix2) (lo iz) (hi iz) <= lo ix2 * lo iz).
      { unfold Ylo. apply Z.le_trans with (Z.min (lo ix2 * lo iz) (lo ix2 * hi iz)); apply Z.le_min_l. }
      clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
      nia. }
  assert (Z.max 1 (lo iy2) / (hi ix2 + 1) < lo iz) by (apply Z.div_lt_upper_bound; [lia|exact Hkey]).
  lia.
Qed.
