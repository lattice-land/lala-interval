From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zneg_5a : forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= -1 -> hi ix2 = -1 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  cdiv (Z.min (-1) (hi iy2)) (lo ix2) <= lo iz.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gxl Gxh Gyl Gyh.
  exfalso.
  assert (Hzhi : hi iz < 0).
  { rewrite Diz. unfold inter. cbn [hi].
    apply Z.le_lt_trans with (hi iz0); [apply Z.le_min_l | exact Hz0]. }
  assert (Hzlo : lo iz < 0) by lia.
  assert (Eiy2lo : lo iy2 = Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz))).
  { rewrite Dy2. unfold inter, Cy. cbn [lo hi]. reflexivity. }
  assert (P1 : 0 <= lo ix2 * lo iz) by (clear - Gxl Hzlo; nia).
  assert (P2 : 0 <= lo ix2 * hi iz) by (clear - Gxl Hzhi; nia).
  assert (HYlo : 0 <= Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { unfold Ylo. apply Z.min_glb.
    - apply Z.min_glb; assumption.
    - rewrite Gxh. apply Z.min_glb; lia. }
  assert (Hpos : 0 <= lo iy2).
  { rewrite Eiy2lo.
    apply Z.le_trans with (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz));
      [exact HYlo | apply Z.le_max_r]. }
  lia.
Qed.
