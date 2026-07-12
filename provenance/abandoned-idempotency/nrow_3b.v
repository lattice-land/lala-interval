From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zneg_3b : forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= 0 -> hi ix2 < -1 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  cdiv (hi iy2) (lo ix2) <= lo iz /\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Ga Gb Gc Gd.
  exfalso.
  assert (Hizneg : hi iz < 0).
  { rewrite Diz. unfold inter. cbn [hi].
    apply Z.le_lt_trans with (hi iz0); [apply Z.le_min_l | exact Hz0]. }
  assert (Haneg : lo ix2 <= -2) by lia.
  assert (Hbneg : hi ix2 <= -2) by lia.
  assert (Hzl : lo iz < 0) by lia.
  assert (Hzu : hi iz < 0) by exact Hizneg.
  assert (Eiy2lo : lo iy2 = Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz))).
  { rewrite Dy2. unfold Cy, inter. cbn [lo hi]. reflexivity. }
  assert (HYpos : 0 < Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { unfold Ylo. apply Z.min_glb_lt; apply Z.min_glb_lt; nia. }
  assert (Hcpos : 0 < lo iy2).
  { rewrite Eiy2lo.
    apply Z.lt_le_trans with (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz));
      [ exact HYpos | apply Z.le_max_r ]. }
  lia.
Qed.
