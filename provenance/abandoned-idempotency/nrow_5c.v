From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zneg_5c : forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> ((0 <? hi iy2) && (0 <=? lo iy2))%bool = false -> lo iy2 = 0 -> hi iy2 = 0 ->
  1 <= lo iz /\ hi iz <= 0.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Glox2 Ghix2 Gb1 Gb2 Gloy2 Ghiy2.
  unfold Cy in Dy2.
  assert (Eizhi : hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0))) by (rewrite Diz; reflexivity).
  assert (Eiy2lo : lo iy2 = Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz))) by (rewrite Dy2; reflexivity).
  assert (Hizneg : hi iz < 0) by (rewrite Eizhi; lia).
  exfalso.
  assert (Hylo : 1 <= Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { unfold Ylo. rewrite Ghix2. apply Z.min_glb.
    - clear - Glox2 Nz Hizneg. apply Z.min_glb; nia.
    - clear - Nz Hizneg. apply Z.min_glb; nia. }
  assert (Hge : 1 <= lo iy2).
  { rewrite Eiy2lo. apply Z.le_trans with (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)); [exact Hylo | apply Z.le_max_r]. }
  rewrite Gloy2 in Hge. lia.
Qed.
