From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zneg_6b : forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> ((lo ix2 <=? 0) && (0 <=? hi ix2) && (lo iy2 <=? 0) && (0 <=? hi iy2))%bool = false -> lo ix2 = 0 -> 0 < hi ix2 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2 ->
  Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 GM0 Gx2lo Gx2hi Gbool Gy2hi Gy2lo.
  exfalso.
  assert (Eizhi : hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0))) by (rewrite Diz; reflexivity).
  assert (Hizhi : hi iz < 0).
  { rewrite Eizhi. apply Z.le_lt_trans with (hi iz0); [apply Z.le_min_l | exact Hz0]. }
  assert (Hizlo : lo iz < 0) by lia.
  assert (Eiy2hi : hi iy2 = Z.min (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))) by (rewrite Dy2; reflexivity).
  assert (HY : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) <= 0).
  { rewrite Gx2lo. unfold Yhi.
    clear Ht Diz Dx2 Dy2 Eizhi Eiy2hi.
    apply Z.max_lub; apply Z.max_lub; nia. }
  assert (Hd0 : hi iy2 <= 0).
  { rewrite Eiy2hi. apply Z.le_trans with (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)); [apply Z.le_min_r | exact HY]. }
  lia.
Qed.
