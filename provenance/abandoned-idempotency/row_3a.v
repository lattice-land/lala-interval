From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_3a : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= 0 -> hi ix2 < -1 -> 0 <= lo iy2 -> 0 < hi iy2 ->
  hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= lo iy2 / lo ix2.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gxl Gxu Gyl Gyu.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (Hxl : lo ix2 < 0) by lia.
  assert (Hzu : 0 < hi iz) by lia.
  assert (HYhi : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) < 0).
  { clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
    unfold Yhi. apply Z.max_lub_lt; apply Z.max_lub_lt; nia. }
  assert (Hmin : hi iy2 <= Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { rewrite Eiy2hi. apply Z.le_min_r. }
  clear - Gyu Hmin HYhi.
  lia.
Qed.
