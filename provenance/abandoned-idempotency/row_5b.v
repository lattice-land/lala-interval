From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_5b : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2 ->
  hi iz <= Z.max 1 (lo iy2) / lo ix2.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Ga Gb Gc Gd Ge.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (Hzu : 0 < hi iz) by lia.
  assert (HY : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) <= -1).
  { unfold Yhi. rewrite Gb.
    clear Diz Dx2 Dy2 Ht Htp Htq Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Nz Nx2 Ny2 Hz0 Hz0hi Hne_ix1 Hne_iy Gc Ge.
    repeat apply Z.max_lub; nia. }
  rewrite Eiy2hi in Gd.
  pose proof (Z.le_min_r (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))) as Hmin.
  lia.
Qed.
