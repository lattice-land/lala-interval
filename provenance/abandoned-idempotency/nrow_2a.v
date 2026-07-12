From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zneg_2a : forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> 0 < lo ix2 -> 0 <= lo iy2 -> 0 < hi iy2 ->
  Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= hi iy2 / lo ix2.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Ga Gc Gd.
  exfalso.
  assert (Eizhi : hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0))) by (rewrite Diz; reflexivity).
  assert (Hizneg : hi iz < 0) by (rewrite Eizhi; lia).
  assert (Eiy2hi : hi iy2 = Z.min (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))).
  { unfold Cy in Dy2. rewrite Dy2. reflexivity. }
  assert (HY : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) < 0).
  { unfold Yhi.
    clear Diz Dx2 Dy2 Ht Eizhi Eiy2hi.
    repeat apply Z.max_lub_lt; nia. }
  rewrite Eiy2hi in Gd.
  assert (Hmr : Z.min (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)) <= Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)) by apply Z.le_min_r.
  lia.
Qed.
