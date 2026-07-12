From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_6a : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 = 0 -> 0 < hi ix2 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gxlo Gxhi Gylo Gyhi.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (Hnn : 0 <= Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { rewrite Gxlo. unfold Ylo.
    clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq Ny2 Nx2.
    apply Z.min_glb.
    - apply Z.min_glb; nia.
    - apply Z.min_glb; nia. }
  assert (0 <= lo iy2).
  { rewrite Eiy2lo. apply Z.le_trans with (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz));
      [exact Hnn | apply Z.le_max_r]. }
  lia.
Qed.
