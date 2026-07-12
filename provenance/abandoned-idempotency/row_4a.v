From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_4a : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 = 0 -> hi ix2 = 0 -> hi iy2 < 0 ->
  hi iz <= hi iy2 - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gx2lo Gx2hi Gy.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  assert (Hy2lo : 0 <= lo iy2).
  { rewrite Eiy2lo. rewrite Gx2lo, Gx2hi.
    apply Z.le_trans with (Ylo 0 0 (lo iz) (hi iz)); [| apply Z.le_max_r].
    unfold Ylo. apply Z.min_glb; apply Z.min_glb; lia. }
  exfalso. clear - Hy2lo Ny2 Gy. lia.
Qed.
