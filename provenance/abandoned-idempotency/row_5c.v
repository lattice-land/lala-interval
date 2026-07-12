From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_5c : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> ((0 <? hi iy2) && (0 <=? lo iy2))%bool = false -> lo iy2 = 0 -> hi iy2 = 0 ->
  1 <= lo iz /\ hi iz <= 0.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 G1 G2 G3 G4 G5 G6.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (HY : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) <= -1).
  { unfold Yhi. rewrite G2.
    apply Z.max_lub.
    - apply Z.max_lub.
      + clear -G1 Hizpos Nz. nia.
      + clear -G1 Hizpos Nz. nia.
    - apply Z.max_lub; lia. }
  rewrite Eiy2hi in G6.
  assert (Hmin : Z.min (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)) <= -1).
  { apply Z.le_trans with (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)); [apply Z.le_min_r | exact HY]. }
  lia.
Qed.
