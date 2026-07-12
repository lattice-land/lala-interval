From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_2b : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> 0 < lo ix2 -> hi iy2 < 0 -> lo iy2 <= 0 ->
  cdiv (lo iy2) (lo ix2) <= lo iz /\ hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Ga Gc Gd.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  destruct (Z.min_spec (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))) as [[Hle Heq]|[Hlt Heq]].
  - assert (Hhiy : hi iy < 0) by (rewrite Eiy2hi, Heq in Gc; exact Gc).
    assert (Hloy : lo iy < 0) by lia.
    assert (Hhiz : 0 < hi iz) by lia.
    assert (HXneg : Xhi (lo iy) (hi iy) (lo iz) (hi iz) < 0).
    { unfold Xhi. repeat apply Z.max_lub_lt; apply Z.div_lt_upper_bound; lia. }
    assert (Hx2 : hi ix2 <= Xhi (lo iy) (hi iy) (lo iz) (hi iz)) by (rewrite Eix2hi; apply Z.le_min_r).
    lia.
  - assert (HYc : lo ix2 * lo iz <= Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)).
    { unfold Yhi. apply Z.le_trans with (Z.max (lo ix2 * lo iz) (lo ix2 * hi iz)); [apply Z.le_max_l | apply Z.le_max_l]. }
    assert (Hpos : 0 < lo ix2 * lo iz) by (apply Z.mul_pos_pos; lia).
    assert (Hyhineg : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) < 0) by (rewrite Eiy2hi, Heq in Gc; exact Gc).
    lia.
Qed.
