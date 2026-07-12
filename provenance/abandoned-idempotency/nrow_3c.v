From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zneg_3c : forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= 0 -> hi ix2 < -1 -> ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false ->
  hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gx1 Gx2 Gg1 Gg2.
  exfalso.
  assert (Hizneg : hi iz < 0).
  { assert (E : hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0))) by (rewrite Diz; reflexivity).
    assert (hi iz <= hi iz0) by (rewrite E; apply Z.le_min_l). lia. }
  assert (Eiy2lo : lo iy2 = Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)))
    by (rewrite Dy2; reflexivity).
  assert (HYlo : 1 <= Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { unfold Ylo. repeat apply Z.min_glb; nia. }
  assert (Hlo2 : 1 <= lo iy2).
  { rewrite Eiy2lo. apply Z.le_trans with (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz));
      [exact HYlo | apply Z.le_max_r]. }
  assert (Ha : (0 <=? lo iy2) = true) by (apply Z.leb_le; lia).
  assert (Hb : (0 <? hi iy2) = true) by (apply Z.ltb_lt; lia).
  rewrite Ha, Hb in Gg1. simpl in Gg1. discriminate.
Qed.
