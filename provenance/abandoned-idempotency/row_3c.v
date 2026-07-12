From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zpos_3c : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= 0 -> hi ix2 < -1 -> ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false ->
  hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gle Ghi G1 G2.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (Hyhi : hi iy2 < 0).
  { rewrite Eiy2hi.
    apply Z.le_lt_trans with (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)); [apply Z.le_min_r|].
    clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq
          Hne_ix1 Hne_iy G1 G2.
    unfold Yhi.
    apply Z.max_lub_lt; apply Z.max_lub_lt; nia. }
  assert (Hylo : lo iy2 < 0) by lia.
  assert ((lo iy2 <? 0) = true) by (apply Z.ltb_lt; exact Hylo).
  assert ((hi iy2 <=? 0) = true) by (apply Z.leb_le; lia).
  rewrite H, H0 in G2. simpl in G2. discriminate.
Qed.
