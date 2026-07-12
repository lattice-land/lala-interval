From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma zneg_4b : forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> ((lo ix2 <=? 0) && (0 <=? hi ix2) && (lo iy2 <=? 0) && (0 <=? hi iy2))%bool = false -> lo ix2 = 0 -> hi ix2 = 0 -> 0 <= hi iy2 ->
  lo iy2 + 1 <= lo iz.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gm Gx0lo Gx0hi Ghy.
  unfold Cx, Cy in Ht, Dx2, Dy2.
  assert (Eizhi : hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0))) by (rewrite Diz; reflexivity).
  assert (Eix2hi : hi ix2 = Z.min (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) by (rewrite Dx2; reflexivity).
  assert (Eiy2lo : lo iy2 = Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz))) by (rewrite Dy2; reflexivity).
  assert (Eiy2hi : hi iy2 = Z.min (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))) by (rewrite Dy2; reflexivity).
  (* z is negative *)
  assert (Hizhi : hi iz < 0)
    by (rewrite Eizhi; pose proof (Z.le_min_l (hi iz0) (hi (fden ix1 iy iz0))); lia).
  assert (Hizlo : lo iz < 0) by lia.
  (* Ylo over x=[0,0] is <= 0 *)
  assert (HYub : Ylo (lo ix2) (hi ix2) (lo iz) (hi iz) <= 0).
  { rewrite Gx0lo, Gx0hi. unfold Ylo.
    apply Z.le_trans with (Z.min (0 * lo iz) (0 * hi iz)); [apply Z.le_min_l|].
    apply Z.le_trans with (0 * lo iz); [apply Z.le_min_l|]. lia. }
  (* guard forces lo iy2 > 0 *)
  assert (Glo : 0 < lo iy2).
  { destruct (Z.leb_spec (lo iy2) 0) as [Hle|Hgt]; [exfalso|exact Hgt].
    rewrite Gx0lo, Gx0hi in Gm.
    assert (Hle' : (lo iy2 <=? 0) = true) by (apply Z.leb_le; exact Hle).
    assert (Hb : (0 <=? hi iy2) = true) by (apply Z.leb_le; exact Ghy).
    cbn in Gm. congruence. }
  (* hence lo iy > 0 *)
  assert (Hloy : 0 < lo iy).
  { rewrite Eiy2lo in Glo.
    destruct (Z.max_spec (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz))) as [[_ E]|[_ E]];
      rewrite E in Glo; lia. }
  (* and hi iy > 0 *)
  assert (Hhiy : 0 < hi iy).
  { pose proof (Z.le_max_l (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz))) as HmL.
    pose proof (Z.le_min_l (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))) as HmR.
    rewrite <- Eiy2lo in HmL. rewrite <- Eiy2hi in HmR. lia. }
  (* hi ix2 = 0 forces Xhi >= 0 *)
  assert (HXge : 0 <= Xhi (lo iy) (hi iy) (lo iz) (hi iz)).
  { pose proof (Z.le_min_r (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) as HM.
    rewrite <- Eix2hi in HM. rewrite Gx0hi in HM. exact HM. }
  (* but Xhi <= -1 since num>0 den<0 *)
  assert (HXle : Xhi (lo iy) (hi iy) (lo iz) (hi iz) <= -1).
  { assert (lo iy / lo iz < 0) by (apply fdiv_lt_neg; lia).
    assert (lo iy / hi iz < 0) by (apply fdiv_lt_neg; lia).
    assert (hi iy / lo iz < 0) by (apply fdiv_lt_neg; lia).
    assert (hi iy / hi iz < 0) by (apply fdiv_lt_neg; lia).
    unfold Xhi. repeat apply Z.max_lub; lia. }
  exfalso. lia.
Qed.
