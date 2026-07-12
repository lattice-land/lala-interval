From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma cdiv_mul_le_neg : forall n M, M < 0 -> M * cdiv n M <= n.
Proof.
  intros n M HM. unfold cdiv.
  pose proof (Z.div_mod (- n) M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound (- n) M HM) as B.
  set (P := (- n) / M) in *. nia.
Qed.

Lemma neg_div_neg : forall a b, a < 0 -> 0 < b -> a / b <= -1.
Proof.
  intros a b Ha Hb.
  assert (a / b < 0) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma fden_lb_mul_neg : forall ix iy iz,
  lo ix <= -1 -> hi ix <= -1 -> 0 < lo iz -> lo iy <= hi iy ->
  lo ix * lo (fden ix iy iz) <= hi iy.
Proof.
  intros ix iy iz Ha Hb Hzl Hcd. unfold fden; cbv zeta.
  set (a := lo ix) in *. set (b := hi ix) in *.
  set (c := lo iy) in *. set (d := hi iy) in *.
  set (zl := lo iz) in *. set (zu := hi iz) in *.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end; cbn iota).
  all: cbn [lo hi].
  all: repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (_ && _)%bool = false |- _ => rewrite andb_false_iff in H; destruct H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    end.
  (* provide the max lower bounds and cdiv corners, then nia *)
  all: try (assert (Hz1 : zl <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_l).
  all: try (assert (Hz2 : zl <= Z.max zl (cdiv d a)) by apply Z.le_max_l).
  all: try (assert (Hz3 : zl <= Z.max zl (d / (b + 1) + 1)) by apply Z.le_max_l).
  all: try (assert (Hz4 : zl <= Z.max zl (c + 1)) by apply Z.le_max_l).
  all: try (assert (Hc1 : cdiv (Z.min (-1) d) a <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_r).
  all: try (assert (Hc2 : cdiv d a <= Z.max zl (cdiv d a)) by apply Z.le_max_r).
  all: try (pose proof (cdiv_mul_le_neg (Z.min (-1) d) a ltac:(lia)) as Hm1).
  all: try (pose proof (cdiv_mul_le_neg d a ltac:(lia)) as Hm2).
  all: try (assert (Hmind : Z.min (-1) d <= d) by apply Z.le_min_r).
  all: nia.
Qed.

Lemma zpos_5a : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= -1 -> hi ix2 = -1 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  cdiv (Z.min (-1) (hi iy2)) (lo ix2) <= lo iz.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gxl Gxh Gyl Gyh.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  assert (Hlo1 : lo ix1 <= lo ix2) by (rewrite Eix2lo; apply Z.le_max_l).
  apply cdiv_ub_neg; [lia|].
  apply Z.min_glb.
  - clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq. nia.
  - rewrite Eiy2hi. apply Z.min_glb.
    2: { unfold Yhi. apply Z.le_trans with (Z.max (lo ix2 * lo iz) (lo ix2 * hi iz)); [apply Z.le_max_l | apply Z.le_max_l]. }
    destruct (Z_lt_le_dec (hi iy) 0) as [Hdneg | Hdnn].
    2: { clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq. nia. }
    assert (Hcy : lo iy < 0) by lia.
    assert (HXhi : Xhi (lo iy) (hi iy) (lo iz0) (hi iz0) <= -1).
    { unfold Xhi. repeat apply Z.max_lub; apply neg_div_neg; lia. }
    assert (Hhi1 : hi ix1 <= -1) by lia.
    assert (Hlo1n : lo ix1 <= -1) by lia.
    rewrite Eix2lo.
    destruct (Z.max_spec (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz))) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
    { assert (HcX : Xlo (lo iy) (hi iy) (lo iz) (hi iz) <= hi iy / lo iz).
      { unfold Xlo. apply Z.le_trans with (Z.min (hi iy / lo iz) (hi iy / hi iz)); [apply Z.le_min_r | apply Z.le_min_l]. }
      apply Z.le_trans with ((hi iy / lo iz) * lo iz);
        [ apply Z.mul_le_mono_nonneg_r; [lia|exact HcX] | rewrite Z.mul_comm; apply Z.mul_div_le; lia ]. }
    { assert (Hcorner : lo ix1 * lo (fden ix1 iy iz0) <= hi iy)
        by (apply fden_lb_mul_neg; [lia|lia|exact Hz0|exact Hne_iy]).
      assert (Hmono : lo ix1 * lo iz <= lo ix1 * lo (fden ix1 iy iz0)).
      { clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He2 Ht Htp Htq; nia. }
      lia. }
Qed.
