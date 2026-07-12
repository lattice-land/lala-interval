From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma fden_hi_pos : forall ix iy iz,
  0 < lo ix -> lo ix <= hi ix -> 0 < hi (fden ix iy iz) -> 0 < hi iy.
Proof.
  intros ix iy iz Ha Hab. unfold fden; cbv zeta.
  set (a := lo ix) in *. set (b := hi ix) in *.
  set (c := lo iy) in *. set (d := hi iy) in *.
  set (zl := lo iz) in *. set (zu := hi iz) in *.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end; cbn iota).
  all: cbn [lo hi].
  all: intro Hhi.
  all: repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    end.
  all: try lia.
  all: first
    [ (assert (Hmm : Z.min zu (d / a) <= d / a) by apply Z.le_min_r;
       pose proof (Z.mul_div_le d a Ha) as Hmd; nia)
    | (assert (Hc0 : cdiv (Z.min (-1) d) (b + 1) <= 0) by
         (apply cdiv_ub; [lia | assert (Hml : Z.min (-1) d <= -1) by apply Z.le_min_l; lia]);
       assert (Hmn : Z.min zu (cdiv (Z.min (-1) d) (b + 1) - 1) <= cdiv (Z.min (-1) d) (b + 1) - 1)
         by apply Z.le_min_r;
       lia) ].
Qed.

Lemma zpos_2c : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> 0 < lo ix2 -> ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false -> ((hi iy2 <? 0) && (lo iy2 <=? 0))%bool = false ->
  cdiv (lo iy2) (lo ix2) <= lo iz /\ hi iz <= hi iy2 / lo ix2.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gx Gc Gd.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  assert (Hylo : lo iy2 <= 0).
  { destruct (Z_le_gt_dec (lo iy2) 0) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    assert (Hcc : ((0 <=? lo iy2) && (0 <? hi iy2))%bool = true).
    { apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    congruence. }
  assert (Hyhi : 0 <= hi iy2).
  { destruct (Z_le_gt_dec 0 (hi iy2)) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    assert (Hcc : ((hi iy2 <? 0) && (lo iy2 <=? 0))%bool = true).
    { apply andb_true_intro. split; [apply Z.ltb_lt; lia | apply Z.leb_le; lia]. }
    congruence. }
  split.
  - apply cdiv_ub; [exact Gx |].
    assert (Hp : 0 < lo ix2 * lo iz) by (apply Z.mul_pos_pos; [exact Gx | exact Hizpos]).
    lia.
  - assert (HUB : lo ix2 * hi iz <= hi iy2).
    { rewrite Eiy2hi. apply Z.min_glb.
      - rewrite Eix2lo.
        destruct (Z.max_spec (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz))) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
        + assert (HcX : Xlo (lo iy) (hi iy) (lo iz) (hi iz) <= hi iy / hi iz).
          { unfold Xlo. apply Z.le_trans with (Z.min (hi iy / lo iz) (hi iy / hi iz)); apply Z.le_min_r. }
          apply Z.le_trans with ((hi iy / hi iz) * hi iz);
            [ apply Z.mul_le_mono_nonneg_r; [lia|exact HcX] | rewrite Z.mul_comm; apply Z.mul_div_le; lia ].
        + assert (Hlo1 : 0 < lo ix1) by lia.
          assert (Hdy : 0 < hi iy).
          { apply (fden_hi_pos ix1 iy iz0); [exact Hlo1 | exact Hne_ix1 | lia]. }
          apply Z.le_trans with (lo ix1 * hi (fden ix1 iy iz0));
            [ apply Z.mul_le_mono_nonneg_l; [lia|exact He2] | apply fden_ub_mul_pos; [exact Hlo1|exact Hdy] ].
      - unfold Yhi. apply Z.le_trans with (Z.max (lo ix2 * lo iz) (lo ix2 * hi iz)); [apply Z.le_max_r | apply Z.le_max_l]. }
    apply Z.div_le_lower_bound; [lia|exact HUB].
Qed.
