From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* When x = [0,0] and hi iy >= 0 (with lo iy > 0), the pass-1 [fden] Z-class
   branch refines the divisor lower bound to at least [lo iy + 1]. *)
Lemma fden_Z_loiy : forall ix iy iz,
  lo ix = 0 -> hi ix = 0 -> 0 < lo iy -> 0 <= hi iy ->
  lo iy + 1 <= lo (fden ix iy iz).
Proof.
  intros ix iy iz Ha Hb Hc Hd. unfold fden; cbv zeta.
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
  all: try lia.
  all: apply Z.le_max_r.
Qed.

Lemma zpos_4b : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 = 0 -> hi ix2 = 0 -> 0 <= hi iy2 ->
  lo iy2 + 1 <= lo iz.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gx0lo Gx0hi Ghy.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  (* [Ylo] over x=[0,0] is <= 0 *)
  assert (HYub : Ylo (lo ix2) (hi ix2) (lo iz) (hi iz) <= 0).
  { rewrite Gx0lo, Gx0hi. unfold Ylo.
    apply Z.le_trans with (Z.min (0 * lo iz) (0 * hi iz)); [apply Z.le_min_l|].
    apply Z.le_trans with (0 * lo iz); [apply Z.le_min_l|]. lia. }
  (* Key: lo iy < lo iz *)
  assert (Hkey : lo iy < lo iz).
  { destruct (Z_le_gt_dec (lo iy) 0) as [Hyle | Hygt].
    - lia.
    - destruct (Z_lt_le_dec (hi iy) (lo iz)) as [HA | HB].
      + lia.
      + (* hi iy >= lo iz, lo iy > 0: force ix1 = [0,0] and use fden *)
        assert (Hxlo0 : 0 <= Xlo (lo iy) (hi iy) (lo iz0) (hi iz0)).
        { unfold Xlo. repeat apply Z.min_glb; apply Z.div_pos; lia. }
        assert (Hlo1_nn : 0 <= lo ix1)
          by (apply Z.le_trans with (Xlo (lo iy) (hi iy) (lo iz0) (hi iz0)); [exact Hxlo0 | exact Htp]).
        assert (Hlo1_np : lo ix1 <= 0).
        { rewrite Eix2lo in Gx0lo.
          pose proof (Z.le_max_l (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz))) as Hml. lia. }
        assert (Hlo1_0 : lo ix1 = 0) by lia.
        assert (HXhi_pos : 1 <= Xhi (lo iy) (hi iy) (lo iz) (hi iz)).
        { apply Z.le_trans with (hi iy / lo iz).
          - apply Z.div_le_lower_bound; lia.
          - unfold Xhi.
            apply Z.le_trans with (Z.max (hi iy / lo iz) (hi iy / hi iz)); [apply Z.le_max_l | apply Z.le_max_r]. }
        assert (Hhi1_0 : hi ix1 = 0).
        { rewrite Eix2hi in Gx0hi.
          destruct (Z.min_spec (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) as [[H1 H2]|[H1 H2]];
            rewrite H2 in Gx0hi; lia. }
        pose proof (fden_Z_loiy ix1 iy iz0 Hlo1_0 Hhi1_0 ltac:(lia) ltac:(lia)) as Hfd.
        lia. }
  rewrite Eiy2lo.
  assert (Hm : Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)) <= lo iz - 1)
    by (apply Z.max_lub; lia).
  lia.
Qed.
