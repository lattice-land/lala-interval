From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma helperB : forall ix iy iz,
  lo ix <= hi ix -> hi ix < -1 -> 0 < lo iz -> lo iy <= hi iy -> lo iy < 0 ->
  lo iy < (hi ix + 1) * hi (fden ix iy iz).
Proof.
  intros ix iy iz Hab Hb Hzl Hne Hc. unfold fden; cbv zeta.
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
  all: assert (Hbr := div_bracket_neg (-c) (b+1) ltac:(lia)); unfold cdiv in *; set (P := (-c)/(b+1)) in *; assert (Hm : Z.min zu (- P - 1) <= - P - 1) by apply Z.le_min_r; nia.
Qed.

Lemma helperA : forall ix iy iz,
  lo ix <= hi ix -> hi ix < 0 -> lo ix < 0 -> 0 < lo iz -> lo iy <= hi iy -> lo iy < 0 ->
  lo ix * lo (fden ix iy iz) <= hi iy.
Proof.
  intros ix iy iz Hab Hb Ha Hzl Hne Hc. unfold fden; cbv zeta.
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
  - assert (Hbr := div_bracket_neg (-d) a ltac:(lia)); unfold cdiv in *; set (P := (-d)/a) in *; assert (Hm : -P <= Z.max zl (-P)) by apply Z.le_max_r; nia.
  - assert (Hd0 : 0 < d) by (destruct (Z_lt_le_dec 0 d) as [|Hdle]; [lia|]; assert (Hcon : ((c <? 0) && (d <=? 0))%bool = true) by (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia); congruence); assert (Hmx : 0 <= Z.max zl (d/(b+1)+1)) by (apply Z.le_trans with zl;[lia|apply Z.le_max_l]); nia.
  - assert (Hbr := div_bracket_neg (-(Z.min (-1) d)) a ltac:(lia)); unfold cdiv in *; set (Q := (-(Z.min (-1) d))/a) in *; assert (Hm : - Q <= Z.max zl (- Q)) by apply Z.le_max_r; assert (Hmin : Z.min (-1) d <= d) by apply Z.le_min_r; nia.
Qed.

Lemma zpos_3b : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= 0 -> hi ix2 < -1 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  cdiv (hi iy2) (lo ix2) <= lo iz /\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Ga Gb Gc Gd.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  assert (Halo : lo ix2 <= -2) by lia.
  assert (Haneg : lo ix2 < 0) by lia.
  assert (Hbneg : hi ix2 < 0) by lia.
  assert (Hb1neg : hi ix2 + 1 < 0) by lia.
  assert (Hcy : lo iy < 0) by (rewrite Eiy2lo in Gc; lia).
  split.
  - apply cdiv_ub_neg; [lia|].
    rewrite Eiy2hi. apply Z.min_glb.
    2:{ unfold Yhi. apply Z.le_trans with (Z.max (lo ix2 * lo iz) (lo ix2 * hi iz)); [apply Z.le_max_l | apply Z.le_max_l]. }
    destruct (Z_lt_le_dec (hi iy) 0) as [Hyn|Hyp]; [| nia ].
    assert (HXneg : Xhi (lo iy) (hi iy) (lo iz0) (hi iz0) < 0) by (unfold Xhi; repeat apply Z.max_lub_lt; apply Z.div_lt_upper_bound; lia).
    assert (Hix1b : hi ix1 < 0) by lia.
    assert (Hix1lo : lo ix1 < 0) by lia.
    pose proof (helperA ix1 iy iz0 Hne_ix1 Hix1b Hix1lo Hz0 Hne_iy Hcy) as HA.
    rewrite Eix2lo.
    destruct (Z.max_spec (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz))) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
    + assert (HcX : Xlo (lo iy) (hi iy) (lo iz) (hi iz) <= hi iy / lo iz) by (unfold Xlo; apply Z.le_trans with (Z.min (hi iy / lo iz) (hi iy / hi iz)); [apply Z.le_min_r | apply Z.le_min_l]).
      apply Z.le_trans with ((hi iy / lo iz) * lo iz); [apply Z.mul_le_mono_nonneg_r; [lia|exact HcX] | rewrite Z.mul_comm; apply Z.mul_div_le; lia].
    + assert (Hmul : lo ix1 * lo iz <= lo ix1 * lo (fden ix1 iy iz0)) by (apply Z.mul_le_mono_nonpos_l; [lia|exact He1]).
      lia.
  - assert (Hhz : 0 < hi iz) by lia.
    assert (Hkey : lo iy2 < (hi ix2 + 1) * hi iz).
    { rewrite Eiy2lo. apply Z.max_lub_lt.
      - rewrite Eix2hi. destruct (Z.min_spec (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
        + assert (Hb1 : hi ix1 < -1) by (assert (Hxx : hi ix2 = hi ix1) by (rewrite Eix2hi; exact Heq); lia).
          pose proof (helperB ix1 iy iz0 Hne_ix1 Hb1 Hz0 Hne_iy Hcy) as HB.
          assert (Hmul : (hi ix1 + 1) * hi (fden ix1 iy iz0) <= (hi ix1 + 1) * hi iz) by (apply Z.mul_le_mono_nonpos_l; [lia|exact He2]).
          lia.
        + assert (HdX : lo iy / hi iz <= Xhi (lo iy) (hi iy) (lo iz) (hi iz)) by (unfold Xhi; apply Z.le_trans with (Z.max (lo iy / lo iz) (lo iy / hi iz)); [apply Z.le_max_r | apply Z.le_max_l]).
          assert (Hsucc : lo iy < hi iz * (lo iy / hi iz + 1)) by (apply Z.mul_succ_div_gt; lia).
          clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq Hge.
          nia.
      - assert (HYc : Ylo (lo ix2) (hi ix2) (lo iz) (hi iz) <= lo ix2 * hi iz) by (unfold Ylo; apply Z.le_trans with (Z.min (lo ix2 * lo iz) (lo ix2 * hi iz)); [apply Z.le_min_l | apply Z.le_min_r]).
        clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
        nia. }
    assert (Hstep : hi iz + 1 <= cdiv (lo iy2) (hi ix2 + 1)).
    { apply cdiv_lb_neg; [lia|].
      clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
      nia. }
    lia.
Qed.
