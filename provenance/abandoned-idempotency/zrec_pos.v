From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ===== template row 2a (from dev.v) ===== *)
Lemma zpos_2a : forall ix1 iy iz0 iz ix2 iy2,
  0 < lo iz0 -> ile ix1 (Cx iy iz0) ->
  iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) ->
  lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 ->
  0 < lo ix2 -> 0 <= lo iy2 -> 0 < hi iy2 ->
  Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= hi iy2 / lo ix2.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Ga Gc Gd.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  assert (Hdy : 0 < hi iy) by (rewrite Eiy2hi in Gd; lia).
  split.
  - assert (Hkey : Z.max 1 (lo iy2) < (hi ix2 + 1) * lo iz).
    { rewrite Eiy2lo. apply Z.max_lub_lt; [ | apply Z.max_lub_lt ].
      - assert (0 < hi ix2) by lia.
        apply Z.lt_le_trans with (2 * 1); [lia | apply Z.mul_le_mono_nonneg; lia].
      - rewrite Eix2hi.
        destruct (Z.min_spec (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
        + destruct (Z_le_gt_dec (lo iy) 0) as [Hyle|Hygt].
          * assert (Hb1 : 0 < hi ix1) by (rewrite Eix2hi in Nx2; lia).
            apply Z.le_lt_trans with 0; [lia | apply Z.mul_pos_pos; lia].
          * assert (Hx1nn : 0 <= lo ix1).
            { apply Z.le_trans with (Xlo (lo iy) (hi iy) (lo iz0) (hi iz0)); [| exact Htp].
              unfold Xlo; repeat apply Z.min_glb; apply Z.div_pos; lia. }
            assert (Hb1 : 0 < hi ix1) by (rewrite Eix2hi in Nx2; lia).
            pose proof (fden_loiy_pos ix1 iy iz0 Hx1nn Hne_ix1 Hz0 ltac:(lia) Hne_iy) as Hlt2.
            assert (Hm : (hi ix1 + 1) * lo (fden ix1 iy iz0) <= (hi ix1 + 1) * lo iz)
              by (apply Z.mul_le_mono_nonneg_l; [lia|exact He1]).
            lia.
        + assert (HdX : hi iy / lo iz <= Xhi (lo iy) (hi iy) (lo iz) (hi iz)).
          { unfold Xhi. apply Z.le_trans with (Z.max (hi iy / lo iz) (hi iy / hi iz)); [apply Z.le_max_l | apply Z.le_max_r]. }
          assert (Hsucc : hi iy < lo iz * (hi iy / lo iz + 1)) by (apply Z.mul_succ_div_gt; lia).
          clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
          nia.
      - assert (HYc : Ylo (lo ix2) (hi ix2) (lo iz) (hi iz) <= lo ix2 * lo iz).
        { unfold Ylo. apply Z.le_trans with (Z.min (lo ix2 * lo iz) (lo ix2 * hi iz)); apply Z.le_min_l. }
        clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
        nia. }
    assert (Z.max 1 (lo iy2) / (hi ix2 + 1) < lo iz) by (apply Z.div_lt_upper_bound; [lia|exact Hkey]).
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
          apply Z.le_trans with (lo ix1 * hi (fden ix1 iy iz0));
            [ apply Z.mul_le_mono_nonneg_l; [lia|exact He2] | apply fden_ub_mul_pos; [exact Hlo1|exact Hdy] ].
      - unfold Yhi. apply Z.le_trans with (Z.max (lo ix2 * lo iz) (lo ix2 * hi iz)); [apply Z.le_max_r | apply Z.le_max_l]. }
    apply Z.div_le_lower_bound; [lia|exact HUB].
Qed.

(* ===== row 2b ===== *)

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

(* ===== row 2c ===== *)

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

(* ===== row 3a ===== *)

Lemma zpos_3a : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= 0 -> hi ix2 < -1 -> 0 <= lo iy2 -> 0 < hi iy2 ->
  hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= lo iy2 / lo ix2.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gxl Gxu Gyl Gyu.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (Hxl : lo ix2 < 0) by lia.
  assert (Hzu : 0 < hi iz) by lia.
  assert (HYhi : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) < 0).
  { clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
    unfold Yhi. apply Z.max_lub_lt; apply Z.max_lub_lt; nia. }
  assert (Hmin : hi iy2 <= Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { rewrite Eiy2hi. apply Z.le_min_r. }
  clear - Gyu Hmin HYhi.
  lia.
Qed.

(* ===== row 3b ===== *)

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

(* ===== row 3c ===== *)

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

(* ===== row 4a ===== *)

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

(* ===== row 4b ===== *)

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

(* ===== row 5a ===== *)

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

(* ===== row 5b ===== *)

Lemma zpos_5b : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2 ->
  hi iz <= Z.max 1 (lo iy2) / lo ix2.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Ga Gb Gc Gd Ge.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (Hzu : 0 < hi iz) by lia.
  assert (HY : Yhi (lo ix2) (hi ix2) (lo iz) (hi iz) <= -1).
  { unfold Yhi. rewrite Gb.
    clear Diz Dx2 Dy2 Ht Htp Htq Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Nz Nx2 Ny2 Hz0 Hz0hi Hne_ix1 Hne_iy Gc Ge.
    repeat apply Z.max_lub; nia. }
  rewrite Eiy2hi in Gd.
  pose proof (Z.le_min_r (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))) as Hmin.
  lia.
Qed.

(* ===== row 5c ===== *)

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

(* ===== row 6a ===== *)

Lemma zpos_6a : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 = 0 -> 0 < hi ix2 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gxlo Gxhi Gylo Gyhi.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  exfalso.
  assert (Hnn : 0 <= Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)).
  { rewrite Gxlo. unfold Ylo.
    clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq Ny2 Nx2.
    apply Z.min_glb.
    - apply Z.min_glb; nia.
    - apply Z.min_glb; nia. }
  assert (0 <= lo iy2).
  { rewrite Eiy2lo. apply Z.le_trans with (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz));
      [exact Hnn | apply Z.le_max_r]. }
  lia.
Qed.

(* ===== row 6b ===== *)

Lemma zpos_6b : forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> lo ix2 = 0 -> 0 < hi ix2 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2 ->
  Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 Gx2lo Gx2hi Gbool Gy2hi Gy2lo.
  zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  assert (Hdy : 0 < hi iy) by (rewrite Eiy2hi in Gy2hi; lia).
  assert (Hb1 : 0 < hi ix1).
  { pose proof Gx2hi as H. rewrite Eix2hi in H. lia. }
  assert (Hkey : Z.max 1 (lo iy2) < (hi ix2 + 1) * lo iz).
  { rewrite Eiy2lo. apply Z.max_lub_lt; [ | apply Z.max_lub_lt ].
    - apply Z.lt_le_trans with (2 * 1); [lia | apply Z.mul_le_mono_nonneg; lia].
    - rewrite Eix2hi.
      destruct (Z.min_spec (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
      + destruct (Z_le_gt_dec (lo iy) 0) as [Hyle|Hygt].
        * apply Z.le_lt_trans with 0; [lia | apply Z.mul_pos_pos; lia].
        * assert (Hx1nn : 0 <= lo ix1).
          { apply Z.le_trans with (Xlo (lo iy) (hi iy) (lo iz0) (hi iz0)); [| exact Htp].
            unfold Xlo; repeat apply Z.min_glb; apply Z.div_pos; lia. }
          pose proof (fden_loiy_pos ix1 iy iz0 Hx1nn Hne_ix1 Hz0 ltac:(lia) Hne_iy) as Hlt2.
          assert (Hm : (hi ix1 + 1) * lo (fden ix1 iy iz0) <= (hi ix1 + 1) * lo iz)
            by (apply Z.mul_le_mono_nonneg_l; [lia|exact He1]).
          lia.
      + assert (HdX : hi iy / lo iz <= Xhi (lo iy) (hi iy) (lo iz) (hi iz)).
        { unfold Xhi. apply Z.le_trans with (Z.max (hi iy / lo iz) (hi iy / hi iz)); [apply Z.le_max_l | apply Z.le_max_r]. }
        assert (Hsucc : hi iy < lo iz * (hi iy / lo iz + 1)) by (apply Z.mul_succ_div_gt; lia).
        clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
        nia.
    - assert (HYc : Ylo (lo ix2) (hi ix2) (lo iz) (hi iz) <= lo ix2 * lo iz).
      { unfold Ylo. apply Z.le_trans with (Z.min (lo ix2 * lo iz) (lo ix2 * hi iz)); apply Z.le_min_l. }
      clear Diz Dx2 Dy2 Eizlo Eizhi Eix2lo Eix2hi Eiy2lo Eiy2hi He1 He2 Ht Htp Htq.
      nia. }
  assert (Z.max 1 (lo iy2) / (hi ix2 + 1) < lo iz) by (apply Z.div_lt_upper_bound; [lia|exact Hkey]).
  lia.
Qed.

(* ===== assembly: Zrec_pos ===== *)
Lemma Zrec_pos : forall ix1 iy iz0 iz ix2 iy2,
  0 < lo iz0 -> ile ix1 (Cx iy iz0) ->
  iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) ->
  lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 ->
  ile iz (fden ix2 iy2 iz).
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  unfold ile. unfold fden; cbv zeta.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end; cbn iota).
  all: cbn [lo hi].
  all: repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    end.
  all: try (split; lia).
  (* remaining 13 nontrivial rows, in fden branch order *)
  - destruct (zpos_2a ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia)) as [L R]; split; lia.
  - destruct (zpos_2b ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia)) as [L R]; split; lia.
  - destruct (zpos_2c ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(assumption) ltac:(assumption)) as [L R]; split; lia.
  - destruct (zpos_3a ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [L R]; split; lia.
  - destruct (zpos_3b ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [L R]; split; lia.
  - destruct (zpos_3c ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption)) as [L R]; split; lia.
  - pose proof (zpos_4a ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia)) as HH; split; lia.
  - pose proof (zpos_4b ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia)) as HH; split; lia.
  - pose proof (zpos_5a ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HH; split; lia.
  - pose proof (zpos_5b ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia)) as HH; split; lia.
  - destruct (zpos_5c ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(lia)) as [L R]; split; lia.
  - pose proof (zpos_6a ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HH; split; lia.
  - pose proof (zpos_6b ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia)) as HH; split; lia.
Qed.

Print Assumptions Zrec_pos.
