From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Definition Cx (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).
Definition Cy (ix iz : itv) : itv :=
  Itv (Ylo (lo ix) (hi ix) (lo iz) (hi iz)) (Yhi (lo ix) (hi ix) (lo iz) (hi iz)).

Lemma X_recover_pos : forall a b yl yu zl zu,
  0 < zl -> 0 < zu ->
  Xlo yl yu zl zu <= a ->
  b <= Xhi yl yu zl zu ->
  Xlo (Z.max yl (Ylo a b zl zu)) (Z.min yu (Yhi a b zl zu)) zl zu <= a /\
  b <= Xhi (Z.max yl (Ylo a b zl zu)) (Z.min yu (Yhi a b zl zu)) zl zu.
Proof.
  intros a b yl yu zl zu Hzl Hzu H1 H2.
  set (Yl := Ylo a b zl zu) in *. set (Yh := Yhi a b zl zu) in *.
  assert (Ea : a * zl / zl = a) by (apply Z.div_mul; lia).
  assert (Eb : b * zl / zl = b) by (apply Z.div_mul; lia).
  assert (Corner1 : Yl <= a * zl) by (unfold Yl, Ylo; lia).
  assert (Corner2 : b * zl <= Yh) by (unfold Yh, Yhi; lia).
  assert (HYlzl : Yl / zl <= a).
  { apply Z.le_trans with (a * zl / zl); [ apply Z.div_le_mono; [lia|exact Corner1] | rewrite Ea; lia ]. }
  assert (HYhzl : b <= Yh / zl).
  { rewrite <- Eb. apply Z.div_le_mono; [lia|exact Corner2]. }
  unfold Xlo, Xhi in *.
  destruct (Z.max_spec yl Yl) as [[Hml Hme]|[Hml Hme]]; rewrite Hme;
  destruct (Z.min_spec yu Yh) as [[Hnl Hne]|[Hnl Hne]]; rewrite Hne.
  all: (
    try assert (yl / zl <= Yl / zl) by (apply Z.div_le_mono; lia);
    try assert (yl / zu <= Yl / zu) by (apply Z.div_le_mono; lia);
    try assert (Yh / zl <= yu / zl) by (apply Z.div_le_mono; lia);
    try assert (Yh / zu <= yu / zu) by (apply Z.div_le_mono; lia);
    split; lia).
Qed.

Lemma X_recover_neg : forall a b yl yu zl zu,
  zl < 0 -> zu < 0 ->
  Xlo yl yu zl zu <= a ->
  b <= Xhi yl yu zl zu ->
  Xlo (Z.max yl (Ylo a b zl zu)) (Z.min yu (Yhi a b zl zu)) zl zu <= a /\
  b <= Xhi (Z.max yl (Ylo a b zl zu)) (Z.min yu (Yhi a b zl zu)) zl zu.
Proof.
  intros a b yl yu zl zu Hzl Hzu H1 H2.
  set (Yl := Ylo a b zl zu) in *. set (Yh := Yhi a b zl zu) in *.
  assert (Ea : a * zl / zl = a) by (apply Z.div_mul; lia).
  assert (Eb : b * zl / zl = b) by (apply Z.div_mul; lia).
  assert (CornerH : a * zl <= Yh) by (unfold Yh, Yhi; lia).
  assert (CornerL : Yl <= b * zl) by (unfold Yl, Ylo; nia).
  assert (Nlo : Yh / zl <= a).
  { apply Z.le_trans with (a * zl / zl); [ apply div_le_mono_num_neg; [lia|exact CornerH] | rewrite Ea; lia ]. }
  assert (Nup : b <= Yl / zl).
  { rewrite <- Eb. apply div_le_mono_num_neg; [lia|exact CornerL]. }
  unfold Xlo, Xhi in *.
  destruct (Z.max_spec yl Yl) as [[Hml Hme]|[Hml Hme]]; rewrite Hme;
  destruct (Z.min_spec yu Yh) as [[Hnl Hne]|[Hnl Hne]]; rewrite Hne.
  all: (
    try assert (Yl / zl <= yl / zl) by (apply div_le_mono_num_neg; lia);
    try assert (Yl / zu <= yl / zu) by (apply div_le_mono_num_neg; lia);
    try assert (yu / zl <= Yh / zl) by (apply div_le_mono_num_neg; lia);
    try assert (yu / zu <= Yh / zu) by (apply div_le_mono_num_neg; lia);
    split; lia).
Qed.

(* ---------- abstract multiplicative bounds on pass-1 fden (positive x) ---------- *)

(* Upper: with an all-positive x-interval and a positive-topped y-interval,
   [lo ix] times the refined-z upper bound never exceeds [hi iy]. *)
Lemma fden_ub_mul_pos : forall ix iy iz,
  0 < lo ix -> 0 < hi iy -> lo ix * hi (fden ix iy iz) <= hi iy.
Proof.
  intros ix iy iz Ha Hd. unfold fden; cbv zeta.
  set (a := lo ix) in *. set (b := hi ix) in *.
  set (c := lo iy) in *. set (d := hi iy) in *.
  set (zl := lo iz) in *. set (zu := hi iz) in *.
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
  all: try lia.
  all: apply Z.le_trans with (a * (d / a));
    [ apply Z.mul_le_mono_nonneg_l; [lia | apply Z.le_min_r]
    | apply Z.mul_div_le; lia ].
Qed.

(* Lower: with an all-positive, nonempty x-interval, [max 1 (lo iy)] is
   strictly below [(hi ix + 1)] times the refined-z lower bound. *)
Lemma fden_lb_mul_pos : forall ix iy iz,
  0 < lo ix -> lo ix <= hi ix -> 0 < lo iz -> lo iy <= hi iy ->
  Z.max 1 (lo iy) < (hi ix + 1) * lo (fden ix iy iz).
Proof.
  intros ix iy iz Ha Hab Hzl Hiyne. unfold fden; cbv zeta.
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
  all: try (assert (Hfl : 1 <= Z.max zl (cdiv c a)) by lia; nia).
  all: assert (Hgt : Z.max 1 c < (b + 1) * (Z.max 1 c / (b + 1) + 1)) by (apply Z.mul_succ_div_gt; lia).
  all: assert (Hmul : (b + 1) * (Z.max 1 c / (b + 1) + 1) <= (b + 1) * Z.max zl (Z.max 1 c / (b + 1) + 1))
         by (apply Z.mul_le_mono_nonneg_l; [lia | apply Z.le_max_r]).
  all: lia.
Qed.

(* With a nonempty x-interval of nonnegative lower bound and a strictly
   positive y lower bound, [lo iy] is strictly below [(hi ix + 1)] times the
   refined-z lower bound.  Covers pass-1 x-classes P1 / P0 / Z. *)
Lemma fden_loiy_pos : forall ix iy iz,
  0 <= lo ix -> lo ix <= hi ix -> 0 < lo iz -> 0 < lo iy -> lo iy <= hi iy ->
  lo iy < (hi ix + 1) * lo (fden ix iy iz).
Proof.
  intros ix iy iz Ha Hab Hzl Hc Hiyne. unfold fden; cbv zeta.
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
  all: try (assert (Hgt : Z.max 1 c < (b + 1) * (Z.max 1 c / (b + 1) + 1)) by (apply Z.mul_succ_div_gt; lia);
            assert (Hmul : (b + 1) * (Z.max 1 c / (b + 1) + 1) <= (b + 1) * Z.max zl (Z.max 1 c / (b + 1) + 1))
              by (apply Z.mul_le_mono_nonneg_l; [lia | apply Z.le_max_r]);
            lia).
Qed.

(* Packaged derived facts shared by every standalone row obligation. *)
Lemma zpos_ctx : forall ix1 iy iz0 iz ix2 iy2,
  0 < lo iz0 -> ile ix1 (Cx iy iz0) ->
  iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) ->
  lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 ->
  Xlo (lo iy) (hi iy) (lo iz0) (hi iz0) <= lo ix1 /\
  hi ix1 <= Xhi (lo iy) (hi iy) (lo iz0) (hi iz0) /\
  lo iz = Z.max (lo iz0) (lo (fden ix1 iy iz0)) /\
  hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0)) /\
  lo ix2 = Z.max (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) /\
  hi ix2 = Z.min (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)) /\
  lo iy2 = Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz)) /\
  hi iy2 = Z.min (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz)) /\
  lo (fden ix1 iy iz0) <= lo iz /\ hi iz <= hi (fden ix1 iy iz0) /\
  0 < lo iz /\ lo ix1 <= hi ix1 /\ lo iy <= hi iy /\ 0 < hi iz0.
Proof.
  intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2.
  unfold Cx, Cy in Ht, Dx2, Dy2.
  assert (Htp : Xlo (lo iy) (hi iy) (lo iz0) (hi iz0) <= lo ix1)
    by (destruct Ht as [HA HB]; cbn [lo hi] in *; lia).
  assert (Htq : hi ix1 <= Xhi (lo iy) (hi iy) (lo iz0) (hi iz0))
    by (destruct Ht as [HA HB]; cbn [lo hi] in *; lia).
  assert (Eizlo : lo iz = Z.max (lo iz0) (lo (fden ix1 iy iz0))) by (rewrite Diz; reflexivity).
  assert (Eizhi : hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0))) by (rewrite Diz; reflexivity).
  assert (Eix2lo : lo ix2 = Z.max (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz))) by (rewrite Dx2; reflexivity).
  assert (Eix2hi : hi ix2 = Z.min (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) by (rewrite Dx2; reflexivity).
  assert (Eiy2lo : lo iy2 = Z.max (lo iy) (Ylo (lo ix2) (hi ix2) (lo iz) (hi iz))) by (rewrite Dy2; reflexivity).
  assert (Eiy2hi : hi iy2 = Z.min (hi iy) (Yhi (lo ix2) (hi ix2) (lo iz) (hi iz))) by (rewrite Dy2; reflexivity).
  assert (Hne_ix1 : lo ix1 <= hi ix1) by (rewrite Eix2lo, Eix2hi in Nx2; lia).
  assert (Hne_iy : lo iy <= hi iy) by (rewrite Eiy2lo, Eiy2hi in Ny2; lia).
  assert (He1 : lo (fden ix1 iy iz0) <= lo iz) by (rewrite Eizlo; lia).
  assert (He2 : hi iz <= hi (fden ix1 iy iz0)) by (rewrite Eizhi; lia).
  assert (Hizpos : 0 < lo iz) by (rewrite Eizlo; lia).
  assert (Hz0hi : 0 < hi iz0) by (rewrite Eizlo, Eizhi in Nz; lia).
  repeat split; assumption.
Qed.

Ltac zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 :=
  destruct (zpos_ctx _ _ _ _ _ _ Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2)
    as [Htp [Htq [Eizlo [Eizhi [Eix2lo [Eix2hi [Eiy2lo [Eiy2hi [He1 [He2 [Hizpos [Hne_ix1 [Hne_iy Hz0hi]]]]]]]]]]]]].

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

(* ---------- z-recovery for the positive branch (fden self-stability) ---------- *)

Lemma Zrec_pos : forall ix1 iy iz0 iz ix2 iy2,
  0 < lo iz0 ->
  ile ix1 (Cx iy iz0) ->
  iz  = inter iz0 (fden ix1 iy iz0) ->
  ix2 = inter ix1 (Cx iy iz) ->
  iy2 = inter iy (Cy ix2 iz) ->
  lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 ->
  ile iz (fden ix2 iy2 iz).
Proof.
Admitted.
