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
