(** This file in_zitv all the definitions and theorems relevant to the concrete domain. *)

From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.

(** Ceiling division for arbitrary signs: [cdiv a b = ceil(a/b) = -floor(-a/b)]. *)
Definition cdiv (a b : Z) : Z := - ((- a) / b).

(* The addition constraint as a ternary relation. *)
Definition add_rel (x y z : Z) : Prop := x = y + z.

(** The constraint relation: floored division with non-zero divisor. *)
Definition fdiv_rel (x y z : Z) : Prop := z <> 0 /\ x =  y / z.
Definition cdiv_rel (x y z : Z) : Prop := z <> 0 /\ x = cdiv y z.
Definition ediv_rel (x y z : Z) : Prop := z <> 0 /\ x = (if 0 <? z then y / z else cdiv y z).
Definition tdiv_rel (x y z : Z) : Prop := z <> 0 /\ x = Z.quot y z.
Definition mul_rel (x y z : Z) : Prop := x = y * z.

Lemma fdiv_cdiv_xy_equiv : forall vx vy vz, fdiv_rel vx vy vz -> cdiv_rel (- vx) (- vy) vz.
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  unfold cdiv. rewrite Z.opp_involutive. lia.
Qed.

Lemma fdiv_cdiv_xz_equiv : forall vx vy vz, fdiv_rel vx vy vz -> cdiv_rel (- vx) vy (- vz).
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  unfold cdiv. rewrite Z.div_opp_opp by lia. lia.
Qed.

(* ---- euclidean/floor solution correspondence ---- *)
Lemma fdiv_ediv_equiv_if_z_lt_0 : forall vx vy vz, fdiv_rel vx vy vz -> 0 < vz -> ediv_rel vx vy vz.
Proof.
  intros vx vy vz [Hnz Hq] Hpos. split; [lia | ].
  rewrite (proj2 (Z.ltb_lt 0 vz) Hpos). exact Hq.
Qed.

Lemma fdiv_ediv_xz_equiv_if_z_lt_0 : forall vx vy vz, fdiv_rel vx vy vz -> 0 < vz -> ediv_rel (- vx) vy (- vz).
Proof.
  intros vx vy vz Hsol Hpos. destruct (fdiv_cdiv_xz_equiv vx vy vz Hsol) as [Hnz Hq].
  split; [lia | ]. rewrite (proj2 (Z.ltb_ge 0 (- vz)) ltac:(lia)). exact Hq.
Qed.

(** Helper lemmas *)

Lemma fdiv_lt_neg : forall n M q, M < 0 -> M * q < n -> n / M < q.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B. nia.
Qed.

Lemma fdiv_lb_neg : forall n M q, M < 0 -> n <= M * q -> q <= n / M.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B. nia.
Qed.

(* ---- band membership (pre-image band -> quotient in [xl,xu]) ---- *)
Lemma band_pos : forall xl xu z Y,
  0 < z -> xl * z <= Y -> Y <= (xu+1)*z - 1 -> xl <= Y / z <= xu.
Proof.
  intros xl xu z Y Hz H1 H2. split.
  - apply Z.div_le_lower_bound; [lia | nia].
  - assert (Y / z < xu + 1) by (apply Z.div_lt_upper_bound; [lia | nia]). lia.
Qed.

Lemma band_neg : forall xl xu z Y,
  z < 0 -> (xu+1)*z + 1 <= Y -> Y <= xl * z -> xl <= Y / z <= xu.
Proof.
  intros xl xu z Y Hz H1 H2. split.
  - apply fdiv_lb_neg; [lia | nia].
  - assert (Y / z < xu + 1) by (apply fdiv_lt_neg; [lia | nia]). lia.
Qed.

(** Bound lemmas for [cdiv] with positive divisor (mirror of the [Z.div] ones). *)
Lemma cdiv_ub : forall n b q, 0 < b -> n <= b * q -> cdiv n b <= q.
Proof.
  intros n b q Hb H. unfold cdiv.
  assert (- q <= (- n) / b) by (apply Z.div_le_lower_bound; [lia| nia]).
  lia.
Qed.

Lemma cdiv_ub_neg : forall n M q, M < 0 -> M * q <= n -> cdiv n M <= q.
Proof.
  intros n M q HM H. unfold cdiv.
  pose proof (Z.div_mod (- n) M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound (- n) M HM) as B. nia.
Qed.

Lemma div_bracket_pos : forall y z,
  0 < z ->
  z * (y / z) <= y <= z * (y / z + 1) - 1.
Proof.
  intros y z Hz.
  assert (Hz' : z <> 0) by lia.
  pose proof (Z.div_mod y z Hz') as Hdm.
  pose proof (Z.mod_pos_bound y z Hz) as Hmod.
  nia.
Qed.

(** Monotonicity of [Z.div] in the numerator, positive and negative divisor. *)
Lemma div_le_mono_num : forall a b c, 0 < c -> a <= b -> a / c <= b / c.
Proof. intros a b c Hc Hab; apply Z.div_le_mono; assumption. Qed.

(** Divisor monotonicity for a *non-positive* numerator (the case
    [Z.div_le_compat_l] does not cover): [p<=0], [0<q<=r] give [p/q <= p/r]. *)
Lemma div_le_compat_l_neg : forall p q r, p <= 0 -> 0 < q <= r -> p / q <= p / r.
Proof.
  intros p q r Hp [Hq Hqr].
  assert (Hr : 0 < r) by lia.
  destruct (div_bracket_pos p r Hr) as [Hlo Hup].
  assert (p / q < p / r + 1) by (apply Z.div_lt_upper_bound; [nia| nia]).
  nia.
Qed.

(** Negative-divisor bound lemmas, proved uniformly from [Z.div_mod] +
    [Z.mod_neg_bound] + [nia].  [M < 0] throughout. *)
Lemma fdiv_ub_neg : forall n M q, M < 0 -> M * q <= n -> n / M <= q.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B.
  nia.
Qed.

(* --- Finite arithmetic cores --- *)
Lemma mul_min_lb : forall x c v d, c <= v -> v <= d -> Z.min (x*c) (x*d) <= x*v.
Proof.
  intros; destruct (Z.le_ge_cases 0 x);
  [ assert (x*c <= x*v) by nia | assert (x*d <= x*v) by nia ]; lia.
Qed.

Lemma mul_max_ub : forall x c v d, c <= v -> v <= d -> x*v <= Z.max (x*c) (x*d).
Proof.
  intros; destruct (Z.le_ge_cases 0 x);
  [ assert (x*v <= x*d) by nia | assert (x*v <= x*c) by nia ]; lia.
Qed.

Ltac dfacts n m :=
  pose proof (Z.div_mod n m ltac:(lia));
  first [ pose proof (Z.mod_pos_bound n m ltac:(lia))
        | pose proof (Z.mod_neg_bound n m ltac:(lia)) ].

Lemma fdiv_num_max : forall a u b m, m <> 0 -> a <= u -> u <= b -> u / m <= Z.max (a / m) (b / m).
Proof.
  intros a u b m Hm Hau Hub.
  destruct (Z.lt_ge_cases m 0) as [HM|HM]; dfacts a m; dfacts u m; dfacts b m; nia.
Qed.

Lemma cdiv_num_min : forall a u b m, m <> 0 -> a <= u -> u <= b -> Z.min (cdiv a m) (cdiv b m) <= cdiv u m.
Proof.
  intros a u b m Hm Hau Hub. unfold cdiv.
  destruct (Z.lt_ge_cases m 0) as [HM|HM]; dfacts (-a) m; dfacts (-u) m; dfacts (-b) m; nia.
Qed.

Lemma fdiv_den_max_pos : forall n mc m md, 0 < mc -> mc <= m -> m <= md -> n / m <= Z.max (n / mc) (n / md).
Proof.
  intros. destruct (Z.le_ge_cases 0 n) as [Hn|Hn];
  [ assert (n/m <= n/mc) by (apply Z.div_le_compat_l; lia)
  | assert (n/m <= n/md) by (apply div_le_compat_l_neg; lia) ]; lia.
Qed.

Lemma fdiv_den_max_neg : forall n mc m md, md < 0 -> mc <= m -> m <= md -> n / m <= Z.max (n / mc) (n / md).
Proof.
  intros.
  pose proof (fdiv_den_max_pos (-n) (-md) (-m) (-mc) ltac:(lia) ltac:(lia) ltac:(lia)) as H2.
  rewrite (Z.div_opp_opp n md) in H2 by lia.
  rewrite (Z.div_opp_opp n m) in H2 by lia.
  rewrite (Z.div_opp_opp n mc) in H2 by lia. lia.
Qed.

Lemma cdiv_den_min_pos : forall n mc m md, 0 < mc -> mc <= m -> m <= md -> Z.min (cdiv n mc) (cdiv n md) <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_den_max_pos (-n) mc m md ltac:(lia) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma cdiv_den_min_neg : forall n mc m md, md < 0 -> mc <= m -> m <= md -> Z.min (cdiv n mc) (cdiv n md) <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_den_max_neg (-n) mc m md ltac:(lia) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fdiv_mono_pos : forall a b m, 0 < m -> a <= b -> a / m <= b / m.
Proof. intros; apply Z.div_le_mono; lia. Qed.

Lemma div_le_mono_num_neg : forall a b c, c < 0 -> a <= b -> b / c <= a / c.
Proof.
  intros a b c Hc Hab.
  rewrite <- (Z.div_opp_opp a c) by lia.
  rewrite <- (Z.div_opp_opp b c) by lia.
  apply Z.div_le_mono; lia.
Qed.

Lemma fdiv_anti_neg : forall a b m, m < 0 -> a <= b -> b / m <= a / m.
Proof. intros; apply div_le_mono_num_neg; lia. Qed.

Lemma cdiv_mono_pos : forall a b m, 0 < m -> a <= b -> cdiv a m <= cdiv b m.
Proof. intros. unfold cdiv. pose proof (fdiv_mono_pos (-b) (-a) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma cdiv_anti_neg : forall a b m, m < 0 -> a <= b -> cdiv b m <= cdiv a m.
Proof. intros. unfold cdiv. pose proof (fdiv_anti_neg (-b) (-a) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fdiv_neg_pos : forall n m, n < 0 -> 0 < m -> n / m <= -1.
Proof. intros. assert (n / m < 0) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

Lemma fdiv_pos_neg : forall n m, 0 < n -> m < 0 -> n / m <= -1.
Proof. intros. assert (n / m < 0) by (apply fdiv_lt_neg; lia). lia. Qed.

Lemma cdiv_pos_pos : forall n m, 0 < n -> 0 < m -> 1 <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_neg_pos (-n) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma cdiv_neg_neg : forall n m, n < 0 -> m < 0 -> 1 <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_pos_neg (-n) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fdiv_den_pinf_pos : forall n mc m, 0 < mc -> mc <= m -> n / m <= Z.max (n / mc) (if n <? 0 then -1 else 0).
Proof.
  intros. destruct (Z.ltb_spec n 0) as [HN|HN].
  - pose proof (fdiv_neg_pos n m ltac:(lia) ltac:(lia)). lia.
  - assert (n/m <= n/mc) by (apply Z.div_le_compat_l; lia). lia.
Qed.

Lemma fdiv_den_ninf_neg : forall n m md, md < 0 -> m <= md -> n / m <= Z.max (if 0 <? n then -1 else 0) (n / md).
Proof.
  intros. destruct (Z.ltb_spec 0 n) as [HN|HN].
  - pose proof (fdiv_pos_neg n m ltac:(lia) ltac:(lia)). lia.
  - assert (n/m <= n/md).
    { rewrite <- (Z.div_opp_opp n m) by lia. rewrite <- (Z.div_opp_opp n md) by lia.
      apply Z.div_le_compat_l; lia. } lia.
Qed.

Lemma cdiv_den_pinf_pos : forall n mc m, 0 < mc -> mc <= m -> Z.min (cdiv n mc) (if 0 <? n then 1 else 0) <= cdiv n m.
Proof.
  intros. destruct (Z.ltb_spec 0 n) as [HN|HN].
  - pose proof (cdiv_pos_pos n m ltac:(lia) ltac:(lia)). lia.
  - unfold cdiv. assert ((-n)/m <= (-n)/mc) by (apply Z.div_le_compat_l; lia). lia.
Qed.

Lemma cdiv_den_ninf_neg : forall n m md, md < 0 -> m <= md -> Z.min (if n <? 0 then 1 else 0) (cdiv n md) <= cdiv n m.
Proof.
  intros. destruct (Z.ltb_spec n 0) as [HN|HN].
  - pose proof (cdiv_neg_neg n m ltac:(lia) ltac:(lia)). lia.
  - unfold cdiv. assert ((-n)/m <= (-n)/md).
    { rewrite <- (Z.div_opp_opp (-n) m) by lia. rewrite <- (Z.div_opp_opp (-n) md) by lia.
      rewrite Z.opp_involutive. apply Z.div_le_compat_l; lia. } lia.
Qed.

Lemma fdiv_abs_ub : forall n m, m <> 0 -> n / m <= Z.max (- n) n.
Proof.
  intros. destruct (Z.lt_ge_cases m 0) as [HM|HM]; destruct (Z.le_ge_cases 0 n) as [HN|HN].
  - assert (n/m <= 0) by (apply fdiv_ub_neg; lia). lia.
  - assert (n/m <= -n) by (apply fdiv_ub_neg; nia). lia.
  - assert (n/m <= n) by (apply Z.div_le_upper_bound; nia). lia.
  - assert (n/m <= 0) by (dfacts n m; nia). lia.
Qed.

Lemma cdiv_abs_lb : forall n m, m <> 0 -> Z.min n (- n) <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_abs_ub (-n) m H). lia. Qed.
