From Stdlib Require Import ZArith Lia Bool.
Open Scope Z_scope.


(** The constraint relation: floored division with non-zero divisor. *)
Definition sol (x y z : Z) : Prop := z <> 0 /\ x =  y / z.

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

Lemma div_bracket_neg : forall y z,
  z < 0 ->
  z * (y / z + 1) + 1 <= y <= z * (y / z).
Proof.
  intros y z Hz.
  assert (Hz' : z <> 0) by lia.
  pose proof (Z.div_mod y z Hz') as Hdm.
  pose proof (Z.mod_neg_bound y z Hz) as Hmod.
  nia.
Qed.

Lemma mul_between : forall a l u t,
  l <= t <= u ->
  Z.min (a*l) (a*u) <= a*t <= Z.max (a*l) (a*u).
Proof.
  intros a l u t [H1 H2].
  destruct (Z_lt_le_dec a 0) as [Ha|Ha].
  - (* a < 0 *)
    nia.
  - (* 0 <= a *)
    nia.
Qed.



(** Monotonicity of [Z.div] in the numerator, positive and negative divisor. *)
Lemma div_le_mono_num : forall a b c, 0 < c -> a <= b -> a / c <= b / c.
Proof. intros a b c Hc Hab; apply Z.div_le_mono; assumption. Qed.

Lemma div_le_mono_num_neg : forall a b c, c < 0 -> a <= b -> b / c <= a / c.
Proof.
  intros a b c Hc Hab.
  rewrite <- (Z.div_opp_opp a c) by lia.
  rewrite <- (Z.div_opp_opp b c) by lia.
  apply Z.div_le_mono; lia.
Qed.

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


(** Divisor monotonicity, positive-divisor interval: [a/t] lies between the
    two corner quotients [a/cl] and [a/cu]. *)
Lemma div_between_pos_den : forall a cl cu t,
  0 < cl -> cl <= t <= cu ->
  Z.min (a/cl) (a/cu) <= a/t <= Z.max (a/cl) (a/cu).
Proof.
  intros a cl cu t Hcl [Htl Htu].
  assert (Ht : 0 < t) by lia.
  destruct (Z_lt_le_dec a 0) as [Ha|Ha].
  - (* a < 0 *)
    assert (a/cl <= a/t) by (apply div_le_compat_l_neg; lia).
    assert (a/t <= a/cu) by (apply div_le_compat_l_neg; lia).
    nia.
  - (* 0 <= a  *)
    assert (a/cu <= a/t) by (apply Z.div_le_compat_l; lia).
    assert (a/t <= a/cl) by (apply Z.div_le_compat_l; lia).
    nia.
Qed.


(** Divisor monotonicity, negative-divisor interval, by reduction to the
    positive case through [(-a)/(-t) = a/t]. *)
Lemma div_between_neg_den : forall a cl cu t,
  cu < 0 -> cl <= t <= cu ->
  Z.min (a/cl) (a/cu) <= a/t <= Z.max (a/cl) (a/cu).
Proof.
  intros a cl cu t Hcu [Htl Htu].
  rewrite <- (Z.div_opp_opp a cl) by lia.
  rewrite <- (Z.div_opp_opp a cu) by lia.
  rewrite <- (Z.div_opp_opp a t)  by lia.
  rewrite (Z.min_comm (-a/-cl) (-a/-cu)).
  rewrite (Z.max_comm (-a/-cl) (-a/-cu)).
  apply (div_between_pos_den (-a) (-cu) (-cl) (-t)); lia.
Qed.

(** Ceiling division for arbitrary signs: [cdiv a b = ceil(a/b) = -floor(-a/b)]. *)
Definition cdiv (a b : Z) : Z := - ((- a) / b).

(** Bound lemmas for [cdiv] with positive divisor (mirror of the [Z.div] ones). *)
Lemma cdiv_ub : forall n b q, 0 < b -> n <= b * q -> cdiv n b <= q.
Proof.
  intros n b q Hb H. unfold cdiv.
  assert (- q <= (- n) / b) by (apply Z.div_le_lower_bound; [lia| nia]).
  lia.
Qed.

Lemma cdiv_lb : forall n b q, 0 < b -> b * (q - 1) < n -> q <= cdiv n b.
Proof.
  intros n b q Hb H. unfold cdiv.
  assert ((- n) / b < 1 - q) by (apply Z.div_lt_upper_bound; [lia| nia]).
  lia.
Qed.

(** Negative-divisor bound lemmas, proved uniformly from [Z.div_mod] +
    [Z.mod_neg_bound] + [nia].  [M < 0] throughout. *)
Lemma fdiv_ub_neg : forall n M q, M < 0 -> M * q <= n -> n / M <= q.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B.
  nia.
Qed.

Lemma fdiv_lb_neg : forall n M q, M < 0 -> n <= M * q -> q <= n / M.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B. nia.
Qed.

Lemma fdiv_lt_neg : forall n M q, M < 0 -> M * q < n -> n / M < q.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B. nia.
Qed.

Lemma cdiv_ub_neg : forall n M q, M < 0 -> M * q <= n -> cdiv n M <= q.
Proof.
  intros n M q HM H. unfold cdiv.
  pose proof (Z.div_mod (- n) M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound (- n) M HM) as B. nia.
Qed.

Lemma cdiv_lb_neg : forall n M q, M < 0 -> n < M * (q - 1) -> q <= cdiv n M.
Proof.
  intros n M q HM H. unfold cdiv.
  pose proof (Z.div_mod (- n) M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound (- n) M HM) as B. nia.
Qed.

(* ---- discrete 1D intermediate value theorem for floored division ---- *)
Lemma div_1d_pos : forall yl yu z x, 0 < z -> yl <= yu ->
   yl / z <= x -> x <=  yu / z ->
  exists y, yl <= y <= yu /\  y / z = x.
Proof.
  intros yl yu z x Hz Hne Hmin Hmax.
  exists (Z.max yl (Z.min yu (x * z))).
  pose proof (Z.div_mod yl z ltac:(lia)) as Dyl. pose proof (Z.mod_pos_bound yl z Hz) as Byl.
  pose proof (Z.div_mod yu z ltac:(lia)) as Dyu. pose proof (Z.mod_pos_bound yu z Hz) as Byu.
  assert (Hxzu : x * z <= yu) by nia.
  rewrite (Z.min_r yu (x*z)) by lia.
  destruct (Z.max_spec yl (x*z)) as [[Hlt Heq]|[Hge Heq]]; rewrite Heq.
  - split; [lia | apply Z.div_mul; lia].
  - split; [lia|]. assert (x = yl / z) by nia. rewrite H; reflexivity.
Qed.

Lemma div_1d : forall yl yu z x, z <> 0 -> yl <= yu ->
  Z.min ( yl / z) ( yu / z) <= x -> x <= Z.max ( yl / z) ( yu / z) ->
  exists y, yl <= y <= yu /\  y / z = x.
Proof.
  intros yl yu z x Hz Hne Hmin Hmax.
  destruct (Z.lt_trichotomy z 0) as [Hzn|[Hz0|Hzp]]; [ | lia | ].
  - (* z < 0 : reduce to z>0 on (-yu, -yl, -z) *)
    assert (Emin : Z.min (yl/z) (yu/z) = yu/z) by (apply Z.min_r; apply div_le_mono_num_neg; lia).
    assert (Emax : Z.max (yl/z) (yu/z) = yl/z) by (apply Z.max_l; apply div_le_mono_num_neg; lia).
    rewrite Emin in Hmin; rewrite Emax in Hmax.
    assert (E1 : (-yu) / (-z) = yu / z) by (apply Z.div_opp_opp; lia).
    assert (E2 : (-yl) / (-z) = yl / z) by (apply Z.div_opp_opp; lia).
    destruct (div_1d_pos (-yu) (-yl) (-z) x ltac:(lia) ltac:(lia)
                ltac:(rewrite E1; exact Hmin) ltac:(rewrite E2; exact Hmax)) as [y' [Hy' Hdiv']].
    exists (-y'). split; [lia|].
    rewrite <- (Z.div_opp_opp (-y') z) by lia. rewrite Z.opp_involutive. exact Hdiv'.
  - (* z > 0 *)
    assert (Emin : Z.min (yl/z) (yu/z) = yl/z) by (apply Z.min_l; apply Z.div_le_mono; lia).
    assert (Emax : Z.max (yl/z) (yu/z) = yu/z) by (apply Z.max_r; apply Z.div_le_mono; lia).
    rewrite Emin in Hmin; rewrite Emax in Hmax.
    apply div_1d_pos; auto; lia.
Qed.

(* A generic positive-divisor witness builder.  For z > 0, whenever the
   y-interval [c,d] meets the pre-image band [a*z, (b+1)*z-1] of the quotient
   window [a,b] (i.e. a*z <= d and c <= (b+1)*z-1), there is an actual
   solution x = y/z with x in [a,b] and y in [c,d].  No sign assumptions on
   a,b,c,d are needed: the witness is y = max(c, a*z), x = y/z. *)
Lemma witness_pos : forall a b c d z,
  0 < z -> a <= b -> c <= d -> a*z <= d -> c <= (b+1)*z - 1 ->
  exists x y, (a <= x <= b) /\ (c <= y <= d) /\ z <> 0 /\ x = y / z.
Proof.
  intros a b c d z Hz Hab Hcd Had Hcb.
  exists ((Z.max c (a*z))/z), (Z.max c (a*z)).
  assert (Haz : a*z <= (b+1)*z - 1) by nia.
  assert (Hyd : Z.max c (a*z) <= d) by (apply Z.max_lub; assumption).
  assert (Hyu : Z.max c (a*z) <= (b+1)*z - 1) by (apply Z.max_lub; assumption).
  assert (Hyl1 : c <= Z.max c (a*z)) by apply Z.le_max_l.
  assert (Hyl2 : a*z <= Z.max c (a*z)) by apply Z.le_max_r.
  assert (Hxa : a <= Z.max c (a*z) / z).
  { apply Z.le_trans with (a*z/z); [ rewrite Z.div_mul by lia; lia | apply Z.div_le_mono; lia ]. }
  assert (Hxb : Z.max c (a*z) / z < b + 1).
  { apply Z.div_lt_upper_bound; [lia|nia]. }
  repeat split; try lia.
Qed.
(* Witness constructor for a negative denominator [z] realizing bound reach. *)
Lemma realize_neg : forall a b c d z,
  z < 0 -> a <= b -> c <= d ->
  c <= a * z -> (b+1) * z < d ->
  exists x y, a <= x <= b /\ c <= y <= d /\ z <> 0 /\ x = y / z.
Proof.
  intros a b c d z Hz Hab Hcd Hc Hd.
  destruct (Z_le_gt_dec (a*z) d) as [HA|HB].
  - exists a, (a*z). repeat split; try lia.
    rewrite Z.div_mul by lia. reflexivity.
  - exists (d/z), d.
    pose proof (div_bracket_neg d z Hz) as [Br1 Br2].
    repeat split; try lia; nia.
Qed.

(* --- Helper facts for [fden_opt] ----------------------------------- *)

(* Ceiling division times a negative divisor under-approximates. *)
Lemma cdiv_mul_le_neg : forall n M, M < 0 -> M * cdiv n M <= n.
Proof.
  intros n M HM. unfold cdiv.
  assert (HM' : M <> 0) by lia.
  pose proof (Z.div_mod (-n) M HM') as Hdm.
  pose proof (Z.mod_neg_bound (-n) M HM) as Hmod.
  nia.
Qed.

(* Ceiling division times a positive divisor over-approximates. *)
Lemma cdiv_mul_ge : forall n b, 0 < b -> n <= b * cdiv n b.
Proof.
  intros n b Hb. unfold cdiv.
  pose proof (Z.mul_div_le (-n) b Hb).
  nia.
Qed.

(* Floor division times a negative divisor over-approximates. *)
Lemma div_mul_ge_neg : forall p q, q < 0 -> p <= q * (p / q).
Proof.
  intros p q Hq.
  assert (Hq' : q <> 0) by lia.
  pose proof (Z.div_mod p q Hq') as Hdm.
  pose proof (Z.mod_neg_bound p q Hq) as Hmod.
  nia.
Qed.

(* ================================================================= *)
(*  Pure arithmetic core: two corner solutions (at zl and zu) whose   *)
(*  x-values lie in [a,b] yield the eight "band" inequalities.        *)
(* ================================================================= *)
Lemma band_from_sols : forall a b c d zl zu xl yl xu yu,
  zl <= zu -> (0 < zl \/ zu < 0) ->
  c <= yl <= d -> c <= yu <= d ->
  zl <> 0 -> xl = yl / zl ->
  zu <> 0 -> xu = yu / zu ->
  a <= xl <= b -> a <= xu <= b ->
  (0 < zu -> a*zu <= d) /\ (0 < zl -> a*zl <= d) /\
  (zl < 0 -> (b+1)*zl+1 <= d) /\ (zu < 0 -> (b+1)*zu+1 <= d) /\
  (0 < zu -> c <= (b+1)*zu-1) /\ (0 < zl -> c <= (b+1)*zl-1) /\
  (zl < 0 -> c <= a*zl) /\ (zu < 0 -> c <= a*zu).
Proof.
  intros a b c d zl zu xl yl xu yu Hz Hsign Hyl Hyu Hzl Hxl Hzu Hxu Hxlb Hxub.
  destruct Hsign as [Hzlp | Hzun].
  - assert (Hzup : 0 < zu) by lia.
    destruct (div_bracket_pos yl zl Hzlp) as [Bl1 Bl2].
    destruct (div_bracket_pos yu zu Hzup) as [Bu1 Bu2].
    rewrite <- Hxl in Bl1, Bl2. rewrite <- Hxu in Bu1, Bu2.
    repeat split; intro Hsg; try lia; nia.
  - assert (Hzln : zl < 0) by lia.
    destruct (div_bracket_neg yl zl Hzln) as [Bl1 Bl2].
    destruct (div_bracket_neg yu zu Hzun) as [Bu1 Bu2].
    rewrite <- Hxl in Bl1, Bl2. rewrite <- Hxu in Bu1, Bu2.
    repeat split; intro Hsg; try lia; nia.
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

(* helper: quotient of a value in [c,d] stays between the endpoint quotients *)
Lemma div_in_range : forall c d z y,
  c <= y <= d ->
  Z.min (c / z) (d / z) <= y / z <= Z.max (c / z) (d / z).
Proof.
  intros c d z y [Hcy Hyd].
  destruct (Z.lt_trichotomy z 0) as [Hz|[Hz|Hz]].
  - assert (d / z <= y / z) by (apply div_le_mono_num_neg; lia).
    assert (y / z <= c / z) by (apply div_le_mono_num_neg; lia).
    lia.
  - subst z. rewrite !Z.div_0_r. lia.
  - assert (c / z <= y / z) by (apply Z.div_le_mono; lia).
    assert (y / z <= d / z) by (apply Z.div_le_mono; lia).
    lia.
Qed.