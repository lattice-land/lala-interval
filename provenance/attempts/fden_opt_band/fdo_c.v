(** * Soundness and optimality of the band floored-division propagator

    Rocq formalisation of the propagator for
        x = fdiv(y,z)  =  x = floor(y/z),  z <> 0
    over the integer interval abstract domain, in its COMPRESSED form: the
    14-row denominator table of [fdiv.v] is replaced by the exact "band"
    refinement [fden] (two linear inequalities per sign of z), mirroring the
    reference C++ implementation [zfdiv2] in [zinterval.hpp].

    The five verified properties (identical statements as in [fdiv.v]):
      - soundness    : [fdiv_soundness]
      - reductivity  : [fdiv_reductive]
      - optimality   : [fdiv_best]        (best abstract transformer)
      - monotonicity : [fdiv_monotone]    (closure-operator corollary)
      - idempotence  : [fdiv_idempotence] (closure-operator corollary)
    All proved by [Qed] -- verify with [Print Assumptions fdiv_best.]. *)

From Stdlib Require Import ZArith Lia.
From LalaInterval Require Export itv.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** The constraint relation                                         *)
(* ------------------------------------------------------------------ *)
(** The generic interval / store infrastructure ([itv], [mem], [nonempty],
    [nonemptyb], [inter], [ijoin], [store], [in_store], [ne_store], [sjoin],
    [sqcupbot], ...) lives in [itv.v] and is re-exported above. *)

(** The constraint relation: floored division with non-zero divisor. *)
Definition sol (x y z : Z) : Prop := z <> 0 /\ x = Z.div y z.

(* ------------------------------------------------------------------ *)
(** ** Lemma 1 : floor bracketing                                      *)
(* ------------------------------------------------------------------ *)

Lemma div_bracket_pos : forall y z,
  0 < z ->
  z * (y / z) <= y /\ y <= z * (y / z + 1) - 1.
Proof.
  intros y z Hz.
  assert (Hz' : z <> 0) by lia.
  pose proof (Z.div_mod y z Hz') as Hdm.
  pose proof (Z.mod_pos_bound y z Hz) as Hmod.
  set (q := y / z) in *. set (r := y mod z) in *.
  split; nia.
Qed.

Lemma div_bracket_neg : forall y z,
  z < 0 ->
  z * (y / z + 1) + 1 <= y /\ y <= z * (y / z).
Proof.
  intros y z Hz.
  assert (Hz' : z <> 0) by lia.
  pose proof (Z.div_mod y z Hz') as Hdm.
  pose proof (Z.mod_neg_bound y z Hz) as Hmod.
  set (q := y / z) in *. set (r := y mod z) in *.
  split; nia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** A monotonicity helper : [a*t] lies between its corner values    *)
(* ------------------------------------------------------------------ *)

Lemma mul_between : forall a l u t,
  l <= t <= u ->
  Z.min (a*l) (a*u) <= a*t <= Z.max (a*l) (a*u).
Proof.
  intros a l u t [H1 H2].
  destruct (Z_lt_le_dec a 0) as [Ha|Ha].
  - (* a < 0 : a*t between a*u (small) and a*l (large) *)
    assert (a*u <= a*t) by nia.
    assert (a*t <= a*l) by nia.
    split.
    + apply Z.le_trans with (a*u); [apply Z.le_min_r| exact H].
    + apply Z.le_trans with (a*l); [exact H0| apply Z.le_max_l].
  - (* 0 <= a *)
    assert (a*l <= a*t) by nia.
    assert (a*t <= a*u) by nia.
    split.
    + apply Z.le_trans with (a*l); [apply Z.le_min_l| exact H].
    + apply Z.le_trans with (a*u); [exact H0| apply Z.le_max_r].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Lemma 3 : fnum is a sound numerator enclosure                   *)
(* ------------------------------------------------------------------ *)

Definition Ylo (xl xu zl zu : Z) : Z :=
  Z.min (Z.min (xl*zl) (xl*zu))
        (Z.min ((xu+1)*zl+1) ((xu+1)*zu+1)).

Definition Yhi (xl xu zl zu : Z) : Z :=
  Z.max (Z.max (xl*zl) (xl*zu))
        (Z.max ((xu+1)*zl-1) ((xu+1)*zu-1)).

Lemma fnum_sound : forall x y z xl xu zl zu,
  xl <= x <= xu ->
  zl <= z <= zu ->
  sol x y z ->
  Ylo xl xu zl zu <= y <= Yhi xl xu zl zu.
Proof.
  intros x y z xl xu zl zu [Hxl Hxu] [Hzl Hzu] [Hz Hxeq]. subst x.
  unfold Ylo, Yhi.
  destruct (Z.lt_trichotomy z 0) as [Hneg | [Hz0 | Hpos]].
  - (* z < 0 : lower bound from f2+1, upper bound from f1 *)
    destruct (div_bracket_neg y z Hneg) as [Hlow Hup].
    pose proof (mul_between (xu+1) zl zu z (conj Hzl Hzu)) as Hf2.
    pose proof (mul_between xl zl zu z (conj Hzl Hzu)) as Hf1.
    assert (Hmono2 : (xu+1)*z <= (y/z + 1)*z) by nia.
    assert (Hmono1 : (y/z)*z <= xl*z) by nia.
    split.
    + apply Z.le_trans with ((xu+1)*z + 1).
      * apply Z.le_trans with (Z.min ((xu+1)*zl+1) ((xu+1)*zu+1)).
        { apply Z.le_min_r. }
        { destruct Hf2 as [Hf2l Hf2u]. lia. }
      * nia.
    + apply Z.le_trans with (xl*z).
      * apply Z.le_trans with ((y/z)*z); [ nia | exact Hmono1 ].
      * apply Z.le_trans with (Z.max (xl*zl) (xl*zu)).
        { destruct Hf1 as [Hf1l Hf1u]. lia. }
        { apply Z.le_max_l. }
  - lia. (* z = 0 contradicts Hz *)
  - (* 0 < z : lower bound from f1, upper bound from f2-1 *)
    destruct (div_bracket_pos y z Hpos) as [Hlow Hup].
    pose proof (mul_between xl zl zu z (conj Hzl Hzu)) as Hf1.
    pose proof (mul_between (xu+1) zl zu z (conj Hzl Hzu)) as Hf2.
    assert (Hmono1 : xl*z <= (y/z)*z) by nia.
    assert (Hmono2 : (y/z+1)*z <= (xu+1)*z) by nia.
    split.
    + apply Z.le_trans with (xl*z).
      * apply Z.le_trans with (Z.min (xl*zl) (xl*zu)).
        { apply Z.le_min_l. }
        { destruct Hf1 as [Hf1l Hf1u]. lia. }
      * apply Z.le_trans with ((y/z)*z); [ exact Hmono1 | nia ].
    + apply Z.le_trans with ((xu+1)*z - 1).
      * nia.
      * apply Z.le_trans with (Z.max ((xu+1)*zl-1) ((xu+1)*zu-1)).
        { destruct Hf2 as [Hf2l Hf2u]. lia. }
        { apply Z.le_max_r. }
Qed.

(* ------------------------------------------------------------------ *)
(** ** Lemma 2 : fdiv is a sound quotient enclosure                    *)
(*     (requires a sign-definite, finite divisor interval)             *)
(* ------------------------------------------------------------------ *)

Definition Xlo (yl yu zl zu : Z) : Z :=
  Z.min (Z.min (yl/zl) (yl/zu)) (Z.min (yu/zl) (yu/zu)).
Definition Xhi (yl yu zl zu : Z) : Z :=
  Z.max (Z.max (yl/zl) (yl/zu)) (Z.max (yu/zl) (yu/zu)).

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
  set (m := p / r) in *.
  assert (Hlt : p < q * (m + 1)).
  { destruct (Z.le_gt_cases (m + 1) 0) as [Hm|Hm].
    - assert (r * (m + 1) <= q * (m + 1)) by nia. nia.
    - nia. }
  assert (p / q < m + 1) by (apply Z.div_lt_upper_bound; [lia| nia]).
  lia.
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
  - (* a < 0 : a/cl <= a/t <= a/cu *)
    assert (a/cl <= a/t) by (apply div_le_compat_l_neg; lia).
    assert (a/t <= a/cu) by (apply div_le_compat_l_neg; lia).
    split.
    + apply Z.le_trans with (a/cl); [apply Z.le_min_l| exact H].
    + apply Z.le_trans with (a/cu); [exact H0| apply Z.le_max_r].
  - (* 0 <= a : a/cu <= a/t <= a/cl *)
    assert (a/cu <= a/t) by (apply Z.div_le_compat_l; lia).
    assert (a/t <= a/cl) by (apply Z.div_le_compat_l; lia).
    split.
    + apply Z.le_trans with (a/cu); [apply Z.le_min_r| exact H].
    + apply Z.le_trans with (a/cl); [exact H0| apply Z.le_max_l].
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

Lemma fdiv_sound_pos : forall x y z yl yu zl zu,
  yl <= y <= yu ->
  zl <= z <= zu ->
  0 < zl ->
  sol x y z ->
  Xlo yl yu zl zu <= x <= Xhi yl yu zl zu.
Proof.
  intros x y z yl yu zl zu [Hyl Hyu] [Hzl Hzu] Hzlpos [Hz Hxeq]. subst x.
  assert (Hzpos : 0 < z) by lia.
  unfold Xlo, Xhi.
  pose proof (div_between_pos_den y zl zu z Hzlpos (conj Hzl Hzu)) as Hden.
  assert (HzlP : 0 < zl) by lia. assert (HzuP : 0 < zu) by lia.
  split.
  - destruct Hden as [Hdl _].
    apply Z.le_trans with (Z.min (y/zl) (y/zu)); [| exact Hdl].
    assert (yl/zl <= y/zl) by (apply div_le_mono_num; lia).
    assert (yl/zu <= y/zu) by (apply div_le_mono_num; lia).
    apply Z.min_glb.
    + apply Z.le_trans with (yl/zl); [| exact H].
      apply Z.le_trans with (Z.min (yl/zl) (yl/zu)); [apply Z.le_min_l|].
      apply Z.le_min_l.
    + apply Z.le_trans with (yl/zu); [| exact H0].
      apply Z.le_trans with (Z.min (yl/zl) (yl/zu)); [apply Z.le_min_l|].
      apply Z.le_min_r.
  - destruct Hden as [_ Hdu].
    apply Z.le_trans with (Z.max (y/zl) (y/zu)); [exact Hdu |].
    assert (y/zl <= yu/zl) by (apply div_le_mono_num; lia).
    assert (y/zu <= yu/zu) by (apply div_le_mono_num; lia).
    apply Z.max_lub.
    + apply Z.le_trans with (yu/zl); [exact H |].
      apply Z.le_trans with (Z.max (yu/zl) (yu/zu)); [apply Z.le_max_l|].
      apply Z.le_max_r.
    + apply Z.le_trans with (yu/zu); [exact H0 |].
      apply Z.le_trans with (Z.max (yu/zl) (yu/zu)); [apply Z.le_max_r|].
      apply Z.le_max_r.
Qed.

Lemma fdiv_sound_neg : forall x y z yl yu zl zu,
  yl <= y <= yu ->
  zl <= z <= zu ->
  zu < 0 ->
  sol x y z ->
  Xlo yl yu zl zu <= x <= Xhi yl yu zl zu.
Proof.
  intros x y z yl yu zl zu [Hyl Hyu] [Hzl Hzu] Hzuneg [Hz Hxeq]. subst x.
  assert (Hzneg : z < 0) by lia.
  unfold Xlo, Xhi.
  pose proof (div_between_neg_den y zl zu z Hzuneg (conj Hzl Hzu)) as Hden.
  assert (HzlN : zl < 0) by lia. assert (HzuN : zu < 0) by lia.
  split.
  - destruct Hden as [Hdl _].
    apply Z.le_trans with (Z.min (y/zl) (y/zu)); [| exact Hdl].
    assert (yu/zl <= y/zl) by (apply div_le_mono_num_neg; lia).
    assert (yu/zu <= y/zu) by (apply div_le_mono_num_neg; lia).
    apply Z.min_glb.
    + apply Z.le_trans with (yu/zl); [| exact H].
      apply Z.le_trans with (Z.min (yu/zl) (yu/zu)); [apply Z.le_min_r| apply Z.le_min_l].
    + apply Z.le_trans with (yu/zu); [| exact H0].
      apply Z.le_trans with (Z.min (yu/zl) (yu/zu)); [apply Z.le_min_r| apply Z.le_min_r].
  - destruct Hden as [_ Hdu].
    apply Z.le_trans with (Z.max (y/zl) (y/zu)); [exact Hdu |].
    assert (y/zl <= yl/zl) by (apply div_le_mono_num_neg; lia).
    assert (y/zu <= yl/zu) by (apply div_le_mono_num_neg; lia).
    apply Z.max_lub.
    + apply Z.le_trans with (yl/zl); [exact H |].
      apply Z.le_trans with (Z.max (yl/zl) (yl/zu)); [apply Z.le_max_l| apply Z.le_max_l].
    + apply Z.le_trans with (yl/zu); [exact H0 |].
      apply Z.le_trans with (Z.max (yl/zl) (yl/zu)); [apply Z.le_max_r| apply Z.le_max_l].
Qed.


(* ------------------------------------------------------------------ *)
(** ** Structural: store-level join preserves witnesses                *)
(* ------------------------------------------------------------------ *)

(** [store] and its lattice operations ([in_store], [ne_store], [sjoin],
    [sqcupbot], with [sqcupbot_pres_l]/[sqcupbot_pres_r]) live in [itv.v]. *)

(* ------------------------------------------------------------------ *)
(** ** fden: the exact "band" divisor refinement, and its soundness    *)
(* ------------------------------------------------------------------ *)

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
  pose proof (Z.mod_neg_bound n M HM) as B. set (Q := n / M) in *. nia.
Qed.

Lemma fdiv_lb_neg : forall n M q, M < 0 -> n <= M * q -> q <= n / M.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B. set (Q := n / M) in *. nia.
Qed.

Lemma fdiv_lt_neg : forall n M q, M < 0 -> M * q < n -> n / M < q.
Proof.
  intros n M q HM H. pose proof (Z.div_mod n M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound n M HM) as B. set (Q := n / M) in *. nia.
Qed.

Lemma cdiv_ub_neg : forall n M q, M < 0 -> M * q <= n -> cdiv n M <= q.
Proof.
  intros n M q HM H. unfold cdiv.
  pose proof (Z.div_mod (- n) M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound (- n) M HM) as B. set (P := (- n) / M) in *. nia.
Qed.

Lemma cdiv_lb_neg : forall n M q, M < 0 -> n < M * (q - 1) -> q <= cdiv n M.
Proof.
  intros n M q HM H. unfold cdiv.
  pose proof (Z.div_mod (- n) M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound (- n) M HM) as B. set (P := (- n) / M) in *. nia.
Qed.

(** The compressed denominator refinement: the 14-row sign-class table is
    replaced by the exact solution of two linear inequalities.  For a
    sign-definite divisor z the y-bands of consecutive quotients are
    contiguous, hence (with [a,b] the x-interval and [c,d] the y-interval):
      z >= 1:   (exists x in [a,b], y in [c,d], x = y/z)
                  <->  a*z <= d  /\  (b+1)*z >= c+1
      z <= -1:  (exists x in [a,b], y in [c,d], x = y/z)
                  <->  a*z >= c  /\  (b+1)*z <= d-1
    Each constraint contributes one bound on z according to the sign of its
    coefficient (a, resp. b+1), or a feasibility test when that coefficient
    is zero.  The bounds are met into [iz] (the one-sided [z.l.meet] /
    [z.u.meet] of the C++ DEN step); an infeasible zero-coefficient
    constraint yields the canonical empty interval [1,0]; a straddling [iz]
    is left untouched (the propagator only calls [fden] on sign-definite
    branches). *)
Definition fden (ix iy iz : itv) : itv :=
  let a := lo ix in let b1 := hi ix + 1 in
  let c := lo iy in let d := hi iy in
  let zl := lo iz in let zu := hi iz in
  if 0 <? zl then
    if (((a =? 0) && (d <? 0)) || ((b1 =? 0) && (0 <=? c)))%bool then Itv 1 0
    else Itv (Z.max zl (Z.max (if a <? 0 then cdiv d a else zl)
                              (if 0 <? b1 then cdiv (c+1) b1 else zl)))
             (Z.min zu (Z.min (if 0 <? a then d / a else zu)
                              (if b1 <? 0 then (c+1) / b1 else zu)))
  else if zu <? 0 then
    if (((a =? 0) && (0 <? c)) || ((b1 =? 0) && (d <=? 0)))%bool then Itv 1 0
    else Itv (Z.max zl (Z.max (if 0 <? a then cdiv c a else zl)
                              (if b1 <? 0 then cdiv (d-1) b1 else zl)))
             (Z.min zu (Z.min (if a <? 0 then c / a else zu)
                              (if 0 <? b1 then (d-1) / b1 else zu)))
  else iz.

(** Soundness of the band refinement: a solution's divisor satisfies both
    linear constraints, hence lies within every bound the refinement meets. *)
Lemma fden_sound : forall x y z ix iy iz,
  mem ix x -> mem iy y -> mem iz z -> sol x y z -> mem (fden ix iy iz) z.
Proof.
  intros x y z ix iy iz Hx Hy Hz [Hz0 Hxeq].
  unfold mem in *. unfold fden; cbv zeta.
  set (a := lo ix) in *. set (b1 := hi ix + 1) in *.
  set (c := lo iy) in *. set (d := hi iy) in *.
  destruct Hx as [Hax Hxb]. destruct Hy as [Hcy Hyd]. destruct Hz as [Hzl Hzu].
  assert (Hxb1 : x + 1 <= b1) by (unfold b1; lia).
  destruct (Z.ltb_spec 0 (lo iz)) as [Hpos|Hnpos].
  - (* z >= 1 : the solution satisfies  a*z <= d  and  c+1 <= b1*z *)
    assert (Hzp : 0 < z) by lia.
    destruct (div_bracket_pos y z Hzp) as [Hbr1 Hbr2].
    rewrite <- Hxeq in Hbr1, Hbr2.
    assert (HA : a * z <= d) by nia.
    assert (HB : c + 1 <= b1 * z) by nia.
    match goal with |- context[if ?g then _ else _] => destruct g eqn:Hk end.
    + exfalso. apply Bool.orb_true_iff in Hk.
      destruct Hk as [Hk|Hk]; apply Bool.andb_true_iff in Hk; destruct Hk as [K1 K2];
        apply Z.eqb_eq in K1; [apply Z.ltb_lt in K2 | apply Z.leb_le in K2]; nia.
    + cbn [lo hi]. split.
      * apply Z.max_lub; [lia|]. apply Z.max_lub.
        -- destruct (Z.ltb_spec a 0) as [Ha|Ha]; [apply cdiv_ub_neg; lia | lia].
        -- destruct (Z.ltb_spec 0 b1) as [Hb|Hb]; [apply cdiv_ub; lia | lia].
      * apply Z.min_glb; [lia|]. apply Z.min_glb.
        -- destruct (Z.ltb_spec 0 a) as [Ha|Ha]; [apply Z.div_le_lower_bound; lia | lia].
        -- destruct (Z.ltb_spec b1 0) as [Hb|Hb]; [apply fdiv_lb_neg; lia | lia].
  - destruct (Z.ltb_spec (hi iz) 0) as [Hneg|Hnneg]; [| lia].
    (* z <= -1 : the solution satisfies  c <= a*z  and  b1*z <= d-1 *)
    assert (Hzn : z < 0) by lia.
    destruct (div_bracket_neg y z Hzn) as [Hbr1 Hbr2].
    rewrite <- Hxeq in Hbr1, Hbr2.
    assert (HA : c <= a * z) by nia.
    assert (HB : b1 * z <= d - 1) by nia.
    match goal with |- context[if ?g then _ else _] => destruct g eqn:Hk end.
    + exfalso. apply Bool.orb_true_iff in Hk.
      destruct Hk as [Hk|Hk]; apply Bool.andb_true_iff in Hk; destruct Hk as [K1 K2];
        apply Z.eqb_eq in K1; [apply Z.ltb_lt in K2 | apply Z.leb_le in K2]; nia.
    + cbn [lo hi]. split.
      * apply Z.max_lub; [lia|]. apply Z.max_lub.
        -- destruct (Z.ltb_spec 0 a) as [Ha|Ha]; [apply cdiv_ub; lia | lia].
        -- destruct (Z.ltb_spec b1 0) as [Hb|Hb]; [apply cdiv_ub_neg; lia | lia].
      * apply Z.min_glb; [lia|]. apply Z.min_glb.
        -- destruct (Z.ltb_spec a 0) as [Ha|Ha]; [apply fdiv_lb_neg; lia | lia].
        -- destruct (Z.ltb_spec 0 b1) as [Hb|Hb]; [apply Z.div_le_lower_bound; lia | lia].
Qed.

Definition fdivxz_pos (s : store) : store :=
  let ix1 := inter (sx s) (Itv (Xlo (lo (sy s)) (hi (sy s)) (lo (sz s)) (hi (sz s)))
                                (Xhi (lo (sy s)) (hi (sy s)) (lo (sz s)) (hi (sz s)))) in
  let iz  := inter (sz s) (fden ix1 (sy s) (sz s)) in
  let ix2 := inter ix1 (Itv (Xlo (lo (sy s)) (hi (sy s)) (lo iz) (hi iz))
                             (Xhi (lo (sy s)) (hi (sy s)) (lo iz) (hi iz))) in
  St ix2 (sy s) iz.

Lemma fdivxz_pos_sound : forall s vx vy vz,
  0 < lo (sz s) ->
  in_store s vx vy vz ->
  sol vx vy vz ->
  in_store (fdivxz_pos s) vx vy vz.
Proof.
  intros s vx vy vz Hpos Hin Hsol.
  destruct Hin as (Hx & Hy & Hz).
  unfold mem in Hx, Hy, Hz.
  unfold fdivxz_pos; cbv zeta; unfold in_store; cbn [sx sy sz].
  set (yl := lo (sy s)) in *. set (yu := hi (sy s)) in *.
  set (zl := lo (sz s)) in *. set (zu := hi (sz s)) in *.
  set (I1 := Itv (Xlo yl yu zl zu) (Xhi yl yu zl zu)) in *.
  set (ix1 := inter (sx s) I1) in *.
  set (iz := inter (sz s) (fden ix1 (sy s) (sz s))) in *.
  set (I2 := Itv (Xlo yl yu (lo iz) (hi iz)) (Xhi yl yu (lo iz) (hi iz))) in *.
  assert (Hx1 : mem ix1 vx).
  { apply mem_inter; [exact Hx|].
    unfold I1, mem; cbn [lo hi].
    apply (fdiv_sound_pos vx vy vz yl yu zl zu); assumption. }
  assert (Hz1 : mem iz vz).
  { apply mem_inter; [exact Hz|].
    apply (fden_sound vx vy vz ix1 (sy s) (sz s)); assumption. }
  assert (Hizpos : 0 < lo iz).
  { unfold iz, inter; cbn [lo hi]. lia. }
  assert (Hx2 : mem (inter ix1 I2) vx).
  { apply mem_inter; [exact Hx1|].
    unfold I2, mem; cbn [lo hi].
    apply (fdiv_sound_pos vx vy vz yl yu (lo iz) (hi iz)); try assumption. }
  split; [exact Hx2 | split; [exact Hy | exact Hz1] ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Main theorem                                                     *)
(* ------------------------------------------------------------------ *)

Definition restrict_z_pos (s : store) : store :=
  St (sx s) (sy s) (inter (sz s) (Itv 1 (hi (sz s)))).
Definition restrict_z_neg (s : store) : store :=
  St (sx s) (sy s) (inter (sz s) (Itv (lo (sz s)) (-1))).

Definition refine_y (s : store) : store :=
  St (sx s) (inter (sy s)
       (Itv (Ylo (lo (sx s)) (hi (sx s)) (lo (sz s)) (hi (sz s)))
            (Yhi (lo (sx s)) (hi (sx s)) (lo (sz s)) (hi (sz s))))) (sz s).

(** Negative branch: identical enclosure computation to [fdivxz_pos] (the
    [Xlo]/[Xhi] corner formulas are sign-agnostic); only the soundness argument
    differs, using the already-proven [fdiv_sound_neg]. *)
Definition fdivxz_neg (s : store) : store :=
  let ix1 := inter (sx s) (Itv (Xlo (lo (sy s)) (hi (sy s)) (lo (sz s)) (hi (sz s)))
                                (Xhi (lo (sy s)) (hi (sy s)) (lo (sz s)) (hi (sz s)))) in
  let iz  := inter (sz s) (fden ix1 (sy s) (sz s)) in
  let ix2 := inter ix1 (Itv (Xlo (lo (sy s)) (hi (sy s)) (lo iz) (hi iz))
                             (Xhi (lo (sy s)) (hi (sy s)) (lo iz) (hi iz))) in
  St ix2 (sy s) iz.

Lemma fdivxz_neg_sound : forall s vx vy vz,
  hi (sz s) < 0 ->
  in_store s vx vy vz ->
  sol vx vy vz ->
  in_store (fdivxz_neg s) vx vy vz.
Proof.
  intros s vx vy vz Hneg Hin Hsol.
  destruct Hin as (Hx & Hy & Hz).
  unfold mem in Hx, Hy, Hz.
  unfold fdivxz_neg; cbv zeta; unfold in_store; cbn [sx sy sz].
  set (yl := lo (sy s)) in *. set (yu := hi (sy s)) in *.
  set (zl := lo (sz s)) in *. set (zu := hi (sz s)) in *.
  set (I1 := Itv (Xlo yl yu zl zu) (Xhi yl yu zl zu)) in *.
  set (ix1 := inter (sx s) I1) in *.
  set (iz := inter (sz s) (fden ix1 (sy s) (sz s))) in *.
  set (I2 := Itv (Xlo yl yu (lo iz) (hi iz)) (Xhi yl yu (lo iz) (hi iz))) in *.
  assert (Hx1 : mem ix1 vx).
  { apply mem_inter; [exact Hx|].
    unfold I1, mem; cbn [lo hi].
    apply (fdiv_sound_neg vx vy vz yl yu zl zu); assumption. }
  assert (Hz1 : mem iz vz).
  { apply mem_inter; [exact Hz|].
    apply (fden_sound vx vy vz ix1 (sy s) (sz s)); assumption. }
  assert (Hizneg : hi iz < 0).
  { unfold iz, inter; cbn [lo hi]. lia. }
  assert (Hx2 : mem (inter ix1 I2) vx).
  { apply mem_inter; [exact Hx1|].
    unfold I2, mem; cbn [lo hi].
    apply (fdiv_sound_neg vx vy vz yl yu (lo iz) (hi iz)); try assumption. }
  split; [exact Hx2 | split; [exact Hy | exact Hz1] ].
Qed.

Definition propagator (s : store) : store :=
  refine_y (sqcupbot (fdivxz_neg (restrict_z_neg s))
                     (fdivxz_pos (restrict_z_pos s))).

Theorem fdiv_soundness : forall s vx vy vz,
  in_store s vx vy vz ->
  sol vx vy vz ->
  in_store (propagator s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hsol.
  destruct (Hsol) as [Hz Hxeq].
  unfold propagator.
  assert (Hjoin : in_store
     (sqcupbot (fdivxz_neg (restrict_z_neg s))
               (fdivxz_pos (restrict_z_pos s))) vx vy vz).
  { destruct (Z.lt_trichotomy vz 0) as [Hneg | [H0 | Hpos]].
    - apply sqcupbot_pres_l.
      apply fdivxz_neg_sound; [ simpl | | exact Hsol ].
      + unfold restrict_z_neg, inter; simpl. lia.
      + unfold restrict_z_neg, in_store, mem, inter; simpl.
        destruct Hin as (Hx & Hy & Hz'). unfold mem in *.
        repeat split; try tauto; simpl; lia.
    - lia.
    - apply sqcupbot_pres_r.
      apply fdivxz_pos_sound; [ simpl | | exact Hsol ].
      + unfold restrict_z_pos, inter; simpl. lia.
      + unfold restrict_z_pos, in_store, mem, inter; simpl.
        destruct Hin as (Hx & Hy & Hz'). unfold mem in *.
        repeat split; try tauto; simpl; lia. }
  set (s' := sqcupbot _ _) in *.
  destruct Hjoin as (Hx' & Hy' & Hz').
  unfold refine_y, in_store; cbn [sx sy sz].
  split; [exact Hx' | split ].
  - apply mem_inter; [exact Hy'|].
    unfold mem; cbn [lo hi].
    apply (fnum_sound vx vy vz (lo (sx s')) (hi (sx s')) (lo (sz s')) (hi (sz s'))).
    + exact Hx'.
    + exact Hz'.
    + exact Hsol.
  - exact Hz'.
Qed.

(* ================================================================= *)
(** ** Order on intervals/stores; corner attainment, discrete IVT,    *)
(**    and fden z-optimality  (formerly optbase.v)                    *)
(* ================================================================= *)

(* ---- order on intervals / stores ---- *)
Definition ile (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.   (* i included in j *)
Definition sle (a b : store) : Prop :=
  ile (sx a) (sx b) /\ ile (sy a) (sy b) /\ ile (sz a) (sz b).
Definition Cx (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).

Lemma ile_antisym : forall i j, ile i j -> ile j i -> i = j.
Proof. intros [il ih] [jl jh]; unfold ile; cbn [lo hi]; intros [??] [??]; f_equal; lia. Qed.
Lemma sle_antisym : forall a b, sle a b -> sle b a -> a = b.
Proof.
  intros [ax ay az] [bx byy bz]; unfold sle; cbn [sx sy sz];
  intros [H1 [H2 H3]] [H4 [H5 H6]]; f_equal; apply ile_antisym; assumption.
Qed.

(* ---- optimality = best abstract transformer ---- *)
Definition contains_sols (s t : store) : Prop :=
  forall vx vy vz, in_store s vx vy vz -> sol vx vy vz -> in_store t vx vy vz.

Definition feasible (s : store) : Prop :=
  exists vx vy vz, in_store s vx vy vz /\ sol vx vy vz.

(* On a feasible input, the propagator output is contained in EVERY store that
   contains all the solutions -- i.e. it is the tightest such store (= alpha o f o gamma). *)
Definition optimal (s : store) : Prop :=
  feasible s -> forall t, contains_sols s t -> sle (propagator s) t.

Definition consistent (s : store) : Prop :=
  lo (sx s) <= hi (sx s) /\ lo (sy s) <= hi (sy s) /\ lo (sz s) <= hi (sz s).

(* soundness (already proven) repackaged *)
Lemma prop_sound : forall s, contains_sols s (propagator s).
Proof. intros s vx vy vz H Hs. apply fdiv_soundness; assumption. Qed.

(* ---- corner attainment: the quotient extremes are realised at box corners ---- *)
Lemma Xhi_corner : forall yl yu zl zu,
  exists y z, (y = yl \/ y = yu) /\ (z = zl \/ z = zu) /\ y / z = Xhi yl yu zl zu.
Proof.
  intros yl yu zl zu. unfold Xhi.
  destruct (Z.max_spec (Z.max (yl/zl) (yl/zu)) (Z.max (yu/zl) (yu/zu))) as [[_ E]|[_ E]]; rewrite E.
  - destruct (Z.max_spec (yu/zl) (yu/zu)) as [[_ E2]|[_ E2]]; rewrite E2;
      [ exists yu, zu | exists yu, zl ]; auto.
  - destruct (Z.max_spec (yl/zl) (yl/zu)) as [[_ E2]|[_ E2]]; rewrite E2;
      [ exists yl, zu | exists yl, zl ]; auto.
Qed.

Lemma Xlo_corner : forall yl yu zl zu,
  exists y z, (y = yl \/ y = yu) /\ (z = zl \/ z = zu) /\ y / z = Xlo yl yu zl zu.
Proof.
  intros yl yu zl zu. unfold Xlo.
  destruct (Z.min_spec (Z.min (yl/zl) (yl/zu)) (Z.min (yu/zl) (yu/zu))) as [[_ E]|[_ E]]; rewrite E.
  - destruct (Z.min_spec (yl/zl) (yl/zu)) as [[_ E2]|[_ E2]]; rewrite E2;
      [ exists yl, zl | exists yl, zu ]; auto.
  - destruct (Z.min_spec (yu/zl) (yu/zu)) as [[_ E2]|[_ E2]]; rewrite E2;
      [ exists yu, zl | exists yu, zu ]; auto.
Qed.

(* ---- discrete 1D intermediate value theorem for floored division ---- *)
Lemma div_1d_pos : forall yl yu z x, 0 < z -> yl <= yu ->
  Z.div yl z <= x -> x <= Z.div yu z ->
  exists y, yl <= y <= yu /\ Z.div y z = x.
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
  Z.min (Z.div yl z) (Z.div yu z) <= x -> x <= Z.max (Z.div yl z) (Z.div yu z) ->
  exists y, yl <= y <= yu /\ Z.div y z = x.
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

(* ---- numerator corner attainment (fnum optimality) ---- *)
Lemma Ylo_attained : forall a b zl zu, a <= b -> zl <= zu -> (0 < zl \/ zu < 0) ->
  exists x z, a <= x <= b /\ zl <= z <= zu /\ z <> 0 /\ x = Z.div (Ylo a b zl zu) z.
Proof.
  intros a b zl zu Hab Hz Hsign.
  destruct Hsign as [Hzl | Hzu].
  - assert (EY : Ylo a b zl zu = Z.min (a*zl) (a*zu)).
    { unfold Ylo. apply Z.min_l. apply Z.min_glb.
      - apply Z.le_trans with (a*zl); [apply Z.le_min_l| nia].
      - apply Z.le_trans with (a*zu); [apply Z.le_min_r| nia]. }
    rewrite EY. destruct (Z.min_spec (a*zl) (a*zu)) as [[_ E]|[_ E]]; rewrite E.
    + exists a, zl. repeat split; try lia. symmetry; apply Z.div_mul; lia.
    + exists a, zu. repeat split; try lia. symmetry; apply Z.div_mul; lia.
  - assert (EY : Ylo a b zl zu = Z.min ((b+1)*zl+1) ((b+1)*zu+1)).
    { unfold Ylo. apply Z.min_r. apply Z.min_glb.
      - apply Z.le_trans with ((b+1)*zl+1); [apply Z.le_min_l| nia].
      - apply Z.le_trans with ((b+1)*zu+1); [apply Z.le_min_r| nia]. }
    rewrite EY.
    assert (D1 : Z.div 1 zl = -1) by (pose proof (Z.div_mod 1 zl ltac:(lia)); pose proof (Z.mod_neg_bound 1 zl ltac:(lia)); nia).
    assert (D2 : Z.div 1 zu = -1) by (pose proof (Z.div_mod 1 zu ltac:(lia)); pose proof (Z.mod_neg_bound 1 zu ltac:(lia)); nia).
    destruct (Z.min_spec ((b+1)*zl+1) ((b+1)*zu+1)) as [[_ E]|[_ E]]; rewrite E.
    + exists b, zl. repeat split; try lia. rewrite Z.div_add_l by lia. rewrite D1. lia.
    + exists b, zu. repeat split; try lia. rewrite Z.div_add_l by lia. rewrite D2. lia.
Qed.
Lemma Yhi_attained : forall a b zl zu, a <= b -> zl <= zu -> (0 < zl \/ zu < 0) ->
  exists x z, a <= x <= b /\ zl <= z <= zu /\ z <> 0 /\ x = Z.div (Yhi a b zl zu) z.
Proof.
  intros a b zl zu Hab Hz Hsign.
  destruct Hsign as [Hzl | Hzu].
  - assert (EY : Yhi a b zl zu = Z.max ((b+1)*zl-1) ((b+1)*zu-1)).
    { unfold Yhi. apply Z.max_r. apply Z.max_lub.
      - apply Z.le_trans with ((b+1)*zl-1); [nia | apply Z.le_max_l].
      - apply Z.le_trans with ((b+1)*zu-1); [nia | apply Z.le_max_r]. }
    rewrite EY.
    assert (D1 : Z.div (-1) zl = -1) by (pose proof (Z.div_mod (-1) zl ltac:(lia)); pose proof (Z.mod_pos_bound (-1) zl ltac:(lia)); nia).
    assert (D2 : Z.div (-1) zu = -1) by (pose proof (Z.div_mod (-1) zu ltac:(lia)); pose proof (Z.mod_pos_bound (-1) zu ltac:(lia)); nia).
    destruct (Z.max_spec ((b+1)*zl-1) ((b+1)*zu-1)) as [[_ E]|[_ E]]; rewrite E.
    + exists b, zu. repeat split; try lia.
      replace ((b+1)*zu-1) with ((b+1)*zu+(-1)) by ring. rewrite Z.div_add_l by lia. rewrite D2. lia.
    + exists b, zl. repeat split; try lia.
      replace ((b+1)*zl-1) with ((b+1)*zl+(-1)) by ring. rewrite Z.div_add_l by lia. rewrite D1. lia.
  - assert (EY : Yhi a b zl zu = Z.max (a*zl) (a*zu)).
    { unfold Yhi. apply Z.max_l. apply Z.max_lub.
      - apply Z.le_trans with (a*zl); [nia | apply Z.le_max_l].
      - apply Z.le_trans with (a*zu); [nia | apply Z.le_max_r]. }
    rewrite EY. destruct (Z.max_spec (a*zl) (a*zu)) as [[_ E]|[_ E]]; rewrite E.
    + exists a, zu. repeat split; try lia. symmetry; apply Z.div_mul; lia.
    + exists a, zl. repeat split; try lia. symmetry; apply Z.div_mul; lia.
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

(* --- Multiplicative bounds for cdiv / Z.div used by [fden_opt] --- *)
Lemma cdiv_mul_le_neg : forall n M, M < 0 -> M * cdiv n M <= n.
Proof.
  intros n M HM. unfold cdiv.
  pose proof (Z.div_mod (- n) M ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound (- n) M HM) as B.
  set (P := (- n) / M) in *. nia.
Qed.

Lemma cdiv_mul_ge : forall n b, 0 < b -> n <= b * cdiv n b.
Proof.
  intros n b Hb. unfold cdiv.
  pose proof (Z.mul_div_le (- n) b Hb) as H.
  set (Q := (- n) / b) in *. nia.
Qed.

Lemma div_mul_ge_neg : forall p q, q < 0 -> p <= q * (p / q).
Proof.
  intros p q Hq.
  pose proof (Z.div_mod p q ltac:(lia)) as D.
  pose proof (Z.mod_neg_bound p q Hq) as B.
  set (Q := p / q) in *. nia.
Qed.

(* Wrappers packaging the band witness builders into the mem/sol interface:
   a positive divisor [w] satisfying both band constraints is realizable. *)
Lemma fden_opt_pos_w : forall ix iy w,
  0 < w -> lo ix <= hi ix -> lo iy <= hi iy ->
  lo ix * w <= hi iy -> lo iy + 1 <= (hi ix + 1) * w ->
  exists x y, mem ix x /\ mem iy y /\ sol x y w.
Proof.
  intros ix iy w Hw Hab Hcd HA HB.
  destruct (witness_pos (lo ix) (hi ix) (lo iy) (hi iy) w Hw Hab Hcd HA ltac:(lia))
    as (x & y & Hx & Hy & Hz & Hxy).
  exists x, y. unfold mem, sol. tauto.
Qed.

Lemma fden_opt_neg_w : forall ix iy w,
  w < 0 -> lo ix <= hi ix -> lo iy <= hi iy ->
  lo iy <= lo ix * w -> (hi ix + 1) * w <= hi iy - 1 ->
  exists x y, mem ix x /\ mem iy y /\ sol x y w.
Proof.
  intros ix iy w Hw Hab Hcd HA HB.
  destruct (realize_neg (lo ix) (hi ix) (lo iy) (hi iy) w Hw Hab Hcd HA ltac:(lia))
    as (x & y & Hx & Hy & Hz & Hxy).
  exists x, y. unfold mem, sol. tauto.
Qed.

(* fden z-optimality, both signs combined: the bounds of the (nonempty)
   refined interval satisfy the two band constraints by construction, and the
   band witness builders [witness_pos]/[realize_neg] realize them. *)
Lemma fden_opt : forall ix iy iz,
  (0 < lo iz \/ hi iz < 0) -> lo ix <= hi ix -> lo iy <= hi iy ->
  ile ix (Cx iy iz) -> lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
  intros ix iy iz Hsign Hxne Hyne _.
  unfold fden; cbv zeta.
  destruct (Z.ltb_spec 0 (lo iz)) as [Hzl|Hzl].
  - (* positive divisor side *)
    match goal with |- context[if ?g then _ else _] => destruct g eqn:Hk end.
    + (* kill row: refined interval is [1,0], contradicts nonemptiness *)
      cbn [lo hi]. intro Habs. exfalso. lia.
    + cbn [lo hi]. intro Hne.
      apply Bool.orb_false_iff in Hk. destruct Hk as [Hk1 Hk2].
      assert (Hka : lo ix = 0 -> 0 <= hi iy).
      { intro Ha0. apply Bool.andb_false_iff in Hk1.
        destruct Hk1 as [K|K]; [apply Z.eqb_neq in K; lia | apply Z.ltb_ge in K; lia]. }
      assert (Hkb : hi ix + 1 = 0 -> lo iy < 0).
      { intro Hb0. apply Bool.andb_false_iff in Hk2.
        destruct Hk2 as [K|K]; [apply Z.eqb_neq in K; lia | apply Z.leb_gt in K; lia]. }
      (* every w between the refined bounds satisfies both band constraints *)
      assert (HA : forall w, (if lo ix <? 0 then cdiv (hi iy) (lo ix) else lo iz) <= w ->
                             w <= (if 0 <? lo ix then hi iy / lo ix else hi iz) ->
                             lo ix * w <= hi iy).
      { destruct (Z.ltb_spec (lo ix) 0) as [Ha|Ha].
        - intros w Hw _. pose proof (cdiv_mul_le_neg (hi iy) (lo ix) Ha). nia.
        - destruct (Z.ltb_spec 0 (lo ix)) as [Ha'|Ha'].
          + intros w _ Hw. pose proof (Z.mul_div_le (hi iy) (lo ix) Ha'). nia.
          + intros w _ _. assert (Ha0 : lo ix = 0) by lia.
            specialize (Hka Ha0). rewrite Ha0. lia. }
      assert (HB : forall w, (if 0 <? hi ix + 1 then cdiv (lo iy + 1) (hi ix + 1) else lo iz) <= w ->
                             w <= (if hi ix + 1 <? 0 then (lo iy + 1) / (hi ix + 1) else hi iz) ->
                             lo iy + 1 <= (hi ix + 1) * w).
      { destruct (Z.ltb_spec 0 (hi ix + 1)) as [Hb|Hb].
        - intros w Hw _. pose proof (cdiv_mul_ge (lo iy + 1) (hi ix + 1) Hb). nia.
        - destruct (Z.ltb_spec (hi ix + 1) 0) as [Hb'|Hb'].
          + intros w _ Hw. pose proof (div_mul_ge_neg (lo iy + 1) (hi ix + 1) Hb'). nia.
          + intros w _ _. specialize (Hkb ltac:(lia)).
            replace (hi ix + 1) with 0 by lia. lia. }
      split.
      * apply fden_opt_pos_w; [lia | lia | lia | apply HA; lia | apply HB; lia].
      * apply fden_opt_pos_w; [lia | lia | lia | apply HA; lia | apply HB; lia].
  - destruct (Z.ltb_spec (hi iz) 0) as [Hzu|Hzu].
    + (* negative divisor side *)
      match goal with |- context[if ?g then _ else _] => destruct g eqn:Hk end.
      * (* kill row *)
        cbn [lo hi]. intro Habs. exfalso. lia.
      * cbn [lo hi]. intro Hne.
        apply Bool.orb_false_iff in Hk. destruct Hk as [Hk1 Hk2].
        assert (Hka : lo ix = 0 -> lo iy <= 0).
        { intro Ha0. apply Bool.andb_false_iff in Hk1.
          destruct Hk1 as [K|K]; [apply Z.eqb_neq in K; lia | apply Z.ltb_ge in K; lia]. }
        assert (Hkb : hi ix + 1 = 0 -> 0 < hi iy).
        { intro Hb0. apply Bool.andb_false_iff in Hk2.
          destruct Hk2 as [K|K]; [apply Z.eqb_neq in K; lia | apply Z.leb_gt in K; lia]. }
        assert (HA : forall w, (if 0 <? lo ix then cdiv (lo iy) (lo ix) else lo iz) <= w ->
                               w <= (if lo ix <? 0 then lo iy / lo ix else hi iz) ->
                               lo iy <= lo ix * w).
        { destruct (Z.ltb_spec 0 (lo ix)) as [Ha|Ha].
          - intros w Hw _. pose proof (cdiv_mul_ge (lo iy) (lo ix) Ha). nia.
          - destruct (Z.ltb_spec (lo ix) 0) as [Ha'|Ha'].
            + intros w _ Hw. pose proof (div_mul_ge_neg (lo iy) (lo ix) Ha'). nia.
            + intros w _ _. assert (Ha0 : lo ix = 0) by lia.
              specialize (Hka Ha0). rewrite Ha0. lia. }
        assert (HB : forall w, (if hi ix + 1 <? 0 then cdiv (hi iy - 1) (hi ix + 1) else lo iz) <= w ->
                               w <= (if 0 <? hi ix + 1 then (hi iy - 1) / (hi ix + 1) else hi iz) ->
                               (hi ix + 1) * w <= hi iy - 1).
        { destruct (Z.ltb_spec (hi ix + 1) 0) as [Hb|Hb].
          - intros w Hw _. pose proof (cdiv_mul_le_neg (hi iy - 1) (hi ix + 1) Hb). nia.
          - destruct (Z.ltb_spec 0 (hi ix + 1)) as [Hb'|Hb'].
            + intros w _ Hw. pose proof (Z.mul_div_le (hi iy - 1) (hi ix + 1) Hb'). nia.
            + intros w _ _. specialize (Hkb ltac:(lia)).
              replace (hi ix + 1) with 0 by lia. lia. }
        split.
        -- apply fden_opt_neg_w; [lia | lia | lia | apply HA; lia | apply HB; lia].
        -- apply fden_opt_neg_w; [lia | lia | lia | apply HA; lia | apply HB; lia].
    + (* straddling divisor interval: excluded by the sign hypothesis *)
      intros _. exfalso. destruct Hsign as [H|H]; lia.
Qed.


(* ================================================================= *)
(** ** Reductivity: propagator s <= s  (formerly optbase2.v)          *)
(* ================================================================= *)

Lemma ile_refl : forall i, ile i i.
Proof. intro i; unfold ile; lia. Qed.
Lemma ile_trans : forall i j k, ile i j -> ile j k -> ile i k.
Proof. unfold ile; intros i j k [??] [??]; lia. Qed.
Lemma inter_ile_l : forall i j, ile (inter i j) i.
Proof. intros i j; unfold ile, inter; cbn [lo hi]; lia. Qed.
Lemma ijoin_ile : forall i j k, ile i k -> ile j k -> ile (ijoin i j) k.
Proof. unfold ile, ijoin; cbn [lo hi]; intros i j k [??] [??]; lia. Qed.
Lemma sle_trans : forall a b c, sle a b -> sle b c -> sle a c.
Proof.
  unfold sle; intros a b c [Hx [Hy Hz]] [Hx' [Hy' Hz']];
  split; [|split]; eapply ile_trans; eassumption.
Qed.

Lemma restrict_z_pos_ile : forall t, sle (restrict_z_pos t) t.
Proof.
  intro t; unfold restrict_z_pos, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply ile_refl | apply inter_ile_l]].
Qed.
Lemma restrict_z_neg_ile : forall t, sle (restrict_z_neg t) t.
Proof.
  intro t; unfold restrict_z_neg, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply ile_refl | apply inter_ile_l]].
Qed.
Lemma fdivxz_pos_ile : forall w, sle (fdivxz_pos w) w.
Proof.
  intro w. unfold fdivxz_pos; cbv zeta; unfold sle; cbn [sx sy sz].
  split; [ eapply ile_trans; apply inter_ile_l
         | split; [apply ile_refl | apply inter_ile_l] ].
Qed.
Lemma fdivxz_neg_ile : forall w, sle (fdivxz_neg w) w.
Proof.
  intro w. unfold fdivxz_neg; cbv zeta; unfold sle; cbn [sx sy sz].
  split; [ eapply ile_trans; apply inter_ile_l
         | split; [apply ile_refl | apply inter_ile_l] ].
Qed.
Lemma refine_y_ile : forall w, sle (refine_y w) w.
Proof.
  intro w; unfold refine_y, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply inter_ile_l | apply ile_refl]].
Qed.
Lemma sqcupbot_ile : forall a b t, sle a t -> sle b t -> sle (sqcupbot a b) t.
Proof.
  intros a b t Ha Hb. unfold sqcupbot.
  destruct (ne_store a), (ne_store b); cbn iota; try assumption.
  unfold sjoin, sle in *; cbn [sx sy sz].
  destruct Ha as [Hax [Hay Haz]]; destruct Hb as [Hbx [Hby Hbz]].
  split; [|split]; apply ijoin_ile; assumption.
Qed.

Theorem fdiv_reductive : forall s, sle (propagator s) s.
Proof.
  intro s. unfold propagator.
  eapply sle_trans; [apply refine_y_ile|].
  apply sqcupbot_ile.
  - eapply sle_trans; [apply fdivxz_neg_ile | apply restrict_z_neg_ile].
  - eapply sle_trans; [apply fdivxz_pos_ile | apply restrict_z_pos_ile].
Qed.

(* ================================================================= *)
(** ** Branch attainment, optimality (fdiv_best), and the             *)
(**    closure-operator corollaries  (formerly optimal.v)            *)
(* ================================================================= *)

(* ================================================================= *)
(*  fden is reductive on the z-interval it refines (except bottom).   *)
(* ================================================================= *)
Lemma fden_bounds : forall ix iy iz,
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  lo iz <= lo (fden ix iy iz) /\ hi (fden ix iy iz) <= hi iz.
Proof.
  intros ix iy iz. unfold fden; cbv zeta.
  set (a := lo ix). set (b := hi ix). set (c := lo iy). set (d := hi iy).
  set (zl := lo iz). set (zu := hi iz).
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end);
    cbn [lo hi];
    intro Hne;
    repeat first [ split | apply Z.le_max_l | apply Z.le_min_l ];
    try (pose proof (Z.le_max_l zl); pose proof (Z.le_min_l zu); lia).
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

(* ================================================================= *)
(*  BLU_branch: for a sign-definite, non-empty branch [fdivxz_pos w], *)
(*  the eight band inequalities relating its quotient window [a,b],   *)
(*  its refined divisor window [zl,zu] and the y-interval [c,d] hold.  *)
(* ================================================================= *)
Lemma BLU_branch : forall w,
  (0 < lo (sz w) \/ hi (sz w) < 0) ->
  lo (sx (fdivxz_pos w)) <= hi (sx (fdivxz_pos w)) ->
  lo (sy w) <= hi (sy w) ->
  lo (sz (fdivxz_pos w)) <= hi (sz (fdivxz_pos w)) ->
  (0 < hi (sz (fdivxz_pos w)) -> lo (sx (fdivxz_pos w)) * hi (sz (fdivxz_pos w)) <= hi (sy w)) /\
  (0 < lo (sz (fdivxz_pos w)) -> lo (sx (fdivxz_pos w)) * lo (sz (fdivxz_pos w)) <= hi (sy w)) /\
  (lo (sz (fdivxz_pos w)) < 0 -> (hi (sx (fdivxz_pos w))+1) * lo (sz (fdivxz_pos w)) + 1 <= hi (sy w)) /\
  (hi (sz (fdivxz_pos w)) < 0 -> (hi (sx (fdivxz_pos w))+1) * hi (sz (fdivxz_pos w)) + 1 <= hi (sy w)) /\
  (0 < hi (sz (fdivxz_pos w)) -> lo (sy w) <= (hi (sx (fdivxz_pos w))+1) * hi (sz (fdivxz_pos w)) - 1) /\
  (0 < lo (sz (fdivxz_pos w)) -> lo (sy w) <= (hi (sx (fdivxz_pos w))+1) * lo (sz (fdivxz_pos w)) - 1) /\
  (lo (sz (fdivxz_pos w)) < 0 -> lo (sy w) <= lo (sx (fdivxz_pos w)) * lo (sz (fdivxz_pos w))) /\
  (hi (sz (fdivxz_pos w)) < 0 -> lo (sy w) <= lo (sx (fdivxz_pos w)) * hi (sz (fdivxz_pos w))).
Proof.
  intros w Hsign Hab Hcd Hzlzu.
  unfold fdivxz_pos in *; cbv zeta in *; cbn [sx sy sz] in *.
  set (c := lo (sy w)) in *. set (d := hi (sy w)) in *.
  set (I1 := {| lo := Xlo c d (lo (sz w)) (hi (sz w));
                hi := Xhi c d (lo (sz w)) (hi (sz w)) |}) in *.
  set (ix1 := inter (sx w) I1) in *.
  set (iz0 := fden ix1 (sy w) (sz w)) in *.
  set (iz := inter (sz w) iz0) in *.
  set (zl := lo iz) in *. set (zu := hi iz) in *.
  set (I2 := {| lo := Xlo c d zl zu; hi := Xhi c d zl zu |}) in *.
  set (ix2 := inter ix1 I2) in *.
  set (a := lo ix2) in *. set (b := hi ix2) in *.
  assert (Ezl : zl = Z.max (lo (sz w)) (lo iz0)) by reflexivity.
  assert (Ezu : zu = Z.min (hi (sz w)) (hi iz0)) by reflexivity.
  assert (Ea : a = Z.max (lo ix1) (Xlo c d zl zu)) by reflexivity.
  assert (Eb : b = Z.min (hi ix1) (Xhi c d zl zu)) by reflexivity.
  assert (Hiz0ne : lo iz0 <= hi iz0).
  { pose proof (Z.le_max_r (lo (sz w)) (lo iz0)).
    pose proof (Z.le_min_r (hi (sz w)) (hi iz0)). lia. }
  destruct (fden_bounds ix1 (sy w) (sz w) Hiz0ne) as [Hlb Hub].
  assert (Hzl : zl = lo iz0) by (rewrite Ezl; apply Z.max_r; exact Hlb).
  assert (Hzu : zu = hi iz0) by (rewrite Ezu; apply Z.min_r; exact Hub).
  assert (Hix1 : lo ix1 <= hi ix1).
  { pose proof (Z.le_max_l (lo ix1) (Xlo c d zl zu)).
    pose proof (Z.le_min_l (hi ix1) (Xhi c d zl zu)). lia. }
  assert (HCx : Cx (sy w) (sz w) = I1) by reflexivity.
  assert (Htight : ile ix1 (Cx (sy w) (sz w))).
  { rewrite HCx. unfold ix1, ile, inter; cbn [lo hi].
    split; [ apply Z.le_max_r | apply Z.le_min_r ]. }
  assert (Hsz : 0 < zl \/ zu < 0) by (destruct Hsign; [left; lia | right; lia]).
  destruct (fden_opt ix1 (sy w) (sz w) Hsign Hix1 Hcd Htight Hiz0ne) as [Hsoll Hsolu].
  destruct Hsoll as [xl [yl [Hmxl [Hmyl Hsl]]]].
  destruct Hsolu as [xu [yu [Hmxu [Hmyu Hsu]]]].
  change (fden ix1 (sy w) (sz w)) with iz0 in Hsl, Hsu.
  rewrite <- Hzl in Hsl. rewrite <- Hzu in Hsu.
  unfold mem in Hmxl, Hmyl, Hmxu, Hmyu.
  destruct Hsl as [Hzlnz Hxleq]. destruct Hsu as [Hzunz Hxueq].
  assert (Hencl : Xlo c d zl zu <= xl <= Xhi c d zl zu).
  { destruct Hsz as [Hp|Hn].
    - apply (fdiv_sound_pos xl yl zl c d zl zu); [ lia | lia | lia | split; [exact Hzlnz|exact Hxleq] ].
    - apply (fdiv_sound_neg xl yl zl c d zl zu); [ lia | lia | lia | split; [exact Hzlnz|exact Hxleq] ]. }
  assert (Hencu : Xlo c d zl zu <= xu <= Xhi c d zl zu).
  { destruct Hsz as [Hp|Hn].
    - apply (fdiv_sound_pos xu yu zu c d zl zu); [ lia | lia | lia | split; [exact Hzunz|exact Hxueq] ].
    - apply (fdiv_sound_neg xu yu zu c d zl zu); [ lia | lia | lia | split; [exact Hzunz|exact Hxueq] ]. }
  assert (Haxl : a <= xl <= b).
  { rewrite Ea, Eb. split; [ apply Z.max_lub; lia | apply Z.min_glb; lia ]. }
  assert (Haxu : a <= xu <= b).
  { rewrite Ea, Eb. split; [ apply Z.max_lub; lia | apply Z.min_glb; lia ]. }
  apply (band_from_sols a b c d zl zu xl yl xu yu Hzlzu Hsz Hmyl Hmyu Hzlnz Hxleq Hzunz Hxueq Haxl Haxu).
Qed.

(* ================================================================= *)
(*  The two sign-definite branches share the same enclosure code.     *)
(* ================================================================= *)
Lemma fdivxz_neg_eq_pos : forall w, fdivxz_neg w = fdivxz_pos w.
Proof. reflexivity. Qed.

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

(* ---- Ylo / Yhi are divided back into [a,b] by a z-corner ---- *)
Lemma corner_Ylo : forall a b zl zu,
  a <= b -> zl <= zu -> zl <> 0 -> zu <> 0 ->
  exists zc, (zc = zl \/ zc = zu) /\ zc <> 0 /\ a <= (Ylo a b zl zu) / zc <= b.
Proof.
  intros a b zl zu Hab Hz Hzln Hzun. unfold Ylo.
  destruct (Z.min_spec (Z.min (a*zl) (a*zu)) (Z.min ((b+1)*zl+1) ((b+1)*zu+1)))
    as [[Hlt E]|[Hle E]]; rewrite E.
  - destruct (Z.min_spec (a*zl) (a*zu)) as [[_ E2]|[_ E2]]; rewrite E2.
    + exists zl. split; [left; reflexivity| split; [exact Hzln|]].
      rewrite Z.div_mul by exact Hzln. lia.
    + exists zu. split; [right; reflexivity| split; [exact Hzun|]].
      rewrite Z.div_mul by exact Hzun. lia.
  - destruct (Z.min_spec ((b+1)*zl+1) ((b+1)*zu+1)) as [[_ E2]|[_ E2]]; rewrite E2.
    + exists zl. split; [left; reflexivity| split; [exact Hzln|]].
      assert (zl < 0) by nia. apply band_neg; [ lia | lia | nia ].
    + exists zu. split; [right; reflexivity| split; [exact Hzun|]].
      assert (zu < 0) by nia. apply band_neg; [ lia | lia | nia ].
Qed.

Lemma corner_Yhi : forall a b zl zu,
  a <= b -> zl <= zu -> zl <> 0 -> zu <> 0 ->
  exists zc, (zc = zl \/ zc = zu) /\ zc <> 0 /\ a <= (Yhi a b zl zu) / zc <= b.
Proof.
  intros a b zl zu Hab Hz Hzln Hzun. unfold Yhi.
  destruct (Z.max_spec (Z.max (a*zl) (a*zu)) (Z.max ((b+1)*zl-1) ((b+1)*zu-1)))
    as [[Hlt E]|[Hge E]]; rewrite E.
  - destruct (Z.max_spec ((b+1)*zl-1) ((b+1)*zu-1)) as [[_ E2]|[_ E2]]; rewrite E2.
    + exists zu. split; [right; reflexivity| split; [exact Hzun|]].
      assert (zu > 0) by nia. apply band_pos; [ lia | nia | lia ].
    + exists zl. split; [left; reflexivity| split; [exact Hzln|]].
      assert (zl > 0) by nia. apply band_pos; [ lia | nia | lia ].
  - destruct (Z.max_spec (a*zl) (a*zu)) as [[_ E2]|[_ E2]]; rewrite E2.
    + exists zu. split; [right; reflexivity| split; [exact Hzun|]].
      rewrite Z.div_mul by exact Hzun. lia.
    + exists zl. split; [left; reflexivity| split; [exact Hzln|]].
      rewrite Z.div_mul by exact Hzln. lia.
Qed.

(* ---- corner selection from the band inequalities ---- *)
Lemma pick_hi : forall a b zl zu Y,
  a <= b -> zl <= zu -> zl <> 0 -> zu <> 0 ->
  Y <= Yhi a b zl zu ->
  (0 < zu -> a*zu <= Y) ->
  (0 < zl -> a*zl <= Y) ->
  (zl < 0 -> (b+1)*zl + 1 <= Y) ->
  (zu < 0 -> (b+1)*zu + 1 <= Y) ->
  exists z, zl <= z <= zu /\ z <> 0 /\ a <= Y / z <= b.
Proof.
  intros a b zl zu Y Hab Hz Hzl0 Hzu0 HY L1 L2 L3 L4.
  unfold Yhi in HY.
  destruct (Z.max_spec (Z.max (a*zl) (a*zu)) (Z.max ((b+1)*zl-1) ((b+1)*zu-1)))
    as [[_ E]|[_ E]]; rewrite E in HY.
  - destruct (Z.max_spec ((b+1)*zl-1) ((b+1)*zu-1)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply band_pos; [lia | apply L1; lia | lia].
      * assert (zu < 0) by lia. apply band_neg; [lia | apply L4; lia | nia].
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply band_pos; [lia | apply L2; lia | lia].
      * assert (zl < 0) by lia. apply band_neg; [lia | apply L3; lia | nia].
  - destruct (Z.max_spec (a*zl) (a*zu)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply band_pos; [lia | apply L1; lia | nia].
      * assert (zu < 0) by lia. apply band_neg; [lia | apply L4; lia | lia].
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply band_pos; [lia | apply L2; lia | nia].
      * assert (zl < 0) by lia. apply band_neg; [lia | apply L3; lia | lia].
Qed.

Lemma pick_lo : forall a b zl zu Y,
  a <= b -> zl <= zu -> zl <> 0 -> zu <> 0 ->
  Ylo a b zl zu <= Y ->
  (0 < zu -> Y <= (b+1)*zu - 1) ->
  (0 < zl -> Y <= (b+1)*zl - 1) ->
  (zl < 0 -> Y <= a*zl) ->
  (zu < 0 -> Y <= a*zu) ->
  exists z, zl <= z <= zu /\ z <> 0 /\ a <= Y / z <= b.
Proof.
  intros a b zl zu Y Hab Hz Hzl0 Hzu0 HY U1 U2 U3 U4.
  unfold Ylo in HY.
  destruct (Z.min_spec (Z.min (a*zl) (a*zu)) (Z.min ((b+1)*zl+1) ((b+1)*zu+1)))
    as [[_ E]|[_ E]]; rewrite E in HY.
  - destruct (Z.min_spec (a*zl) (a*zu)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply band_pos; [lia | lia | apply U2; lia].
      * assert (zl < 0) by lia. apply band_neg; [lia | nia | apply U3; lia].
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply band_pos; [lia | lia | apply U1; lia].
      * assert (zu < 0) by lia. apply band_neg; [lia | nia | apply U4; lia].
  - destruct (Z.min_spec ((b+1)*zl+1) ((b+1)*zu+1)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply band_pos; [lia | nia | apply U2; lia].
      * assert (zl < 0) by lia. apply band_neg; [lia | lia | apply U3; lia].
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply band_pos; [lia | nia | apply U1; lia].
      * assert (zu < 0) by lia. apply band_neg; [lia | lia | apply U4; lia].
Qed.

(* ================================================================= *)
(*  Structural facts about the propagator output.                     *)
(* ================================================================= *)
Lemma prop_branches : forall s,
  propagator s = refine_y (sqcupbot (fdivxz_pos (restrict_z_neg s))
                                    (fdivxz_pos (restrict_z_pos s))).
Proof. intro s. unfold propagator. rewrite fdivxz_neg_eq_pos. reflexivity. Qed.

Lemma sy_sqcupbot_branches : forall s,
  lo (sy (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))) = lo (sy s) /\
  hi (sy (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))) = hi (sy s).
Proof.
  intro s. unfold sqcupbot.
  set (A := fdivxz_pos (restrict_z_neg s)).
  set (B := fdivxz_pos (restrict_z_pos s)).
  assert (HA : sy A = sy s) by reflexivity.
  assert (HB : sy B = sy s) by reflexivity.
  destruct (ne_store A); destruct (ne_store B); cbn iota.
  - unfold sjoin; cbn [sy]. rewrite HA, HB. unfold ijoin; cbn [lo hi].
    split; [ apply Z.min_id | apply Z.max_id ].
  - rewrite HA; split; reflexivity.
  - rewrite HB; split; reflexivity.
  - rewrite HB; split; reflexivity.
Qed.

(* ================================================================= *)
(*  The lift: the joined output's z-corners are non-zero and satisfy  *)
(*  the eight band inequalities (w.r.t. the input y-interval [c,d]).  *)
(* ================================================================= *)
Lemma prop_bands : forall s, consistent (propagator s) ->
  lo (sz (propagator s)) <> 0 /\ hi (sz (propagator s)) <> 0 /\
  (0 < hi (sz (propagator s)) -> lo (sx (propagator s)) * hi (sz (propagator s)) <= hi (sy s)) /\
  (0 < lo (sz (propagator s)) -> lo (sx (propagator s)) * lo (sz (propagator s)) <= hi (sy s)) /\
  (lo (sz (propagator s)) < 0 -> (hi (sx (propagator s))+1) * lo (sz (propagator s)) + 1 <= hi (sy s)) /\
  (hi (sz (propagator s)) < 0 -> (hi (sx (propagator s))+1) * hi (sz (propagator s)) + 1 <= hi (sy s)) /\
  (0 < hi (sz (propagator s)) -> lo (sy s) <= (hi (sx (propagator s))+1) * hi (sz (propagator s)) - 1) /\
  (0 < lo (sz (propagator s)) -> lo (sy s) <= (hi (sx (propagator s))+1) * lo (sz (propagator s)) - 1) /\
  (lo (sz (propagator s)) < 0 -> lo (sy s) <= lo (sx (propagator s)) * lo (sz (propagator s))) /\
  (hi (sz (propagator s)) < 0 -> lo (sy s) <= lo (sx (propagator s)) * hi (sz (propagator s))).
Proof.
  intros s Hcons.
  pose proof (fdiv_reductive s) as Hred.
  unfold sle in Hred. destruct Hred as [_ [Hrey _]]. unfold ile in Hrey.
  assert (Hsy_s : lo (sy s) <= hi (sy s)).
  { destruct Hcons as [_ [Hyy _]]. lia. }
  pose proof (prop_branches s) as Hpb.
  set (N := fdivxz_pos (restrict_z_neg s)) in *.
  set (P := fdivxz_pos (restrict_z_pos s)) in *.
  assert (HsxJ : sx (propagator s) = sx (sqcupbot N P))
    by (rewrite Hpb; unfold refine_y; cbn [sx]; reflexivity).
  assert (HszJ : sz (propagator s) = sz (sqcupbot N P))
    by (rewrite Hpb; unfold refine_y; cbn [sz]; reflexivity).
  destruct Hcons as [Hxx [Hyy Hzz]].
  rewrite HsxJ, HszJ in *.
  assert (HhiN : hi (sz N) <= -1).
  { unfold N, fdivxz_pos; cbv zeta; cbn [sz]. unfold restrict_z_neg; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  assert (HloP : 1 <= lo (sz P)).
  { unfold P, fdivxz_pos; cbv zeta; cbn [sz]. unfold restrict_z_pos; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  assert (HsignN : 0 < lo (sz (restrict_z_neg s)) \/ hi (sz (restrict_z_neg s)) < 0).
  { right. unfold restrict_z_neg; cbn [sz]. unfold inter; cbn [lo hi]. lia. }
  assert (HsignP : 0 < lo (sz (restrict_z_pos s)) \/ hi (sz (restrict_z_pos s)) < 0).
  { left. unfold restrict_z_pos; cbn [sz]. unfold inter; cbn [lo hi]. lia. }
  assert (HsyN : lo (sy (restrict_z_neg s)) <= hi (sy (restrict_z_neg s)))
    by (unfold restrict_z_neg; cbn [sy]; exact Hsy_s).
  assert (HsyP : lo (sy (restrict_z_pos s)) <= hi (sy (restrict_z_pos s)))
    by (unfold restrict_z_pos; cbn [sy]; exact Hsy_s).
  unfold sqcupbot. destruct (ne_store N) eqn:EN; destruct (ne_store P) eqn:EP; cbn iota.
  - (* both branches active: sjoin N P *)
    unfold ne_store in EN. apply andb_prop in EN. destruct EN as [EN12 ENz].
    apply andb_prop in EN12. destruct EN12 as [ENx _].
    unfold nonemptyb in ENx, ENz. apply Z.leb_le in ENx, ENz.
    unfold ne_store in EP. apply andb_prop in EP. destruct EP as [EP12 EPz].
    apply andb_prop in EP12. destruct EP12 as [EPx _].
    unfold nonemptyb in EPx, EPz. apply Z.leb_le in EPx, EPz.
    assert (HzNn : lo (sz N) < 0 /\ hi (sz N) < 0) by lia.
    assert (HzPp : 0 < lo (sz P) /\ 0 < hi (sz P)) by lia.
    destruct (BLU_branch (restrict_z_neg s) HsignN ENx HsyN ENz)
      as [_ [_ [BN3 [_ [_ [_ [BN7 _]]]]]]].
    destruct (BLU_branch (restrict_z_pos s) HsignP EPx HsyP EPz)
      as [BP1 [_ [_ [_ [BP5 [_ [_ _]]]]]]].
    fold N in BN3, BN7. fold P in BP1, BP5.
    assert (HN3 : (hi (sx N) + 1) * lo (sz N) + 1 <= hi (sy s)) by (apply BN3; lia).
    assert (HN7 : lo (sy s) <= lo (sx N) * lo (sz N)) by (apply BN7; lia).
    assert (HP1 : lo (sx P) * hi (sz P) <= hi (sy s)) by (apply BP1; lia).
    assert (HP5 : lo (sy s) <= (hi (sx P) + 1) * hi (sz P) - 1) by (apply BP5; lia).
    clear BN3 BN7 BP1 BP5 HsignN HsignP Hpb HsxJ HszJ Hrey Hyy Hxx Hzz HsyN HsyP.
    unfold sjoin, ijoin; cbn [sx sz lo hi].
    pose proof (Z.le_min_l (lo (sx N)) (lo (sx P))) as M1.
    pose proof (Z.le_min_r (lo (sx N)) (lo (sx P))) as M2.
    pose proof (Z.le_max_l (hi (sx N)) (hi (sx P))) as M3.
    pose proof (Z.le_max_r (hi (sx N)) (hi (sx P))) as M4.
    assert (EZL : Z.min (lo (sz N)) (lo (sz P)) = lo (sz N)) by lia.
    assert (EZU : Z.max (hi (sz N)) (hi (sz P)) = hi (sz P)) by lia.
    rewrite EZL, EZU.
    repeat split; intro Hsg; try lia; nia.
  - (* only the negative branch active: returns N *)
    unfold ne_store in EN. apply andb_prop in EN. destruct EN as [EN12 ENz].
    apply andb_prop in EN12. destruct EN12 as [ENx _].
    unfold nonemptyb in ENx, ENz. apply Z.leb_le in ENx, ENz.
    assert (HzNn : lo (sz N) < 0 /\ hi (sz N) < 0) by lia.
    destruct (BLU_branch (restrict_z_neg s) HsignN ENx HsyN ENz)
      as [_ [_ [BN3 [BN4 [_ [_ [BN7 BN8]]]]]]].
    fold N in BN3, BN4, BN7, BN8.
    assert (HN3 : (hi (sx N) + 1) * lo (sz N) + 1 <= hi (sy s)) by (apply BN3; lia).
    assert (HN4 : (hi (sx N) + 1) * hi (sz N) + 1 <= hi (sy s)) by (apply BN4; lia).
    assert (HN7 : lo (sy s) <= lo (sx N) * lo (sz N)) by (apply BN7; lia).
    assert (HN8 : lo (sy s) <= lo (sx N) * hi (sz N)) by (apply BN8; lia).
    repeat split; intro Hsg; try lia; nia.
  - (* returns P, positive branch nonempty via ne_store *)
    unfold ne_store in EP. apply andb_prop in EP. destruct EP as [EP12 EPz].
    apply andb_prop in EP12. destruct EP12 as [EPx _].
    unfold nonemptyb in EPx, EPz. apply Z.leb_le in EPx, EPz.
    assert (HzPp : 0 < lo (sz P) /\ 0 < hi (sz P)) by lia.
    destruct (BLU_branch (restrict_z_pos s) HsignP EPx HsyP EPz)
      as [BP1 [BP2 [_ [_ [BP5 [BP6 [_ _]]]]]]].
    fold P in BP1, BP2, BP5, BP6.
    assert (HP1 : lo (sx P) * hi (sz P) <= hi (sy s)) by (apply BP1; lia).
    assert (HP2 : lo (sx P) * lo (sz P) <= hi (sy s)) by (apply BP2; lia).
    assert (HP5 : lo (sy s) <= (hi (sx P) + 1) * hi (sz P) - 1) by (apply BP5; lia).
    assert (HP6 : lo (sy s) <= (hi (sx P) + 1) * lo (sz P) - 1) by (apply BP6; lia).
    repeat split; intro Hsg; try lia; nia.
  - (* returns P, nonemptiness from consistency *)
    unfold sqcupbot in Hxx, Hzz. rewrite EN in Hxx, Hzz. cbn iota in Hxx, Hzz.
    assert (EPx : lo (sx P) <= hi (sx P)) by exact Hxx.
    assert (EPz : lo (sz P) <= hi (sz P)) by exact Hzz.
    assert (HzPp : 0 < lo (sz P) /\ 0 < hi (sz P)) by lia.
    destruct (BLU_branch (restrict_z_pos s) HsignP EPx HsyP EPz)
      as [BP1 [BP2 [_ [_ [BP5 [BP6 [_ _]]]]]]].
    fold P in BP1, BP2, BP5, BP6.
    assert (HP1 : lo (sx P) * hi (sz P) <= hi (sy s)) by (apply BP1; lia).
    assert (HP2 : lo (sx P) * lo (sz P) <= hi (sy s)) by (apply BP2; lia).
    assert (HP5 : lo (sy s) <= (hi (sx P) + 1) * hi (sz P) - 1) by (apply BP5; lia).
    assert (HP6 : lo (sy s) <= (hi (sx P) + 1) * lo (sz P) - 1) by (apply BP6; lia).
    repeat split; intro Hsg; try lia; nia.
Qed.

(* ---- refined y-bounds are meets with the numerator extremes ---- *)
Lemma prop_sy_lo : forall s,
  lo (sy (propagator s)) =
  Z.max (lo (sy s)) (Ylo (lo (sx (propagator s))) (hi (sx (propagator s)))
                         (lo (sz (propagator s))) (hi (sz (propagator s)))).
Proof.
  intro s. unfold propagator, refine_y; cbn [sy sx sz].
  rewrite fdivxz_neg_eq_pos. unfold inter; cbn [lo hi].
  destruct (sy_sqcupbot_branches s) as [H _]. rewrite H. reflexivity.
Qed.

Lemma prop_sy_hi : forall s,
  hi (sy (propagator s)) =
  Z.min (hi (sy s)) (Yhi (lo (sx (propagator s))) (hi (sx (propagator s)))
                         (lo (sz (propagator s))) (hi (sz (propagator s)))).
Proof.
  intro s. unfold propagator, refine_y; cbn [sy sx sz].
  rewrite fdivxz_neg_eq_pos. unfold inter; cbn [lo hi].
  destruct (sy_sqcupbot_branches s) as [_ H]. rewrite H. reflexivity.
Qed.

(* ================================================================= *)
(*  Main result: both refined y-bounds are attained by a solution     *)
(*  inside the input store.                                            *)
(* ================================================================= *)
Lemma y_attain : forall s, consistent (propagator s) ->
  (exists x z, in_store s x (lo (sy (propagator s))) z /\ sol x (lo (sy (propagator s))) z) /\
  (exists x z, in_store s x (hi (sy (propagator s))) z /\ sol x (hi (sy (propagator s))) z).
Proof.
  intros s Hcons.
  pose proof (fdiv_reductive s) as Hred. unfold sle, ile in Hred.
  destruct Hred as [[Rx1 Rx2] [[Ry1 Ry2] [Rz1 Rz2]]].
  pose proof (prop_bands s Hcons) as PB.
  destruct PB as [Hzln [Hzun [c1 [c2 [c3 [c4 [c5 [c6 [c7 c8]]]]]]]]].
  destruct Hcons as [Hxx [Hyy Hzz]].
  assert (Hcore : forall Y, lo (sy (propagator s)) <= Y -> Y <= hi (sy (propagator s)) ->
     (exists z, lo (sz (propagator s)) <= z <= hi (sz (propagator s)) /\ z <> 0 /\
        lo (sx (propagator s)) <= Y / z <= hi (sx (propagator s))) ->
     exists x z, in_store s x Y z /\ sol x Y z).
  { intros Y HYl HYh [z [Hzr [Hznz [Hxa Hxb]]]].
    exists (Y / z), z. split.
    - unfold in_store, mem. repeat split; lia.
    - unfold sol. split; [exact Hznz | reflexivity]. }
  split.
  - apply Hcore; [lia|lia|].
    rewrite prop_sy_lo.
    destruct (Z.max_spec (lo (sy s)) (Ylo (lo (sx (propagator s))) (hi (sx (propagator s)))
                (lo (sz (propagator s))) (hi (sz (propagator s))))) as [[Hlt E]|[Hge E]]; rewrite E.
    + destruct (corner_Ylo (lo (sx (propagator s))) (hi (sx (propagator s)))
                 (lo (sz (propagator s))) (hi (sz (propagator s))) Hxx Hzz Hzln Hzun)
        as [zc [Hzc [Hznz Hb]]].
      exists zc. split; [destruct Hzc; subst zc; lia | split; [exact Hznz | exact Hb]].
    + destruct (pick_lo (lo (sx (propagator s))) (hi (sx (propagator s)))
                 (lo (sz (propagator s))) (hi (sz (propagator s))) (lo (sy s))
                 Hxx Hzz Hzln Hzun Hge c5 c6 c7 c8) as [z [Hzr [Hznz Hb]]].
      exists z. split; [exact Hzr | split; [exact Hznz | exact Hb]].
  - apply Hcore; [lia|lia|].
    rewrite prop_sy_hi.
    destruct (Z.min_spec (hi (sy s)) (Yhi (lo (sx (propagator s))) (hi (sx (propagator s)))
                (lo (sz (propagator s))) (hi (sz (propagator s))))) as [[Hlt E]|[Hge E]]; rewrite E.
    + assert (HYle : hi (sy s) <= Yhi (lo (sx (propagator s))) (hi (sx (propagator s)))
                (lo (sz (propagator s))) (hi (sz (propagator s)))) by lia.
      destruct (pick_hi (lo (sx (propagator s))) (hi (sx (propagator s)))
                 (lo (sz (propagator s))) (hi (sz (propagator s))) (hi (sy s))
                 Hxx Hzz Hzln Hzun HYle c1 c2 c3 c4) as [z [Hzr [Hznz Hb]]].
      exists z. split; [exact Hzr | split; [exact Hznz | exact Hb]].
    + destruct (corner_Yhi (lo (sx (propagator s))) (hi (sx (propagator s)))
                 (lo (sz (propagator s))) (hi (sz (propagator s))) Hxx Hzz Hzln Hzun)
        as [zc [Hzc [Hznz Hb]]].
      exists zc. split; [destruct Hzc; subst zc; lia | split; [exact Hznz | exact Hb]].
Qed.

(* ================================================================= *)
(*  Branch (x,z) attainment + optimality, and the final assembly.    *)
(*  (imported verbatim from the self-contained optdev.v; the base     *)
(*   lemmas it uses live in optbase/optbase2 with identical names.)    *)
(* ================================================================= *)

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
  - subst z. rewrite !Zdiv_0_r. lia.
  - assert (c / z <= y / z) by (apply Z.div_le_mono; lia).
    assert (y / z <= d / z) by (apply Z.div_le_mono; lia).
    lia.
Qed.

Lemma branch_attain : forall w,
  (0 < lo (sz w) \/ hi (sz w) < 0) ->
  lo (sy w) <= hi (sy w) ->
  lo (sx (fdivxz_pos w)) <= hi (sx (fdivxz_pos w)) ->
  lo (sz (fdivxz_pos w)) <= hi (sz (fdivxz_pos w)) ->
  (exists y z, in_store w (lo (sx (fdivxz_pos w))) y z /\ sol (lo (sx (fdivxz_pos w))) y z) /\
  (exists y z, in_store w (hi (sx (fdivxz_pos w))) y z /\ sol (hi (sx (fdivxz_pos w))) y z) /\
  (exists x y, in_store w x y (lo (sz (fdivxz_pos w))) /\ sol x y (lo (sz (fdivxz_pos w)))) /\
  (exists x y, in_store w x y (hi (sz (fdivxz_pos w))) /\ sol x y (hi (sz (fdivxz_pos w)))).
Proof.
  intros w Hsign Hy Hxne Hzne.
  unfold fdivxz_pos in *; cbv zeta in *.
  cbn [sx sy sz] in *.
  set (iy := sy w) in *.
  set (iz0 := sz w) in *.
  set (I1 := Itv (Xlo (lo iy) (hi iy) (lo iz0) (hi iz0)) (Xhi (lo iy) (hi iy) (lo iz0) (hi iz0))) in *.
  set (ix1 := inter (sx w) I1) in *.
  set (fd := fden ix1 iy iz0) in *.
  set (iz := inter iz0 fd) in *.
  set (I2 := Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))) in *.
  set (ix2 := inter ix1 I2) in *.
  (* ---- common facts ---- *)
  assert (Hfne : lo fd <= hi fd).
  { unfold iz, inter in Hzne; cbn [lo hi] in Hzne. lia. }
  assert (Hfin : lo iz0 <= lo fd /\ hi fd <= hi iz0) by (apply fden_bounds; exact Hfne).
  assert (Hlz : lo iz = lo fd) by (unfold iz, inter; cbn [lo hi]; lia).
  assert (Hhz : hi iz = hi fd) by (unfold iz, inter; cbn [lo hi]; lia).
  assert (Hlz0 : lo iz0 <= lo iz) by (unfold iz, inter; cbn [lo hi]; lia).
  assert (Hhz0 : hi iz <= hi iz0) by (unfold iz, inter; cbn [lo hi]; lia).
  assert (Hizs : 0 < lo iz \/ hi iz < 0) by (destruct Hsign; [left|right]; lia).
  assert (Hx2x1 : lo ix1 <= lo ix2 /\ hi ix2 <= hi ix1)
    by (unfold ix2, inter; cbn [lo hi]; lia).
  assert (Hx1ne : lo ix1 <= hi ix1) by lia.
  assert (Hx1sx : lo (sx w) <= lo ix1 /\ hi ix1 <= hi (sx w))
    by (unfold ix1, inter; cbn [lo hi]; lia).
  assert (HileI1 : Xlo (lo iy) (hi iy) (lo iz0) (hi iz0) <= lo ix1
                   /\ hi ix1 <= Xhi (lo iy) (hi iy) (lo iz0) (hi iz0))
    by (unfold ix1, inter, I1; cbn [lo hi]; lia).
  assert (Hx2I2 : Xlo (lo iy) (hi iy) (lo iz) (hi iz) <= lo ix2
                  /\ hi ix2 <= Xhi (lo iy) (hi iy) (lo iz) (hi iz))
    by (unfold ix2, inter, I2; cbn [lo hi]; lia).
  assert (HileCx : ile ix1 (Cx iy iz0))
    by (unfold ile, Cx; cbn [lo hi]; exact HileI1).
  destruct (fden_opt ix1 iy iz0 Hsign Hx1ne Hy HileCx Hfne) as [Zlo Zhi].
  assert (Hlox2 : lo ix2 = Z.max (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz)))
    by (unfold ix2, inter, I2; cbn [lo hi]; reflexivity).
  assert (Hhix2 : hi ix2 = Z.min (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)))
    by (unfold ix2, inter, I2; cbn [lo hi]; reflexivity).
  assert (Hiznz : lo iz <> 0 /\ hi iz <> 0) by (split; destruct Hizs; lia).
  assert (Hmemiz : (lo iz0 <= lo iz <= hi iz0) /\ (lo iz0 <= hi iz <= hi iz0)) by (split; lia).
  assert (Hfinish : forall v, lo (sx w) <= v <= hi (sx w) ->
    (exists y z, (lo iy <= y <= hi iy) /\ (lo iz0 <= z <= hi iz0) /\ z <> 0 /\ v = y / z) ->
    exists y z, in_store w v y z /\ sol v y z).
  { intros v Hmv [y [z [Hy2 [Hz2 [Hnz Heq]]]]]. exists y, z.
    unfold in_store, sol, mem; cbn [sx sy sz]. fold iy iz0.
    repeat split; try lia; try assumption. }
  assert (Hmemlo : lo (sx w) <= lo ix2 <= hi (sx w)) by lia.
  assert (Hmemhi : lo (sx w) <= hi ix2 <= hi (sx w)) by lia.
  (* ---- the four attainment goals ---- *)
  split; [ | split; [ | split ] ].
  - (* x-lo bound *)
    apply (Hfinish (lo ix2) Hmemlo). rewrite Hlox2.
    destruct (Z.max_spec (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz)))
      as [[Hcmp Heq]|[Hcmp Heq]]; rewrite Heq.
    + (* max = Xlo : realise the exact quotient extreme at a corner *)
      destruct (Xlo_corner (lo iy) (hi iy) (lo iz) (hi iz)) as [yc [zc [Hyc [Hzc Hdv]]]].
      exists yc, zc.
      destruct Hyc as [->| ->]; destruct Hzc as [->| ->];
        repeat split; try lia; try (symmetry; assumption).
    + (* max = lo ix1 : uniform witness via the two fden_opt corner points *)
      destruct Zlo as [xL [yL [HmxL [HmyL [HnzL HeqL]]]]].
      destruct Zhi as [xH [yH [HmxH [HmyH [HnzH HeqH]]]]].
      unfold mem in HmxL, HmyL, HmxH, HmyH.
      assert (HeqL' : xL = yL / lo iz) by (rewrite Hlz; exact HeqL).
      assert (HeqH' : xH = yH / hi iz) by (rewrite Hhz; exact HeqH).
      pose proof (div_in_range (lo iy) (hi iy) (lo iz) yL (conj (proj1 HmyL) (proj2 HmyL))) as DL.
      pose proof (div_in_range (lo iy) (hi iy) (hi iz) yH (conj (proj1 HmyH) (proj2 HmyH))) as DH.
      rewrite <- HeqL' in DL. rewrite <- HeqH' in DH.
      assert (Ua_l : lo ix1 <= Z.max (lo iy / lo iz) (hi iy / lo iz)) by lia.
      assert (Ua_h : lo ix1 <= Z.max (lo iy / hi iz) (hi iy / hi iz)) by lia.
      assert (Hspl : Z.min (lo iy / lo iz) (hi iy / lo iz) <= lo ix1
                     \/ Z.min (lo iy / hi iz) (hi iy / hi iz) <= lo ix1)
        by (unfold Xlo in Hcmp; lia).
      destruct Hspl as [Hs|Hs];
      [ destruct (div_1d (lo iy) (hi iy) (lo iz) (lo ix1) (proj1 Hiznz) Hy Hs Ua_l) as [y0 [Hy0 Hd0]];
        exists y0, (lo iz)
      | destruct (div_1d (lo iy) (hi iy) (hi iz) (lo ix1) (proj2 Hiznz) Hy Hs Ua_h) as [y0 [Hy0 Hd0]];
        exists y0, (hi iz) ];
      repeat split; try lia; symmetry; exact Hd0.
  - (* x-hi bound *)
    apply (Hfinish (hi ix2) Hmemhi). rewrite Hhix2.
    destruct (Z.min_spec (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)))
      as [[Hcmp Heq]|[Hcmp Heq]]; rewrite Heq.
    + (* min = hi ix1 : uniform witness via the two fden_opt corner points *)
      destruct Zlo as [xL [yL [HmxL [HmyL [HnzL HeqL]]]]].
      destruct Zhi as [xH [yH [HmxH [HmyH [HnzH HeqH]]]]].
      unfold mem in HmxL, HmyL, HmxH, HmyH.
      assert (HeqL' : xL = yL / lo iz) by (rewrite Hlz; exact HeqL).
      assert (HeqH' : xH = yH / hi iz) by (rewrite Hhz; exact HeqH).
      pose proof (div_in_range (lo iy) (hi iy) (lo iz) yL (conj (proj1 HmyL) (proj2 HmyL))) as DL.
      pose proof (div_in_range (lo iy) (hi iy) (hi iz) yH (conj (proj1 HmyH) (proj2 HmyH))) as DH.
      rewrite <- HeqL' in DL. rewrite <- HeqH' in DH.
      assert (La_l : Z.min (lo iy / lo iz) (hi iy / lo iz) <= hi ix1) by lia.
      assert (La_h : Z.min (lo iy / hi iz) (hi iy / hi iz) <= hi ix1) by lia.
      assert (Hspl : hi ix1 <= Z.max (lo iy / lo iz) (hi iy / lo iz)
                     \/ hi ix1 <= Z.max (lo iy / hi iz) (hi iy / hi iz))
        by (unfold Xhi in Hcmp; lia).
      destruct Hspl as [Hs|Hs];
      [ destruct (div_1d (lo iy) (hi iy) (lo iz) (hi ix1) (proj1 Hiznz) Hy La_l Hs) as [y0 [Hy0 Hd0]];
        exists y0, (lo iz)
      | destruct (div_1d (lo iy) (hi iy) (hi iz) (hi ix1) (proj2 Hiznz) Hy La_h Hs) as [y0 [Hy0 Hd0]];
        exists y0, (hi iz) ];
      repeat split; try lia; symmetry; exact Hd0.
    + (* min = Xhi : realise the exact quotient extreme at a corner *)
      destruct (Xhi_corner (lo iy) (hi iy) (lo iz) (hi iz)) as [yc [zc [Hyc [Hzc Hdv]]]].
      exists yc, zc.
      destruct Hyc as [->| ->]; destruct Hzc as [->| ->];
        repeat split; try lia; try (symmetry; assumption).
  - (* z-lo bound *)
    destruct Zlo as [x [y [Hmx [Hmy [Hnz Heq]]]]].
    exists x, y. unfold in_store, sol, mem in *; cbn [sx sy sz].
    fold iy iz0. rewrite Hlz. repeat split; try lia. exact Heq.
  - (* z-hi bound *)
    destruct Zhi as [x [y [Hmx [Hmy [Hnz Heq]]]]].
    exists x, y. unfold in_store, sol, mem in *; cbn [sx sy sz].
    fold iy iz0. rewrite Hhz. repeat split; try lia. exact Heq.
Qed.

(* Branch (x,z) optimality: on a sign-definite w, the x and z bounds of [fdivxz_pos w]
   land inside any t containing w's solutions. *)
Lemma branch_opt : forall w t,
  (0 < lo (sz w) \/ hi (sz w) < 0) ->
  contains_sols w t ->
  lo (sy w) <= hi (sy w) ->
  lo (sx (fdivxz_pos w)) <= hi (sx (fdivxz_pos w)) ->
  lo (sz (fdivxz_pos w)) <= hi (sz (fdivxz_pos w)) ->
  ile (sx (fdivxz_pos w)) (sx t) /\ ile (sz (fdivxz_pos w)) (sz t).
Proof.
  intros w t Hsign Ht Hy Hnx Hnz.
  destruct (branch_attain w Hsign Hy Hnx Hnz) as
    [[y1 [z1 [H1 S1]]] [[y2 [z2 [H2 S2]]] [[x3 [y3 [H3 S3]]] [x4 [y4 [H4 S4]]]]]].
  pose proof (Ht _ _ _ H1 S1) as T1. pose proof (Ht _ _ _ H2 S2) as T2.
  pose proof (Ht _ _ _ H3 S3) as T3. pose proof (Ht _ _ _ H4 S4) as T4.
  destruct T1 as (M1 & _ & _). destruct T2 as (M2 & _ & _).
  destruct T3 as (_ & _ & M3). destruct T4 as (_ & _ & M4).
  unfold ile, mem in *. split; split; lia.
Qed.

(* ---- small structural helpers for the assembly ---- *)
Lemma mem_inter_l : forall i j v, mem (inter i j) v -> mem i v.
Proof.
  intros i j v; unfold mem, inter; cbn [lo hi]; intro H.
  pose proof (Z.le_max_l (lo i) (lo j)). pose proof (Z.le_min_l (hi i) (hi j)). lia.
Qed.

Lemma Esy_fd : forall w, sy (fdivxz_pos w) = sy w.
Proof. intro w; unfold fdivxz_pos; cbv zeta; cbn [sy]; reflexivity. Qed.

Lemma ne_store_bounds : forall p, ne_store p = true ->
  lo (sx p) <= hi (sx p) /\ lo (sy p) <= hi (sy p) /\ lo (sz p) <= hi (sz p).
Proof.
  intros p H. unfold ne_store, nonemptyb in H.
  destruct (lo (sx p) <=? hi (sx p)) eqn:Ax; cbn in H; try discriminate.
  destruct (lo (sy p) <=? hi (sy p)) eqn:Ay; cbn in H; try discriminate.
  destruct (lo (sz p) <=? hi (sz p)) eqn:Az; cbn in H; try discriminate.
  apply Z.leb_le in Ax. apply Z.leb_le in Ay. apply Z.leb_le in Az. auto.
Qed.

Lemma bounds_ne_store : forall p,
  lo (sx p) <= hi (sx p) -> lo (sy p) <= hi (sy p) -> lo (sz p) <= hi (sz p) ->
  ne_store p = true.
Proof.
  intros p Hx Hy Hz. unfold ne_store, nonemptyb.
  destruct (lo (sx p) <=? hi (sx p)) eqn:Ax; [|apply Z.leb_gt in Ax; lia].
  destruct (lo (sy p) <=? hi (sy p)) eqn:Ay; [|apply Z.leb_gt in Ay; lia].
  destruct (lo (sz p) <=? hi (sz p)) eqn:Az; [|apply Z.leb_gt in Az; lia].
  reflexivity.
Qed.

(* THE optimality theorem: propagator s = alpha (gamma s cap Sol) (best transformer) *)
Lemma fdiv_best : forall s, optimal s.
Proof.
  intros s Hfeas t Ht.
  (* consistency of the output from a feasible witness *)
  destruct Hfeas as (wx & wy & wz & Hinw & Hsolw).
  assert (Hinp : in_store (propagator s) wx wy wz) by (apply prop_sound; assumption).
  assert (Hcp : consistent (propagator s)).
  { destruct Hinp as (Mx & My & Mz). unfold consistent, mem in *. repeat split; lia. }
  assert (Hsy_s : lo (sy s) <= hi (sy s)).
  { destruct Hinw as (_ & Hwy & _). unfold mem in Hwy. lia. }
  (* structural rewrites: propagator s = refine_y (sqcupbot (F rzn) (F rzp)) *)
  assert (EPS : propagator s = refine_y (sqcupbot (fdivxz_pos (restrict_z_neg s))
                                                  (fdivxz_pos (restrict_z_pos s)))).
  { unfold propagator. rewrite (fdivxz_neg_eq_pos (restrict_z_neg s)). reflexivity. }
  assert (ESX : sx (propagator s)
             = sx (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))).
  { rewrite EPS; unfold refine_y; cbn [sx]; reflexivity. }
  assert (ESZ : sz (propagator s)
             = sz (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))).
  { rewrite EPS; unfold refine_y; cbn [sz]; reflexivity. }
  (* sign-definiteness of the two restricted branches *)
  assert (HsignN : 0 < lo (sz (restrict_z_neg s)) \/ hi (sz (restrict_z_neg s)) < 0).
  { unfold restrict_z_neg; cbn [sz]; unfold inter; cbn [lo hi]; right.
    pose proof (Z.le_min_r (hi (sz s)) (-1)); lia. }
  assert (HsignP : 0 < lo (sz (restrict_z_pos s)) \/ hi (sz (restrict_z_pos s)) < 0).
  { unfold restrict_z_pos; cbn [sz]; unfold inter; cbn [lo hi]; left.
    pose proof (Z.le_max_r (lo (sz s)) 1); lia. }
  (* both restrictions preserve s's solutions, hence contain them in t *)
  assert (HtN : contains_sols (restrict_z_neg s) t).
  { intros vx vy vz Hin Hsol. destruct Hin as (Hx & Hy & Hz).
    unfold restrict_z_neg in Hx, Hy, Hz; cbn [sx sy sz] in Hx, Hy, Hz.
    apply Ht; [| exact Hsol].
    unfold in_store; split; [exact Hx | split; [exact Hy | exact (mem_inter_l _ _ _ Hz)]]. }
  assert (HtP : contains_sols (restrict_z_pos s) t).
  { intros vx vy vz Hin Hsol. destruct Hin as (Hx & Hy & Hz).
    unfold restrict_z_pos in Hx, Hy, Hz; cbn [sx sy sz] in Hx, Hy, Hz.
    apply Ht; [| exact Hsol].
    unfold in_store; split; [exact Hx | split; [exact Hy | exact (mem_inter_l _ _ _ Hz)]]. }
  assert (Esy_rzn : sy (restrict_z_neg s) = sy s) by (unfold restrict_z_neg; cbn [sy]; reflexivity).
  assert (Esy_rzp : sy (restrict_z_pos s) = sy s) by (unfold restrict_z_pos; cbn [sy]; reflexivity).
  (* per-branch (x,z) optimality via branch_opt, guarded by non-emptiness *)
  assert (BN : ne_store (fdivxz_pos (restrict_z_neg s)) = true ->
     ile (sx (fdivxz_pos (restrict_z_neg s))) (sx t)
     /\ ile (sz (fdivxz_pos (restrict_z_neg s))) (sz t)).
  { intro EN. destruct (ne_store_bounds _ EN) as (Bx & _ & Bz).
    apply (branch_opt (restrict_z_neg s) t HsignN HtN).
    - rewrite Esy_rzn; exact Hsy_s.
    - exact Bx.
    - exact Bz. }
  assert (BP : ne_store (fdivxz_pos (restrict_z_pos s)) = true ->
     ile (sx (fdivxz_pos (restrict_z_pos s))) (sx t)
     /\ ile (sz (fdivxz_pos (restrict_z_pos s))) (sz t)).
  { intro EP. destruct (ne_store_bounds _ EP) as (Bx & _ & Bz).
    apply (branch_opt (restrict_z_pos s) t HsignP HtP).
    - rewrite Esy_rzp; exact Hsy_s.
    - exact Bx.
    - exact Bz. }
  (* at least one branch is non-empty (else the consistent output would be empty) *)
  assert (Hone : ne_store (fdivxz_pos (restrict_z_neg s)) = true
               \/ ne_store (fdivxz_pos (restrict_z_pos s)) = true).
  { destruct (ne_store (fdivxz_pos (restrict_z_pos s))) eqn:EP; [right; reflexivity|].
    destruct (ne_store (fdivxz_pos (restrict_z_neg s))) eqn:EN; [left; reflexivity|].
    exfalso.
    assert (EX : sx (propagator s) = sx (fdivxz_pos (restrict_z_pos s))).
    { rewrite ESX; unfold sqcupbot; rewrite EN; reflexivity. }
    assert (EZ : sz (propagator s) = sz (fdivxz_pos (restrict_z_pos s))).
    { rewrite ESZ; unfold sqcupbot; rewrite EN; reflexivity. }
    destruct Hcp as (HCx & _ & HCz). rewrite EX in HCx. rewrite EZ in HCz.
    assert (Hsyp : lo (sy (fdivxz_pos (restrict_z_pos s)))
                 <= hi (sy (fdivxz_pos (restrict_z_pos s)))).
    { rewrite Esy_fd, Esy_rzp; exact Hsy_s. }
    pose proof (bounds_ne_store _ HCx Hsyp HCz) as Hne.
    rewrite Hne in EP; discriminate. }
  (* y-bounds attained by solutions of s, hence inside t *)
  destruct (y_attain s Hcp) as [[xl0 [zl0 [HinL HsolL]]] [xh0 [zh0 [HinH HsolH]]]].
  pose proof (Ht _ _ _ HinL HsolL) as TL.
  pose proof (Ht _ _ _ HinH HsolH) as TH.
  destruct TL as (_ & TLy & _). destruct TH as (_ & THy & _).
  unfold mem in TLy, THy.
  (* assemble the three components *)
  unfold sle. split; [| split].
  - (* x *)
    rewrite ESX; unfold sqcupbot.
    destruct (ne_store (fdivxz_pos (restrict_z_neg s))) eqn:EN;
    destruct (ne_store (fdivxz_pos (restrict_z_pos s))) eqn:EP.
    + cbn [sx sjoin]. apply ijoin_ile; [ exact (proj1 (BN eq_refl)) | exact (proj1 (BP eq_refl)) ].
    + exact (proj1 (BN eq_refl)).
    + exact (proj1 (BP eq_refl)).
    + destruct Hone as [H|H]; congruence.
  - (* y *) unfold ile. lia.
  - (* z *)
    rewrite ESZ; unfold sqcupbot.
    destruct (ne_store (fdivxz_pos (restrict_z_neg s))) eqn:EN;
    destruct (ne_store (fdivxz_pos (restrict_z_pos s))) eqn:EP.
    + cbn [sz sjoin]. apply ijoin_ile; [ exact (proj2 (BN eq_refl)) | exact (proj2 (BP eq_refl)) ].
    + exact (proj2 (BN eq_refl)).
    + exact (proj2 (BP eq_refl)).
    + destruct Hone as [H|H]; congruence.
Qed.

(* ================================================================= *)
(*  Closure-operator consequences of optimality.                     *)
(*  On feasible inputs the propagator equals  alpha o f o gamma  (the *)
(*  best abstract transformer, [fdiv_best]); being also sound         *)
(*  ([fdiv_soundness]) and reductive ([fdiv_reductive]) it is a lower *)
(*  closure operator, hence MONOTONE and IDEMPOTENT.  Both are derived *)
(*  here purely from those three facts -- no further interval         *)
(*  reasoning is needed.                                             *)
(* ================================================================= *)

Lemma mem_of_ile : forall i j v, ile i j -> mem i v -> mem j v.
Proof. unfold ile, mem; intros i j v [??] [??]; lia. Qed.

Lemma in_store_sle : forall s t vx vy vz,
  sle s t -> in_store s vx vy vz -> in_store t vx vy vz.
Proof.
  unfold sle, in_store; intros s t vx vy vz (Hx & Hy & Hz) (Mx & My & Mz).
  split; [| split]; eapply mem_of_ile; eassumption.
Qed.

(* Monotonicity: a tighter feasible input yields a tighter output. *)
Theorem fdiv_monotone : forall s t,
  feasible s -> sle s t -> sle (propagator s) (propagator t).
Proof.
  intros s t Hfeas Hle.
  apply (fdiv_best s Hfeas).
  intros vx vy vz Hin Hsol.
  apply fdiv_soundness; [ eapply in_store_sle; eassumption | exact Hsol ].
Qed.

(* Idempotence: re-propagating a feasible output changes nothing. *)
Theorem fdiv_idempotence : forall s,
  feasible s -> propagator (propagator s) = propagator s.
Proof.
  intros s Hfeas.
  apply sle_antisym.
  - apply fdiv_reductive.
  - apply (fdiv_best s Hfeas).
    intros vx vy vz Hin Hsol.
    apply fdiv_soundness; [ apply fdiv_soundness; [ exact Hin | exact Hsol ] | exact Hsol ].
Qed.
