(** * Soundness of the floored-division interval propagator

    Rocq formalisation of the soundness proof for
        x = fdiv(y,z)  =  x = floor(y/z),  z <> 0
    over the integer interval abstract domain.

    Floored division (rounding towards -infinity) is exactly [Z.div] in Rocq,
    so a "solution" is a triple (x,y,z) with [z <> 0] and [x = Z.div y z].

    We machine-check the whole proof:
      - Lemma 1  (floor bracketing)          : [div_bracket_pos] / [div_bracket_neg]
      - Lemma 2  (fdiv, quotient enclosure)   : [fdiv_sound_pos] / [fdiv_sound_neg]
      - Lemma 3  (fnum, numerator enclosure)  : [fnum_sound]
      - Lemma 4  (fden, divisor table sound)  : [fden_sound]  (all 14 rows of Table 2)
    and then assemble the structural argument (split on the sign of z,
    store-level join, numerator refinement) into the main soundness theorem
    [fdiv_propagator_sound].

    The full 14-row denominator table [fden] is defined concretely and its
    soundness [fden_sound] is proved by exhaustive sign-class case analysis
    (each column split on the sign of z, closed with the [cdiv]/[fdiv] bound
    lemmas + [nia]).  Everything is proved by [Qed]: both [fden_sound] and
    [fdiv_propagator_sound] are "Closed under the global context" -- ZERO
    axioms.  Verify with [Print Assumptions fdiv_propagator_sound.]. *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Intervals and membership                                        *)
(* ------------------------------------------------------------------ *)

(** A (finite) interval is a pair of bounds; we work with finite bounds,
    which is what the top-level infinite-bound guard secures. *)
Record itv := Itv { lo : Z ; hi : Z }.

Definition mem (i : itv) (v : Z) : Prop := lo i <= v <= hi i.

Definition nonempty (i : itv) : Prop := lo i <= hi i.

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
(** ** Lemma 4 : fden, representative row  P1 x P                       *)
(*                                                                     *)
(*  x in [a,b] with a >= 1 (class P1), y in [c,d] with c >= 0 < d      *)
(*  (class P).  Then z lies in                                         *)
(*    [ floor(max(1,c)/(b+1)) + 1 , floor(d/a) ].                       *)
(* ------------------------------------------------------------------ *)

Lemma fden_P1_P : forall x y z a b c d,
  1 <= a -> a <= x <= b ->
  0 <= c -> 0 < d -> c <= y <= d ->
  sol x y z ->
  (Z.max 1 c) / (b+1) + 1 <= z <= d / a.
Proof.
  intros x y z a b c d Ha [Hxa Hxb] Hc Hd [Hyc Hyd] [Hz Hxeq]. subst x.
  remember (y / z) as q eqn:Hq.
  assert (Hq1 : 1 <= q) by lia.                (* from 1 <= a <= q *)
  assert (Hy0 : 0 <= y) by lia.                (* from 0 <= c <= y *)
  assert (Hy1 : 1 <= y).
  { destruct (Z.eq_dec y 0) as [Hy|Hy].
    - subst y. rewrite Z.div_0_l in Hq by lia. lia.
    - lia. }
  assert (Hzpos : 0 < z).
  { destruct (Z.lt_trichotomy z 0) as [Hzc|[Hzc|Hzc]]; [ | lia | lia ].
    exfalso.
    destruct (div_bracket_neg y z Hzc) as [_ Hupn].   (* y <= z * (y/z) = z*q *)
    rewrite <- Hq in Hupn. nia. }
  destruct (div_bracket_pos y z Hzpos) as [Hlo Hup].
  rewrite <- Hq in Hlo, Hup.                    (* Hlo: z*q <= y ; Hup: y <= z*(q+1)-1 *)
  split.
  - assert (Hlt : y < (q+1) * z) by nia.
    assert (Hdiv : y / (q+1) < z) by (apply Z.div_lt_upper_bound; [lia| nia]).
    assert (Hchain : Z.max 1 c / (b+1) <= y / (q+1)).
    { apply Z.le_trans with (y / (b+1)).
      - apply Z.div_le_mono; [lia | apply Z.max_lub; lia].
      - apply Z.div_le_compat_l; [lia | lia]. }
    lia.
  - assert (Hazd : a * z <= d) by nia.
    apply Z.div_le_lower_bound; [lia | nia].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Structural: store-level join preserves witnesses                *)
(* ------------------------------------------------------------------ *)

Record store := St { sx : itv ; sy : itv ; sz : itv }.

Definition in_store (s : store) (vx vy vz : Z) : Prop :=
  mem (sx s) vx /\ mem (sy s) vy /\ mem (sz s) vz.

Definition nonemptyb (i : itv) : bool := Z.leb (lo i) (hi i).
Definition ne_store (s : store) : bool :=
  (nonemptyb (sx s) && nonemptyb (sy s) && nonemptyb (sz s))%bool.

Lemma nonemptyb_true : forall i v, mem i v -> nonemptyb i = true.
Proof. intros i v Hm. unfold nonemptyb. apply Z.leb_le. unfold mem in Hm. lia. Qed.

Lemma ne_store_true : forall s vx vy vz, in_store s vx vy vz -> ne_store s = true.
Proof.
  intros s vx vy vz (Hx & Hy & Hz); unfold ne_store.
  rewrite (nonemptyb_true _ _ Hx), (nonemptyb_true _ _ Hy), (nonemptyb_true _ _ Hz).
  reflexivity.
Qed.

Definition ijoin (i j : itv) : itv :=
  Itv (Z.min (lo i) (lo j)) (Z.max (hi i) (hi j)).
Definition sjoin (s t : store) : store :=
  St (ijoin (sx s) (sx t)) (ijoin (sy s) (sy t)) (ijoin (sz s) (sz t)).

Definition sqcupbot (s t : store) : store :=
  if ne_store s
  then (if ne_store t then sjoin s t else s)
  else t.

Lemma in_store_ijoin_l : forall i j v, mem i v -> mem (ijoin i j) v.
Proof. intros i j v Hm. unfold mem, ijoin in *; simpl in *. lia. Qed.
Lemma in_store_ijoin_r : forall i j v, mem j v -> mem (ijoin i j) v.
Proof. intros i j v Hm. unfold mem, ijoin in *; simpl in *. lia. Qed.

Lemma sqcupbot_pres_l : forall s t vx vy vz,
  in_store s vx vy vz -> in_store (sqcupbot s t) vx vy vz.
Proof.
  intros s t vx vy vz Hs.
  unfold sqcupbot.
  rewrite (ne_store_true _ _ _ _ Hs).
  destruct (ne_store t) eqn:Et.
  - destruct Hs as (Hx & Hy & Hz).
    repeat split; simpl; apply in_store_ijoin_l; assumption.
  - exact Hs.
Qed.

Lemma sqcupbot_pres_r : forall s t vx vy vz,
  in_store t vx vy vz -> in_store (sqcupbot s t) vx vy vz.
Proof.
  intros s t vx vy vz Ht.
  unfold sqcupbot.
  rewrite (ne_store_true _ _ _ _ Ht).
  destruct (ne_store s) eqn:Es; simpl.
  - destruct Ht as (Hx & Hy & Hz).
    repeat split; simpl; apply in_store_ijoin_r; assumption.
  - exact Ht.
Qed.

(* ------------------------------------------------------------------ *)
(** ** fden generic table (assumed) and its soundness                  *)
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

(** The denominator table of the paper (Table 2), implemented concretely by
    meeting the finite table bounds into the incoming z-interval [iz] — exactly
    the one-sided [z.l.meet]/[z.u.meet] of the reference C++ [zfdiv_fast3] DEN.
    Rows with an infinite side simply leave that side of [iz] untouched, which
    is how the finite integer model represents the paper's +/-oo entries.
    [a,b] = x-interval bounds, [c,d] = y, [zl,zu] = z_in. *)
Definition fden (ix iy iz : itv) : itv :=
  let a := lo ix in let b := hi ix in
  let c := lo iy in let d := hi iy in
  let zl := lo iz in let zu := hi iz in
  if ((a <=? 0) && (0 <=? b) && (c <=? 0) && (0 <=? d))%bool then iz   (* M0 x M0 *)
  else if (0 <? a) then                                                (* P1 *)
    if ((0 <=? c) && (0 <? d))%bool then                               (* P *)
      Itv (Z.max zl ((Z.max 1 c) / (b+1) + 1)) (Z.min zu (d / a))
    else if ((d <? 0) && (c <=? 0))%bool then                          (* N *)
      Itv (Z.max zl (cdiv c a)) (Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1))
    else                                                               (* M/Z *)
      Itv (Z.max zl (cdiv c a)) (Z.min zu (d / a))
  else if (b <? -1) then                                              (* N'1 *)
    if ((0 <=? c) && (0 <? d))%bool then                               (* P *)
      Itv (Z.max zl (d / (b+1) + 1)) (Z.min zu (c / a))
    else if ((c <? 0) && (d <=? 0))%bool then                          (* N *)
      Itv (Z.max zl (cdiv d a)) (Z.min zu (cdiv c (b+1) - 1))
    else                                                               (* M/Z *)
      Itv (Z.max zl (d / (b+1) + 1)) (Z.min zu (cdiv c (b+1) - 1))
  else if ((a =? 0) && (b =? 0))%bool then                            (* Z : x=[0,0] *)
    if (d <? 0) then Itv zl (Z.min zu (d - 1))
    else Itv (Z.max zl (c + 1)) zu
  else if ((a <=? -1) && (b =? -1))%bool then                         (* N'0, O *)
    if ((c <? 0) && (d <=? 0))%bool then Itv (Z.max zl (cdiv (Z.min (-1) d) a)) zu
    else if ((0 <? d) && (0 <=? c))%bool then Itv zl (Z.min zu ((Z.max 1 c) / a))
    else if ((c =? 0) && (d =? 0))%bool then Itv 1 0                   (* bottom *)
    else iz                                                            (* M *)
  else if ((a =? 0) && (0 <? b))%bool then                            (* P0 *)
    if ((c <? 0) && (d <=? 0))%bool then Itv zl (Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1))
    else if ((0 <? d) && (0 <=? c))%bool then Itv (Z.max zl ((Z.max 1 c) / (b+1) + 1)) zu
    else iz
  else iz.

(** Soundness of the table. *)
Lemma fden_sound : forall x y z ix iy iz,
  mem ix x -> mem iy y -> mem iz z -> sol x y z -> mem (fden ix iy iz) z.
Proof.
  intros x y z ix iy iz Hx Hy Hz [Hz0 Hxeq].
  unfold mem in *. unfold fden; cbv zeta.
  set (a := lo ix) in *. set (b := hi ix) in *.
  set (c := lo iy) in *. set (d := hi iy) in *.
  destruct Hx as [Hax Hxb]. destruct Hy as [Hcy Hyd]. destruct Hz as [Hzlz Hzzu].
  (* multiplicative bracket for x = y/z, one per sign of z *)
  assert (Bpos : 0 < z -> z * x <= y /\ y <= z * (x + 1) - 1).
  { intro Hp. destruct (div_bracket_pos y z Hp) as [P1 P2].
    rewrite <- Hxeq in P1, P2. lia. }
  assert (Bneg : z < 0 -> z * (x + 1) + 1 <= y /\ y <= z * x).
  { intro Hn. destruct (div_bracket_neg y z Hn) as [N1 N2].
    rewrite <- Hxeq in N1, N2. lia. }
  (* split every table branch, pruning dead ones *)
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end;
          cbn iota).
  (* decode the surviving boolean guards into arithmetic facts *)
  all: repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    end.
  all: cbn [lo hi].
  all: try lia.
  (* --- P1 x P --- *)
  - assert (HP : Z.max 1 c / (b + 1) + 1 <= z <= d / a).
    { apply (fden_P1_P x y z a b c d);
      [ lia | split; [exact Hax|exact Hxb] | lia | lia
      | split; [exact Hcy|exact Hyd] | split; [exact Hz0|exact Hxeq] ]. }
    split; [ apply Z.max_lub; [exact Hzlz| lia] | apply Z.min_glb; [exact Hzzu| lia] ].
  (* --- P1 x N --- *)
  - assert (Hzn : z < 0).
    { destruct (Z.lt_trichotomy z 0) as [?|[?|Hzp]]; [assumption|lia|].
      exfalso. destruct (Bpos Hzp) as [B1 B2]. nia. }
    destruct (Bneg Hzn) as [N1 N2].
    split.
    + apply Z.max_lub; [exact Hzlz|]. apply cdiv_ub; [lia| nia].
    + apply Z.min_glb; [exact Hzzu|].
      assert (z + 1 <= cdiv (Z.min (-1) d) (b + 1)).
      { apply cdiv_lb; [lia|]. replace (Z.min (-1) d) with d by lia. nia. }
      lia.
  (* --- P1 x M/Z --- *)
  - assert (Hd0 : 0 <= d).
    { destruct (Z_lt_le_dec d 0) as [Hdl|]; [exfalso|lia].
      assert (((d <? 0) && (c <=? 0))%bool = true)
        by (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia).
      congruence. }
    assert (Hc0 : c <= 0).
    { destruct (Z_lt_le_dec 0 d) as [Hd|Hd]; [|lia].
      destruct (Z_lt_le_dec 0 c) as [Hc|]; [exfalso|lia].
      assert (((0 <=? c) && (0 <? d))%bool = true)
        by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      congruence. }
    split.
    + apply Z.max_lub; [exact Hzlz|].
      destruct (Z.lt_trichotomy z 0) as [Hzn|[|Hzp]]; [|lia|].
      * destruct (Bneg Hzn) as [N1 N2]. apply cdiv_ub; [lia|nia].
      * assert (cdiv c a <= 0) by (apply cdiv_ub; [lia|nia]). lia.
    + apply Z.min_glb; [exact Hzzu|].
      destruct (Z.lt_trichotomy z 0) as [Hzn|[|Hzp]]; [|lia|].
      * assert (0 <= d / a) by (apply Z.div_pos; lia). lia.
      * destruct (Bpos Hzp) as [B1 B2]. apply Z.div_le_lower_bound; [lia|nia].
  (* --- N'1 x P --- *)
  - assert (Hzn : z < 0).
    { destruct (Z.lt_trichotomy z 0) as [?|[?|Hzp]]; [assumption|lia|].
      exfalso. destruct (Bpos Hzp) as [B1 B2]. nia. }
    destruct (Bneg Hzn) as [N1 N2].
    split.
    + apply Z.max_lub; [exact Hzlz|].
      assert (d / (b + 1) < z) by (apply fdiv_lt_neg; [lia|nia]). lia.
    + apply Z.min_glb; [exact Hzzu|]. apply fdiv_lb_neg; [lia|nia].
  (* --- N'1 x N --- *)
  - assert (Hzp : 0 < z).
    { destruct (Z.lt_trichotomy z 0) as [Hzn|[|]]; [exfalso|lia|assumption].
      destruct (Bneg Hzn) as [N1 N2]. nia. }
    destruct (Bpos Hzp) as [B1 B2].
    split.
    + apply Z.max_lub; [exact Hzlz|]. apply cdiv_ub_neg; [lia|nia].
    + apply Z.min_glb; [exact Hzzu|].
      assert (z + 1 <= cdiv c (b + 1)) by (apply cdiv_lb_neg; [lia|nia]). lia.
  (* --- N'1 x M/Z --- *)
  - assert (Hc0 : c < 0).
    { destruct (Z_lt_le_dec c 0) as [|Hc]; [lia|exfalso].
      assert (d <= 0).
      { destruct (Z_lt_le_dec 0 d) as [Hd|]; [exfalso|lia].
        assert (((0 <=? c) && (0 <? d))%bool = true)
          by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        congruence. }
      assert (y = 0) by lia. subst y. rewrite Z.div_0_l in Hxeq by lia. lia. }
    assert (Hd0 : 0 < d).
    { destruct (Z_lt_le_dec 0 d) as [|Hd]; [lia|exfalso].
      assert (((c <? 0) && (d <=? 0))%bool = true)
        by (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia).
      congruence. }
    split.
    + apply Z.max_lub; [exact Hzlz|].
      assert (d / (b + 1) < z).
      { apply fdiv_lt_neg; [lia|].
        destruct (Z.lt_trichotomy z 0) as [Hzn|[|Hzp]]; [|lia|].
        - destruct (Bneg Hzn) as [N1 N2]. nia.
        - nia. }
      lia.
    + apply Z.min_glb; [exact Hzzu|].
      assert (z + 1 <= cdiv c (b + 1)).
      { apply cdiv_lb_neg; [lia|].
        destruct (Z.lt_trichotomy z 0) as [Hzn|[|Hzp]]; [|lia|].
        - nia.
        - destruct (Bpos Hzp) as [B1 B2]. nia. }
      lia.
  (* --- N'0,O x N --- *)
  - assert (Hzp : 0 < z).
    { destruct (Z.lt_trichotomy z 0) as [Hzn|[|]]; [exfalso|lia|assumption].
      destruct (Bneg Hzn) as [N1 N2]. nia. }
    destruct (Bpos Hzp) as [B1 B2].
    split.
    + apply Z.max_lub; [exact Hzlz|]. apply cdiv_ub_neg; [lia|].
      apply Z.min_glb; nia.
    + exact Hzzu.
  (* --- N'0,O x P --- *)
  - assert (Hzn : z < 0).
    { destruct (Z.lt_trichotomy z 0) as [|[|Hzp]]; [assumption|lia|exfalso].
      destruct (Bpos Hzp) as [B1 B2]. nia. }
    assert (Hy1 : 1 <= y).
    { destruct (Z_lt_le_dec 0 y) as [|Hy]; [lia|].
      assert (y = 0) by lia. subst y. rewrite Z.div_0_l in Hxeq by lia. lia. }
    destruct (Bneg Hzn) as [N1 N2].
    split; [exact Hzlz|].
    apply Z.min_glb; [exact Hzzu|]. apply fdiv_lb_neg; [lia|].
    assert (Z.max 1 c <= y) by (apply Z.max_lub; lia). nia.
  (* --- N'0,O x Z  (bottom) --- *)
  - assert (y = 0) by lia. subst y. rewrite Z.div_0_l in Hxeq by lia. lia.
  (* --- P0 x N --- *)
  - assert (Hd : d < 0).
    { destruct (Z_lt_le_dec d 0) as [|Hd]; [lia|exfalso].
      assert (((a <=? 0) && (0 <=? b) && (c <=? 0) && (0 <=? d))%bool = true)
        by (apply andb_true_intro; split;
            [ apply andb_true_intro; split;
              [ apply andb_true_intro; split; apply Z.leb_le; lia
              | apply Z.leb_le; lia ]
            | apply Z.leb_le; lia ]).
      congruence. }
    assert (Hzn : z < 0).
    { destruct (Z.lt_trichotomy z 0) as [|[|Hzp]]; [assumption|lia|exfalso].
      destruct (Bpos Hzp) as [B1 B2]. nia. }
    destruct (Bneg Hzn) as [N1 N2].
    split; [exact Hzlz|].
    apply Z.min_glb; [exact Hzzu|].
    assert (z + 1 <= cdiv (Z.min (-1) d) (b + 1)).
    { apply cdiv_lb; [lia|]. replace (Z.min (-1) d) with d by lia. nia. }
    lia.
  (* --- P0 x P --- *)
  - assert (Hc : 0 < c).
    { destruct (Z_lt_le_dec 0 c) as [|Hc]; [lia|exfalso].
      assert (((a <=? 0) && (0 <=? b) && (c <=? 0) && (0 <=? d))%bool = true)
        by (apply andb_true_intro; split;
            [ apply andb_true_intro; split;
              [ apply andb_true_intro; split; apply Z.leb_le; lia
              | apply Z.leb_le; lia ]
            | apply Z.leb_le; lia ]).
      congruence. }
    assert (Hzp : 0 < z).
    { destruct (Z.lt_trichotomy z 0) as [Hzn|[|]]; [exfalso|lia|assumption].
      destruct (Bneg Hzn) as [N1 N2]. nia. }
    destruct (Bpos Hzp) as [B1 B2].
    split; [|exact Hzzu].
    apply Z.max_lub; [exact Hzlz|].
    assert (Z.max 1 c / (b + 1) < z).
    { apply Z.div_lt_upper_bound; [lia|].
      assert (Z.max 1 c <= y) by (apply Z.max_lub; lia). nia. }
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** One propagation branch (sign-definite divisor)                  *)
(* ------------------------------------------------------------------ *)

Definition inter (i j : itv) : itv := Itv (Z.max (lo i) (lo j)) (Z.min (hi i) (hi j)).
Lemma mem_inter : forall i j v, mem i v -> mem j v -> mem (inter i j) v.
Proof. intros i j v Hi Hj. unfold mem, inter in *; simpl in *. lia. Qed.

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

Theorem fdiv_propagator_sound : forall s vx vy vz,
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
