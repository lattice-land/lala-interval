From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase.
From LalaInterval Require Import optbase2.
From LalaInterval Require idem.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Pure band lemmas: a z-corner whose numerator band contains Y       *)
(*  divides Y back into the x-interval [xl,xu].                         *)
(* ------------------------------------------------------------------ *)
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

(* ------------------------------------------------------------------ *)
(*  Endpoint corners: the numerator EXTREMES Ylo/Yhi are always        *)
(*  divided back into [a,b] by one of the two z-corners.  No fden      *)
(*  content is needed here -- an extreme is literally a band endpoint. *)
(* ------------------------------------------------------------------ *)
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

(* ------------------------------------------------------------------ *)
(*  The z-corners of a consistent output are non-zero.  Each corner of *)
(*  sz(propagator s) comes from a sign-definite branch (neg branch     *)
(*  z <= -1, pos branch z >= 1), so it can never be 0.                  *)
(* ------------------------------------------------------------------ *)
Lemma prop_z_nonzero : forall s,
  consistent (propagator s) ->
  lo (sz (propagator s)) <> 0 /\ hi (sz (propagator s)) <> 0.
Proof.
  intros s Hcons.
  assert (HZ : sz (propagator s) = sz (idem.J s))
    by (rewrite idem.propagator_J; unfold refine_y; cbn [sz]; reflexivity).
  unfold consistent in Hcons. destruct Hcons as [_ [_ Hzz]].
  (* bounds coming from the two sign-definite branches *)
  set (N := fdivxz_neg (restrict_z_neg s)) in *.
  set (P := fdivxz_pos (restrict_z_pos s)) in *.
  assert (HN : hi (sz N) <= -1).
  { unfold N, fdivxz_neg; cbv zeta; cbn [sz]. unfold restrict_z_neg; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  assert (HP : 1 <= lo (sz P)).
  { unfold P, fdivxz_pos; cbv zeta; cbn [sz]. unfold restrict_z_pos; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  assert (HJ : idem.J s = sqcupbot N P) by reflexivity.
  rewrite HZ, HJ in *.
  unfold sqcupbot in Hzz |- *.
  destruct (ne_store N) eqn:EN; destruct (ne_store P) eqn:EP; cbn iota in Hzz |- *.
  - (* both nonempty: sjoin *)
    unfold sjoin; cbn [sz]. unfold ijoin; cbn [lo hi].
    unfold ne_store in EN, EP.
    apply andb_prop in EN; destruct EN as [_ ENz].
    apply andb_prop in EP; destruct EP as [_ EPz].
    unfold nonemptyb in ENz, EPz. apply Z.leb_le in ENz, EPz.
    split.
    + pose proof (Z.le_min_l (lo (sz N)) (lo (sz P))). lia.
    + pose proof (Z.le_max_r (hi (sz N)) (hi (sz P))). lia.
  - (* only N *)
    unfold ne_store in EN. apply andb_prop in EN; destruct EN as [_ ENz].
    unfold nonemptyb in ENz. apply Z.leb_le in ENz. lia.
  - (* only P (ne_store N false) *)
    lia.
  - (* neither: sz = sz P, consistency forces nonempty sz *)
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(*  Corner coverage of the OUTPUT y-bounds (grid-validated true:        *)
(*  [y1d_grid] in yopt.v).  For each output y-bound Y there is a        *)
(*  non-zero z-corner of the refined output that divides Y back into    *)
(*  the refined x-interval.                                             *)
(*                                                                      *)
(*  Two sub-cases per bound (via [Z.max_spec]/[Z.min_spec]):            *)
(*   - the bound equals the numerator extreme Ylo/Yhi -> PROVED here    *)
(*     ([corner_Ylo]/[corner_Yhi]): an extreme is literally a band      *)
(*     endpoint, needs no [fden] content.                               *)
(*   - the bound equals the INPUT y-bound (the meet kept the looser     *)
(*     numerator window) -> the two [admit]s below.  This is the OPEN   *)
(*     CRUX (= the [y_attain]/[Jexp_*] lemmas Admitted in optdev.v /    *)
(*     idem.v).  It is FALSE from [Ylo<=Y<=Yhi] alone (machine          *)
(*     counterexample: a=b=100, zl=1, zu=2, Y=150: Ylo=100, Yhi=201,    *)
(*     but 150/1=150 and 150/2=75 are both outside [100,100]); it holds *)
(*     only because the [fden] refinement of z excludes such           *)
(*     configurations on a consistent output.  Discharging it needs the *)
(*     per-sign-class [fden] coverage argument together with the branch *)
(*     join -- the open completeness content of the development.        *)
(* ------------------------------------------------------------------ *)
Lemma y_coverage : forall s,
  consistent (propagator s) ->
  (exists zc, (zc = lo (sz (propagator s)) \/ zc = hi (sz (propagator s))) /\ zc <> 0 /\
     lo (sx (propagator s)) <= lo (sy (propagator s)) / zc <= hi (sx (propagator s))) /\
  (exists zc, (zc = lo (sz (propagator s)) \/ zc = hi (sz (propagator s))) /\ zc <> 0 /\
     lo (sx (propagator s)) <= hi (sy (propagator s)) / zc <= hi (sx (propagator s))).
Proof.
  intros s Hcons.
  set (p := propagator s) in *.
  assert (HpJ : p = refine_y (idem.J s)) by (apply idem.propagator_J).
  set (a := lo (sx p)) in *. set (b := hi (sx p)) in *.
  set (zl := lo (sz p)) in *. set (zu := hi (sz p)) in *.
  assert (HXj : sx (idem.J s) = sx p) by (rewrite HpJ; unfold refine_y; cbn [sx]; reflexivity).
  assert (HZj : sz (idem.J s) = sz p) by (rewrite HpJ; unfold refine_y; cbn [sz]; reflexivity).
  assert (HYlo : lo (sy p) = Z.max (lo (sy s)) (Ylo a b zl zu)).
  { rewrite HpJ at 1. unfold refine_y; cbn [sy]. unfold inter; cbn [lo hi].
    rewrite idem.J_sy. rewrite HXj, HZj. reflexivity. }
  assert (HYhi : hi (sy p) = Z.min (hi (sy s)) (Yhi a b zl zu)).
  { rewrite HpJ at 1. unfold refine_y; cbn [sy]. unfold inter; cbn [lo hi].
    rewrite idem.J_sy. rewrite HXj, HZj. reflexivity. }
  assert (Hcons' := Hcons). unfold consistent in Hcons'.
  destruct Hcons' as [Hab [Hyy Hzz]]. fold p in Hab, Hyy, Hzz.
  fold a b in Hab. fold zl zu in Hzz.
  destruct (prop_z_nonzero s Hcons) as [Hzln Hzun]. fold p in Hzln, Hzun.
  fold zl in Hzln. fold zu in Hzun.
  split.
  - rewrite HYlo. destruct (Z.max_spec (lo (sy s)) (Ylo a b zl zu)) as [[_ E]|[_ E]]; rewrite E.
    + apply corner_Ylo; assumption.
    + (* OPEN CRUX: output lower bound = input lower bound lo (sy s) *)
      admit.
  - rewrite HYhi. destruct (Z.min_spec (hi (sy s)) (Yhi a b zl zu)) as [[_ E]|[_ E]]; rewrite E.
    + (* OPEN CRUX: output upper bound = input upper bound hi (sy s) *)
      admit.
    + apply corner_Yhi; assumption.
Admitted.

Lemma y_attain : forall s, consistent (propagator s) ->
  (exists x z, in_store s x (lo (sy (propagator s))) z /\ sol x (lo (sy (propagator s))) z) /\
  (exists x z, in_store s x (hi (sy (propagator s))) z /\ sol x (hi (sy (propagator s))) z).
Proof.
  intros s Hcons.
  set (p := propagator s) in *.
  pose proof (propagator_reductive s) as Hred.
  unfold sle in Hred. destruct Hred as [Rx [Ry Rz]].
  unfold ile in Rx, Ry, Rz. fold p in Rx, Ry, Rz.
  assert (Hcons' := Hcons). unfold consistent in Hcons'.
  destruct Hcons' as [Hab [Hyy Hzz]]. fold p in Hab, Hyy, Hzz.
  destruct (y_coverage s Hcons) as [Cov_lo Cov_hi]. fold p in Cov_lo, Cov_hi.
  (* membership plumbing: a corner (zc<>0, in x-range) gives an in-store solution. *)
  assert (Hcore : forall Y, lo (sy p) <= Y -> Y <= hi (sy p) ->
     (exists zc, (zc = lo (sz p) \/ zc = hi (sz p)) /\ zc <> 0 /\
        lo (sx p) <= Y / zc <= hi (sx p)) ->
     exists x z, in_store s x Y z /\ sol x Y z).
  { intros Y HYl HYh [zc [Hzc [Hznz [Hxa Hxb]]]].
    exists (Y / zc), zc. split.
    - unfold in_store, mem. repeat split.
      + destruct Rx as [Rx1 Rx2]. lia.
      + destruct Rx as [Rx1 Rx2]. lia.
      + destruct Ry as [Ry1 Ry2]. lia.
      + destruct Ry as [Ry1 Ry2]. lia.
      + destruct Rz as [Rz1 Rz2]. destruct Hzc; subst zc; lia.
      + destruct Rz as [Rz1 Rz2]. destruct Hzc; subst zc; lia.
    - unfold sol. split; [exact Hznz | reflexivity]. }
  split.
  - apply Hcore; [ lia | lia | exact Cov_lo ].
  - apply Hcore; [ lia | lia | exact Cov_hi ].
Qed.
