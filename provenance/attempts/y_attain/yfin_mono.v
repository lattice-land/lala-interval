From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase.
From LalaInterval Require Import optbase2.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

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
  pose proof (propagator_reductive s) as Hred.
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
  pose proof (propagator_reductive s) as Hred. unfold sle, ile in Hred.
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
