From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase.
From LalaInterval Require Import optbase2.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ================================================================= *)
(*  Pure band lemmas (copied from ya_a.v / ya_b.v; fdiv only).        *)
(* ================================================================= *)

Lemma num_in_band_pos : forall a b z Y,
  0 < z -> a * z <= Y -> Y <= (b+1)*z - 1 -> a <= Y / z <= b.
Proof.
  intros a b z Y Hz Hlo Hhi. split.
  - apply Z.div_le_lower_bound; [lia | nia].
  - assert (Y / z < b + 1) by (apply Z.div_lt_upper_bound; [lia | nia]). lia.
Qed.

Lemma num_in_band_neg : forall a b z Y,
  z < 0 -> (b+1)*z + 1 <= Y -> Y <= a * z -> a <= Y / z <= b.
Proof.
  intros a b z Y Hz Hlo Hhi. split.
  - apply fdiv_lb_neg; [lia | nia].
  - assert (Y / z < b + 1) by (apply fdiv_lt_neg; [lia | nia]). lia.
Qed.

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
      * apply num_in_band_pos; [lia | apply L1; lia | lia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | apply L4; lia | nia].
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply num_in_band_pos; [lia | apply L2; lia | lia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | apply L3; lia | nia].
  - destruct (Z.max_spec (a*zl) (a*zu)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply num_in_band_pos; [lia | apply L1; lia | nia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | apply L4; lia | lia].
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply num_in_band_pos; [lia | apply L2; lia | nia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | apply L3; lia | lia].
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
      * apply num_in_band_pos; [lia | lia | apply U2; lia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | nia | apply U3; lia].
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply num_in_band_pos; [lia | lia | apply U1; lia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | nia | apply U4; lia].
  - destruct (Z.min_spec ((b+1)*zl+1) ((b+1)*zu+1)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply num_in_band_pos; [lia | nia | apply U2; lia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | lia | apply U3; lia].
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply num_in_band_pos; [lia | nia | apply U1; lia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | lia | apply U4; lia].
Qed.

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

(* ================================================================= *)
(*  Structural lemmas copied from optdev.v (fdiv/optbase only).       *)
(* ================================================================= *)

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

Lemma fden_bounds : forall ix iy iz,
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  lo iz <= lo (fden ix iy iz) /\ hi (fden ix iy iz) <= hi iz.
Proof.
  intros ix iy iz.
  unfold fden; cbv zeta.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end;
          cbn iota).
  all: cbn [lo hi]; lia.
Qed.

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

Lemma fdivxz_neg_eq_pos : forall w, fdivxz_neg w = fdivxz_pos w.
Proof. reflexivity. Qed.

Lemma Esy_fd : forall w, sy (fdivxz_pos w) = sy w.
Proof. intro w; unfold fdivxz_pos; cbv zeta; cbn [sy]; reflexivity. Qed.

(* ================================================================= *)
(*  branch_attain (copied from optdev.v; fdiv/optbase only).          *)
(* ================================================================= *)

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
  split; [ | split; [ | split ] ].
  - apply (Hfinish (lo ix2) Hmemlo). rewrite Hlox2.
    destruct (Z.max_spec (lo ix1) (Xlo (lo iy) (hi iy) (lo iz) (hi iz)))
      as [[Hcmp Heq]|[Hcmp Heq]]; rewrite Heq.
    + destruct (Xlo_corner (lo iy) (hi iy) (lo iz) (hi iz)) as [yc [zc [Hyc [Hzc Hdv]]]].
      exists yc, zc.
      destruct Hyc as [->| ->]; destruct Hzc as [->| ->];
        repeat split; try lia; try (symmetry; assumption).
    + destruct Zlo as [xL [yL [HmxL [HmyL [HnzL HeqL]]]]].
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
  - apply (Hfinish (hi ix2) Hmemhi). rewrite Hhix2.
    destruct (Z.min_spec (hi ix1) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)))
      as [[Hcmp Heq]|[Hcmp Heq]]; rewrite Heq.
    + destruct Zlo as [xL [yL [HmxL [HmyL [HnzL HeqL]]]]].
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
    + destruct (Xhi_corner (lo iy) (hi iy) (lo iz) (hi iz)) as [yc [zc [Hyc [Hzc Hdv]]]].
      exists yc, zc.
      destruct Hyc as [->| ->]; destruct Hzc as [->| ->];
        repeat split; try lia; try (symmetry; assumption).
  - destruct Zlo as [x [y [Hmx [Hmy [Hnz Heq]]]]].
    exists x, y. unfold in_store, sol, mem in *; cbn [sx sy sz].
    fold iy iz0. rewrite Hlz. repeat split; try lia. exact Heq.
  - destruct Zhi as [x [y [Hmx [Hmy [Hnz Heq]]]]].
    exists x, y. unfold in_store, sol, mem in *; cbn [sx sy sz].
    fold iy iz0. rewrite Hhz. repeat split; try lia. exact Heq.
Qed.

(* ================================================================= *)
(*  BLU_branch : branch-level band conditions.                        *)
(* ================================================================= *)

Lemma BLU_branch : forall w,
  (0 < lo (sz w) \/ hi (sz w) < 0) ->
  lo (sx (fdivxz_pos w)) <= hi (sx (fdivxz_pos w)) ->
  lo (sy w) <= hi (sy w) ->
  lo (sz (fdivxz_pos w)) <= hi (sz (fdivxz_pos w)) ->
  let a := lo (sx (fdivxz_pos w)) in let b := hi (sx (fdivxz_pos w)) in
  let zl := lo (sz (fdivxz_pos w)) in let zu := hi (sz (fdivxz_pos w)) in
  let c := lo (sy w) in let d := hi (sy w) in
  (0 < zu -> a*zu <= d) /\ (0 < zl -> a*zl <= d) /\
  (zl < 0 -> (b+1)*zl+1 <= d) /\ (zu < 0 -> (b+1)*zu+1 <= d) /\
  (0 < zu -> c <= (b+1)*zu-1) /\ (0 < zl -> c <= (b+1)*zl-1) /\
  (zl < 0 -> c <= a*zl) /\ (zu < 0 -> c <= a*zu).
Proof.
  intros w Hsign Hxne Hy Hzne. cbv zeta.
  destruct (branch_attain w Hsign Hy Hxne Hzne) as
    [_ [_ [[xC [yC [HinC HsolC]]] [xD [yD [HinD HsolD]]]]]].
  assert (Hlzge : lo (sz w) <= lo (sz (fdivxz_pos w))).
  { unfold fdivxz_pos; cbv zeta; cbn [sz]; unfold inter; cbn [lo hi]. apply Z.le_max_l. }
  assert (Hhzle : hi (sz (fdivxz_pos w)) <= hi (sz w)).
  { unfold fdivxz_pos; cbv zeta; cbn [sz]; unfold inter; cbn [lo hi]. apply Z.le_min_l. }
  set (a := lo (sx (fdivxz_pos w))) in *.
  set (b := hi (sx (fdivxz_pos w))) in *.
  set (zl := lo (sz (fdivxz_pos w))) in *.
  set (zu := hi (sz (fdivxz_pos w))) in *.
  set (c := lo (sy w)) in *.
  set (d := hi (sy w)) in *.
  assert (HmemyC : c <= yC <= d) by (destruct HinC as (_&M&_); exact M).
  assert (HmemyD : c <= yD <= d) by (destruct HinD as (_&M&_); exact M).
  assert (HeqC : xC = yC / zl) by (apply HsolC).
  assert (HeqD : xD = yD / zu) by (apply HsolD).
  destruct Hsign as [Hpos | Hneg].
  - (* positive branch *)
    assert (Hzlp : 0 < zl) by lia.
    assert (Hzup : 0 < zu) by lia.
    pose proof (fdivxz_pos_sound w xC yC zl Hpos HinC HsolC) as HCP.
    pose proof (fdivxz_pos_sound w xD yD zu Hpos HinD HsolD) as HDP.
    assert (HbC : a <= xC <= b) by (destruct HCP as (M&_&_); exact M).
    assert (HbD : a <= xD <= b) by (destruct HDP as (M&_&_); exact M).
    pose proof (div_bracket_pos yC zl Hzlp) as [BC1 BC2].
    pose proof (div_bracket_pos yD zu Hzup) as [BD1 BD2].
    rewrite <- HeqC in BC1, BC2. rewrite <- HeqD in BD1, BD2.
    clear HinC HinD HsolC HsolD HCP HDP HeqC HeqD Hlzge Hhzle Hxne Hy Hzne.
    repeat split; intro Hsgn; nia.
  - (* negative branch *)
    assert (Hzun : zu < 0) by lia.
    assert (Hzln : zl < 0) by lia.
    pose proof (fdivxz_neg_sound w xC yC zl Hneg HinC HsolC) as HCP.
    pose proof (fdivxz_neg_sound w xD yD zu Hneg HinD HsolD) as HDP.
    rewrite fdivxz_neg_eq_pos in HCP, HDP.
    assert (HbC : a <= xC <= b) by (destruct HCP as (M&_&_); exact M).
    assert (HbD : a <= xD <= b) by (destruct HDP as (M&_&_); exact M).
    pose proof (div_bracket_neg yC zl Hzln) as [BC1 BC2].
    pose proof (div_bracket_neg yD zu Hzun) as [BD1 BD2].
    rewrite <- HeqC in BC1, BC2. rewrite <- HeqD in BD1, BD2.
    clear HinC HinD HsolC HsolD HCP HDP HeqC HeqD Hlzge Hhzle Hxne Hy Hzne.
    repeat split; intro Hsgn; nia.
Qed.

(* ================================================================= *)
(*  Assembly helpers.                                                 *)
(* ================================================================= *)

Lemma assemble : forall s Y,
  lo (sy (propagator s)) <= Y -> Y <= hi (sy (propagator s)) ->
  (exists z, lo (sz (propagator s)) <= z <= hi (sz (propagator s)) /\ z <> 0 /\
     lo (sx (propagator s)) <= Y / z <= hi (sx (propagator s))) ->
  exists x z, in_store s x Y z /\ sol x Y z.
Proof.
  intros s Y HYl HYh [z [Hzr [Hnz Hxb]]].
  pose proof (propagator_reductive s) as Hred.
  unfold sle in Hred. destruct Hred as [Rx [Ry Rz]].
  unfold ile in Rx, Ry, Rz.
  destruct Rx as [Rx1 Rx2]; destruct Ry as [Ry1 Ry2]; destruct Rz as [Rz1 Rz2].
  exists (Y / z), z. unfold in_store, mem, sol.
  repeat split; try reflexivity; try lia.
Qed.

Lemma cover_lo : forall (A B ZL ZU c : Z),
  A <= B -> ZL <= ZU -> ZL <> 0 -> ZU <> 0 ->
  (0 < ZU -> c <= (B+1)*ZU-1) -> (0 < ZL -> c <= (B+1)*ZL-1) ->
  (ZL < 0 -> c <= A*ZL) -> (ZU < 0 -> c <= A*ZU) ->
  exists z, ZL <= z <= ZU /\ z <> 0 /\ A <= (Z.max c (Ylo A B ZL ZU)) / z <= B.
Proof.
  intros A B ZL ZU c HAB HZ HZLn HZUn U1 U2 U3 U4.
  destruct (Z.max_spec c (Ylo A B ZL ZU)) as [[_ E]|[_ E]]; rewrite E.
  - destruct (corner_Ylo A B ZL ZU HAB HZ HZLn HZUn) as [zc [Hor [Hnz Hb]]].
    exists zc. split; [destruct Hor; lia | split; [exact Hnz | exact Hb]].
  - assert (HYlo : Ylo A B ZL ZU <= c) by lia.
    destruct (pick_lo A B ZL ZU c HAB HZ HZLn HZUn HYlo U1 U2 U3 U4) as [z [Hr [Hnz Hb]]].
    exists z; split; [exact Hr | split; [exact Hnz | exact Hb]].
Qed.

Lemma cover_hi : forall (A B ZL ZU d : Z),
  A <= B -> ZL <= ZU -> ZL <> 0 -> ZU <> 0 ->
  (0 < ZU -> A*ZU <= d) -> (0 < ZL -> A*ZL <= d) ->
  (ZL < 0 -> (B+1)*ZL+1 <= d) -> (ZU < 0 -> (B+1)*ZU+1 <= d) ->
  exists z, ZL <= z <= ZU /\ z <> 0 /\ A <= (Z.min d (Yhi A B ZL ZU)) / z <= B.
Proof.
  intros A B ZL ZU d HAB HZ HZLn HZUn L1 L2 L3 L4.
  destruct (Z.min_spec d (Yhi A B ZL ZU)) as [[_ E]|[_ E]]; rewrite E.
  - assert (HYhi : d <= Yhi A B ZL ZU) by lia.
    destruct (pick_hi A B ZL ZU d HAB HZ HZLn HZUn HYhi L1 L2 L3 L4) as [z [Hr [Hnz Hb]]].
    exists z; split; [exact Hr | split; [exact Hnz | exact Hb]].
  - destruct (corner_Yhi A B ZL ZU HAB HZ HZLn HZUn) as [zc [Hor [Hnz Hb]]].
    exists zc. split; [destruct Hor; lia | split; [exact Hnz | exact Hb]].
Qed.

Lemma y_attain : forall s, consistent (propagator s) ->
  (exists x z, in_store s x (lo (sy (propagator s))) z /\ sol x (lo (sy (propagator s))) z) /\
  (exists x z, in_store s x (hi (sy (propagator s))) z /\ sol x (hi (sy (propagator s))) z).
Proof.
  intros s Hcons.
  set (N := fdivxz_pos (restrict_z_neg s)) in *.
  set (P := fdivxz_pos (restrict_z_pos s)) in *.
  set (u := sqcupbot N P) in *.
  assert (EPS : propagator s = refine_y u).
  { unfold u, N, P, propagator. rewrite (fdivxz_neg_eq_pos (restrict_z_neg s)). reflexivity. }
  assert (Esx : sx (propagator s) = sx u) by (rewrite EPS; unfold refine_y; cbn [sx]; reflexivity).
  assert (Esz : sz (propagator s) = sz u) by (rewrite EPS; unfold refine_y; cbn [sz]; reflexivity).
  assert (EsyN : sy N = sy s).
  { unfold N; rewrite Esy_fd; unfold restrict_z_neg; cbn [sy]; reflexivity. }
  assert (EsyP : sy P = sy s).
  { unfold P; rewrite Esy_fd; unfold restrict_z_pos; cbn [sy]; reflexivity. }
  assert (Esyu : lo (sy u) = lo (sy s) /\ hi (sy u) = hi (sy s)).
  { unfold u, sqcupbot.
    destruct (ne_store N) eqn:EN; destruct (ne_store P) eqn:EP; cbn iota.
    - cbn [sy sjoin]. unfold ijoin; cbn [lo hi]. rewrite EsyN, EsyP.
      split; [apply Z.min_id | apply Z.max_id].
    - rewrite EsyN; split; reflexivity.
    - rewrite EsyP; split; reflexivity.
    - rewrite EsyP; split; reflexivity. }
  assert (EsyLo : lo (sy (propagator s)) = Z.max (lo (sy s)) (Ylo (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u)))).
  { rewrite EPS; unfold refine_y; cbn [sy]; unfold inter; cbn [lo hi].
    rewrite (proj1 Esyu); reflexivity. }
  assert (EsyHi : hi (sy (propagator s)) = Z.min (hi (sy s)) (Yhi (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u)))).
  { rewrite EPS; unfold refine_y; cbn [sy]; unfold inter; cbn [lo hi].
    rewrite (proj2 Esyu); reflexivity. }
  assert (HrznN : hi (sz (restrict_z_neg s)) <= -1).
  { unfold restrict_z_neg; cbn [sz]; unfold inter; cbn [lo hi]. apply Z.le_min_r. }
  assert (HNle : hi (sz N) <= hi (sz (restrict_z_neg s))).
  { unfold N, fdivxz_pos; cbv zeta; cbn [sz]; unfold inter; cbn [lo hi]. apply Z.le_min_l. }
  assert (HN1 : hi (sz N) <= -1) by lia.
  assert (HrznP : 1 <= lo (sz (restrict_z_pos s))).
  { unfold restrict_z_pos; cbn [sz]; unfold inter; cbn [lo hi]. apply Z.le_max_r. }
  assert (HPge : lo (sz (restrict_z_pos s)) <= lo (sz P)).
  { unfold P, fdivxz_pos; cbv zeta; cbn [sz]; unfold inter; cbn [lo hi]. apply Z.le_max_l. }
  assert (HP1 : 1 <= lo (sz P)) by lia.
  assert (HsignN : 0 < lo (sz (restrict_z_neg s)) \/ hi (sz (restrict_z_neg s)) < 0) by lia.
  assert (HsignP : 0 < lo (sz (restrict_z_pos s)) \/ hi (sz (restrict_z_pos s)) < 0) by lia.
  unfold consistent in Hcons. destruct Hcons as [HCx [HCy HCz]].
  rewrite Esx in HCx. rewrite Esz in HCz.
  assert (Hcd : lo (sy s) <= hi (sy s)).
  { pose proof (Z.le_max_l (lo (sy s)) (Ylo (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u)))) as M1.
    pose proof (Z.le_min_l (hi (sy s)) (Yhi (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u)))) as M2.
    rewrite EsyLo in HCy. rewrite EsyHi in HCy. lia. }
  assert (Esy_rzp : sy (restrict_z_pos s) = sy s) by (unfold restrict_z_pos; cbn [sy]; reflexivity).
  assert (Esy_rzn : sy (restrict_z_neg s) = sy s) by (unfold restrict_z_neg; cbn [sy]; reflexivity).
  assert (Hznz : lo (sz u) <> 0 /\ hi (sz u) <> 0).
  { unfold u, sqcupbot in HCz |- *.
    destruct (ne_store N) eqn:EN; destruct (ne_store P) eqn:EP; cbn iota in HCz |- *.
    - cbn [sz sjoin] in HCz |- *. unfold ijoin in HCz |- *; cbn [lo hi] in HCz |- *.
      destruct (ne_store_bounds N EN) as (_ & _ & BNz).
      destruct (ne_store_bounds P EP) as (_ & _ & BPz).
      pose proof (Z.le_min_l (lo (sz N)) (lo (sz P))).
      pose proof (Z.le_max_r (hi (sz N)) (hi (sz P))). lia.
    - destruct (ne_store_bounds N EN) as (_ & _ & BNz). lia.
    - lia.
    - lia. }
  assert (Bands :
    (0 < hi (sz u) -> lo (sy s) <= (hi (sx u)+1)*hi (sz u)-1) /\
    (0 < lo (sz u) -> lo (sy s) <= (hi (sx u)+1)*lo (sz u)-1) /\
    (lo (sz u) < 0 -> lo (sy s) <= lo (sx u)*lo (sz u)) /\
    (hi (sz u) < 0 -> lo (sy s) <= lo (sx u)*hi (sz u)) /\
    (0 < hi (sz u) -> lo (sx u)*hi (sz u) <= hi (sy s)) /\
    (0 < lo (sz u) -> lo (sx u)*lo (sz u) <= hi (sy s)) /\
    (lo (sz u) < 0 -> (hi (sx u)+1)*lo (sz u)+1 <= hi (sy s)) /\
    (hi (sz u) < 0 -> (hi (sx u)+1)*hi (sz u)+1 <= hi (sy s))).
  { unfold u, sqcupbot in HCx, HCz |- *.
    destruct (ne_store N) eqn:EN; cbn iota in HCx, HCz |- *.
    - destruct (ne_store P) eqn:EP; cbn iota in HCx, HCz |- *.
      + (* both branches active *)
        cbn [sx sz sjoin] in HCx, HCz |- *. unfold ijoin in HCx, HCz |- *; cbn [lo hi] in HCx, HCz |- *.
        destruct (ne_store_bounds N EN) as (BNx & _ & BNz).
        destruct (ne_store_bounds P EP) as (BPx & _ & BPz).
        pose proof (BLU_branch (restrict_z_neg s) HsignN BNx Hcd BNz) as BN.
        pose proof (BLU_branch (restrict_z_pos s) HsignP BPx Hcd BPz) as BP.
        cbv zeta in BN, BP. rewrite Esy_rzn in BN. rewrite Esy_rzp in BP.
        fold N in BN. fold P in BP.
        destruct BN as [_ [_ [BN3 [_ [_ [_ [BN7 _]]]]]]].
        destruct BP as [BP1 [_ [_ [_ [BP5 _]]]]].
        assert (Hord1 : hi (sz N) <= hi (sz P)) by lia.
        assert (Hord2 : lo (sz N) <= lo (sz P)) by lia.
        assert (EZU : Z.max (hi (sz N)) (hi (sz P)) = hi (sz P)) by (apply Z.max_r; exact Hord1).
        assert (EZL : Z.min (lo (sz N)) (lo (sz P)) = lo (sz N)) by (apply Z.min_l; exact Hord2).
        rewrite EZU, EZL.
        specialize (BP1 ltac:(lia)). specialize (BP5 ltac:(lia)).
        specialize (BN3 ltac:(lia)). specialize (BN7 ltac:(lia)).
        pose proof (Z.le_max_r (hi (sx N)) (hi (sx P))) as MBP.
        pose proof (Z.le_max_l (hi (sx N)) (hi (sx P))) as MBN.
        pose proof (Z.le_min_r (lo (sx N)) (lo (sx P))) as MAP.
        pose proof (Z.le_min_l (lo (sx N)) (lo (sx P))) as MAN.
        clear EsyLo EsyHi HCy Esyu HsignN HsignP EPS Esx Esz EsyN EsyP Esy_rzp Esy_rzn HrznN HNle HrznP HPge Hznz HCx HCz.
        repeat split; intro Hsgn; nia.
      + (* only negative branch *)
        destruct (ne_store_bounds N EN) as (BNx & _ & BNz).
        pose proof (BLU_branch (restrict_z_neg s) HsignN BNx Hcd BNz) as BN.
        cbv zeta in BN. rewrite Esy_rzn in BN. fold N in BN.
        destruct BN as [_ [_ [BN3 [BN4 [_ [_ [BN7 BN8]]]]]]].
        clear EsyLo EsyHi HCy Esyu HsignN HsignP EPS Esx Esz EsyN EsyP Esy_rzp Esy_rzn HrznN HNle HrznP HPge Hznz HCx HCz HP1 HPge.
        repeat split; intro Hsgn;
          solve [ exfalso; lia | apply BN3; lia | apply BN4; lia | apply BN7; lia | apply BN8; lia ].
    - (* only positive branch (u = P) *)
      pose proof (BLU_branch (restrict_z_pos s) HsignP HCx Hcd HCz) as BP.
      cbv zeta in BP. rewrite Esy_rzp in BP. fold P in BP.
      destruct BP as [BP1 [BP2 [_ [_ [BP5 [BP6 _]]]]]].
      clear EsyLo EsyHi HCy Esyu HsignN HsignP EPS Esx Esz EsyN EsyP Esy_rzp Esy_rzn HrznN HNle HN1 HrznN Hznz.
      repeat split; intro Hsgn;
        solve [ exfalso; lia | apply BP1; lia | apply BP2; lia | apply BP5; lia | apply BP6; lia ]. }
  destruct Hznz as [ZLnz ZUnz].
  destruct Bands as [Bd1 [Bd2 [Bd3 [Bd4 [Bd5 [Bd6 [Bd7 Bd8]]]]]]].
  split.
  - apply assemble.
    + lia.
    + exact HCy.
    + rewrite Esx, Esz, EsyLo.
      apply (cover_lo (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u)) (lo (sy s)));
        [ exact HCx | exact HCz | exact ZLnz | exact ZUnz | exact Bd1 | exact Bd2 | exact Bd3 | exact Bd4 ].
  - apply assemble.
    + exact HCy.
    + lia.
    + rewrite Esx, Esz, EsyHi.
      apply (cover_hi (lo (sx u)) (hi (sx u)) (lo (sz u)) (hi (sz u)) (hi (sy s)));
        [ exact HCx | exact HCz | exact ZLnz | exact ZUnz | exact Bd5 | exact Bd6 | exact Bd7 | exact Bd8 ].
Qed.

