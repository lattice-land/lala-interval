From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase.
From LalaInterval Require Import optbase2.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ================================================================= *)
(*  Numerator "band" membership (copied from ya_a.v)                 *)
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

(* ================================================================= *)
(*  Endpoint corners (copied from ya_b.v)                            *)
(* ================================================================= *)

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
(*  Branch (x,z) attainment (copied from optdev.v, self-contained)    *)
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
(*  Structural helpers                                               *)
(* ================================================================= *)

Lemma mem_inter_l : forall i j v, mem (inter i j) v -> mem i v.
Proof.
  intros i j v; unfold mem, inter; cbn [lo hi]; intro H.
  pose proof (Z.le_max_l (lo i) (lo j)). pose proof (Z.le_min_l (hi i) (hi j)). lia.
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

Lemma instore_rzp : forall s x y z, in_store (restrict_z_pos s) x y z -> in_store s x y z.
Proof.
  intros s x y z (Hx & Hy & Hz).
  unfold restrict_z_pos in *; cbn [sx sy sz] in *.
  unfold in_store; split; [exact Hx | split; [exact Hy | exact (mem_inter_l _ _ _ Hz)]].
Qed.

Lemma instore_rzn : forall s x y z, in_store (restrict_z_neg s) x y z -> in_store s x y z.
Proof.
  intros s x y z (Hx & Hy & Hz).
  unfold restrict_z_neg in *; cbn [sx sy sz] in *.
  unfold in_store; split; [exact Hx | split; [exact Hy | exact (mem_inter_l _ _ _ Hz)]].
Qed.

(* z-corner solutions for the positive branch, lifted into s *)
Lemma zcorners_P : forall s,
  ne_store (fdivxz_pos (restrict_z_pos s)) = true -> lo (sy s) <= hi (sy s) ->
  (exists x y, in_store s x y (lo (sz (fdivxz_pos (restrict_z_pos s))))
               /\ sol x y (lo (sz (fdivxz_pos (restrict_z_pos s))))) /\
  (exists x y, in_store s x y (hi (sz (fdivxz_pos (restrict_z_pos s))))
               /\ sol x y (hi (sz (fdivxz_pos (restrict_z_pos s))))).
Proof.
  intros s HP Hsy.
  destruct (ne_store_bounds _ HP) as (Bx & _ & Bz).
  assert (Hsign : 0 < lo (sz (restrict_z_pos s)) \/ hi (sz (restrict_z_pos s)) < 0).
  { unfold restrict_z_pos; cbn [sz]; unfold inter; cbn [lo hi]; left.
    pose proof (Z.le_max_r (lo (sz s)) 1); lia. }
  assert (Hyw : lo (sy (restrict_z_pos s)) <= hi (sy (restrict_z_pos s)))
    by (unfold restrict_z_pos; cbn [sy]; exact Hsy).
  destruct (branch_attain (restrict_z_pos s) Hsign Hyw Bx Bz)
    as [_ [_ [[xl [yl [Hl Sl]]] [xh [yh [Hh Sh]]]]]].
  split.
  - exists xl, yl. split; [apply instore_rzp; exact Hl | exact Sl].
  - exists xh, yh. split; [apply instore_rzp; exact Hh | exact Sh].
Qed.

Lemma zcorners_N : forall s,
  ne_store (fdivxz_pos (restrict_z_neg s)) = true -> lo (sy s) <= hi (sy s) ->
  (exists x y, in_store s x y (lo (sz (fdivxz_pos (restrict_z_neg s))))
               /\ sol x y (lo (sz (fdivxz_pos (restrict_z_neg s))))) /\
  (exists x y, in_store s x y (hi (sz (fdivxz_pos (restrict_z_neg s))))
               /\ sol x y (hi (sz (fdivxz_pos (restrict_z_neg s))))).
Proof.
  intros s HN Hsy.
  destruct (ne_store_bounds _ HN) as (Bx & _ & Bz).
  assert (Hsign : 0 < lo (sz (restrict_z_neg s)) \/ hi (sz (restrict_z_neg s)) < 0).
  { unfold restrict_z_neg; cbn [sz]; unfold inter; cbn [lo hi]; right.
    pose proof (Z.le_min_r (hi (sz s)) (-1)); lia. }
  assert (Hyw : lo (sy (restrict_z_neg s)) <= hi (sy (restrict_z_neg s)))
    by (unfold restrict_z_neg; cbn [sy]; exact Hsy).
  destruct (branch_attain (restrict_z_neg s) Hsign Hyw Bx Bz)
    as [_ [_ [[xl [yl [Hl Sl]]] [xh [yh [Hh Sh]]]]]].
  split.
  - exists xl, yl. split; [apply instore_rzn; exact Hl | exact Sl].
  - exists xh, yh. split; [apply instore_rzn; exact Hh | exact Sh].
Qed.

(* z-corners of a consistent output are non-zero *)
Lemma prop_z_nonzero : forall s,
  consistent (propagator s) ->
  lo (sz (propagator s)) <> 0 /\ hi (sz (propagator s)) <> 0.
Proof.
  intros s Hcons.
  set (N := fdivxz_pos (restrict_z_neg s)) in *.
  set (P := fdivxz_pos (restrict_z_pos s)) in *.
  assert (ESZ : sz (propagator s) = sz (sqcupbot N P)) by reflexivity.
  unfold consistent in Hcons. destruct Hcons as [_ [_ Hzz]].
  assert (HN : hi (sz N) <= -1).
  { unfold N, fdivxz_pos; cbv zeta; cbn [sz]. unfold restrict_z_neg; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  assert (HP : 1 <= lo (sz P)).
  { unfold P, fdivxz_pos; cbv zeta; cbn [sz]. unfold restrict_z_pos; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  rewrite ESZ in Hzz |- *.
  unfold sqcupbot in Hzz |- *.
  destruct (ne_store N) eqn:EN; destruct (ne_store P) eqn:EP; cbn iota in Hzz |- *.
  - unfold sjoin; cbn [sz]; unfold ijoin; cbn [lo hi].
    destruct (ne_store_bounds _ EN) as (_ & _ & BzN).
    destruct (ne_store_bounds _ EP) as (_ & _ & BzP).
    split.
    + pose proof (Z.le_min_l (lo (sz N)) (lo (sz P))). lia.
    + pose proof (Z.le_max_r (hi (sz N)) (hi (sz P))). lia.
  - destruct (ne_store_bounds _ EN) as (_ & _ & BzN). lia.
  - destruct (ne_store_bounds _ EP) as (_ & _ & BzP). lia.
  - lia.
Qed.

(* ================================================================= *)
(*  z-corner solutions of a consistent output                        *)
(* ================================================================= *)
Lemma corner_sols : forall s, consistent (propagator s) ->
  (exists x y, in_store s x y (lo (sz (propagator s))) /\ sol x y (lo (sz (propagator s)))) /\
  (exists x y, in_store s x y (hi (sz (propagator s))) /\ sol x y (hi (sz (propagator s)))).
Proof.
  intros s Hcons.
  set (N := fdivxz_pos (restrict_z_neg s)) in *.
  set (P := fdivxz_pos (restrict_z_pos s)) in *.
  assert (ESZ : sz (propagator s) = sz (sqcupbot N P)) by reflexivity.
  pose proof (propagator_reductive s) as Hred.
  destruct Hred as [_ [Ry _]]. unfold ile in Ry.
  assert (Hcc := Hcons). unfold consistent in Hcc. destruct Hcc as [_ [HCy _]].
  assert (Hsy : lo (sy s) <= hi (sy s)) by lia.
  assert (HN : hi (sz N) <= -1).
  { unfold N, fdivxz_pos; cbv zeta; cbn [sz]. unfold restrict_z_neg; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  assert (HP : 1 <= lo (sz P)).
  { unfold P, fdivxz_pos; cbv zeta; cbn [sz]. unfold restrict_z_pos; cbn [sz].
    unfold inter at 1; cbn [lo hi]. unfold inter; cbn [lo hi]. lia. }
  rewrite ESZ.
  unfold sqcupbot.
  destruct (ne_store N) eqn:EN; destruct (ne_store P) eqn:EP.
  - destruct (ne_store_bounds _ EN) as (_ & _ & BzN).
    destruct (ne_store_bounds _ EP) as (_ & _ & BzP).
    cbn [sz sjoin]; unfold ijoin; cbn [lo hi].
    rewrite (Z.min_l (lo (sz N)) (lo (sz P))) by lia.
    rewrite (Z.max_r (hi (sz N)) (hi (sz P))) by lia.
    destruct (zcorners_N s EN Hsy) as [ZNlo _].
    destruct (zcorners_P s EP Hsy) as [_ ZPhi].
    split; [exact ZNlo | exact ZPhi].
  - destruct (zcorners_N s EN Hsy) as [ZNlo ZNhi].
    split; [exact ZNlo | exact ZNhi].
  - destruct (zcorners_P s EP Hsy) as [ZPlo ZPhi].
    split; [exact ZPlo | exact ZPhi].
  - exfalso.
    assert (HeqP : sqcupbot N P = P) by (unfold sqcupbot; rewrite EN; reflexivity).
    destruct Hcons as (HCx & HCy2 & HCz).
    assert (EXX : sx (propagator s) = sx P).
    { change (propagator s) with (refine_y (sqcupbot N P)); unfold refine_y; cbn [sx]; rewrite HeqP; reflexivity. }
    assert (EZZ : sz (propagator s) = sz P).
    { change (propagator s) with (refine_y (sqcupbot N P)); unfold refine_y; cbn [sz]; rewrite HeqP; reflexivity. }
    assert (EYY : sy (propagator s) = inter (sy P) (Itv (Ylo (lo (sx P)) (hi (sx P)) (lo (sz P)) (hi (sz P))) (Yhi (lo (sx P)) (hi (sx P)) (lo (sz P)) (hi (sz P))))).
    { change (propagator s) with (refine_y (sqcupbot N P)); unfold refine_y; cbn [sx sy sz]; rewrite HeqP; reflexivity. }
    rewrite EXX in HCx. rewrite EZZ in HCz. rewrite EYY in HCy2.
    unfold inter in HCy2; cbn [lo hi] in HCy2.
    assert (Ay : lo (sy P) <= hi (sy P)).
    { pose proof (Z.le_max_l (lo (sy P)) (Ylo (lo (sx P)) (hi (sx P)) (lo (sz P)) (hi (sz P)))).
      pose proof (Z.le_min_l (hi (sy P)) (Yhi (lo (sx P)) (hi (sx P)) (lo (sz P)) (hi (sz P)))). lia. }
    pose proof (bounds_ne_store P HCx Ay HCz) as Hne. rewrite Hne in EP; discriminate.
Qed.

(* the joined sy-interval keeps the input sy bounds *)
Lemma sy_join : forall s,
  lo (sy (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))) = lo (sy s)
  /\ hi (sy (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))) = hi (sy s).
Proof.
  intro s. unfold sqcupbot.
  destruct (ne_store (fdivxz_pos (restrict_z_neg s)));
  destruct (ne_store (fdivxz_pos (restrict_z_pos s)));
  cbn [sjoin sy ijoin lo hi]; try (rewrite Z.min_id, Z.max_id); split; reflexivity.
Qed.

(* a nonzero corner solution converts a quotient-window membership into band bounds *)
Lemma band_from_pos : forall a b zc y, 0 < zc -> a <= y/zc <= b -> a*zc <= y /\ y <= (b+1)*zc - 1.
Proof.
  intros a b zc y Hzc [H1 H2]. destruct (div_bracket_pos y zc Hzc) as [B1 B2]. split; nia.
Qed.
Lemma band_from_neg : forall a b zc y, zc < 0 -> a <= y/zc <= b -> y <= a*zc /\ (b+1)*zc + 1 <= y.
Proof.
  intros a b zc y Hzc [H1 H2]. destruct (div_bracket_neg y zc Hzc) as [B1 B2]. split; nia.
Qed.

(* ================================================================= *)
(*  Main theorem: the output y-bounds are attained by input solutions *)
(* ================================================================= *)
Lemma y_attain : forall s, consistent (propagator s) ->
  (exists x z, in_store s x (lo (sy (propagator s))) z /\ sol x (lo (sy (propagator s))) z) /\
  (exists x z, in_store s x (hi (sy (propagator s))) z /\ sol x (hi (sy (propagator s))) z).
Proof.
  intros s Hcons.
  pose proof (propagator_reductive s) as Hred.
  destruct Hred as [Rx [Ry Rz]]. unfold ile in Rx, Ry, Rz.
  assert (Hc := Hcons). unfold consistent in Hc. destruct Hc as [Hxx [Hyy Hzz]].
  destruct (prop_z_nonzero s Hcons) as [Hzln Hzun].
  destruct (corner_sols s Hcons) as [CSlo CShi].
  destruct (sy_join s) as [LSY HSY].
  set (A := lo (sx (propagator s))) in *.
  set (B := hi (sx (propagator s))) in *.
  set (ZL := lo (sz (propagator s))) in *.
  set (ZU := hi (sz (propagator s))) in *.
  destruct Rx as [Rx1 Rx2]. destruct Rz as [Rz1 Rz2]. destruct Ry as [Ry1 Ry2].
  assert (Hsyle : lo (sy s) <= hi (sy s)) by lia.
  assert (HYlo : lo (sy (propagator s)) = Z.max (lo (sy s)) (Ylo A B ZL ZU)).
  { change (propagator s) with
      (refine_y (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))) at 1.
    unfold refine_y; cbn [sx sy sz]. unfold inter; cbn [lo hi]. rewrite LSY. reflexivity. }
  assert (HYhi : hi (sy (propagator s)) = Z.min (hi (sy s)) (Yhi A B ZL ZU)).
  { change (propagator s) with
      (refine_y (sqcupbot (fdivxz_pos (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))) at 1.
    unfold refine_y; cbn [sx sy sz]. unfold inter; cbn [lo hi]. rewrite HSY. reflexivity. }
  assert (BandU : forall zc, (exists x y, in_store s x y zc /\ sol x y zc) ->
     exists y, lo (sy s) <= y <= hi (sy s) /\ A <= y / zc <= B /\ zc <> 0).
  { intros zc [x [y [Hin Hsol]]].
    pose proof (fdiv_propagator_sound s x y zc Hin Hsol) as Hinp.
    destruct Hinp as (Mx & _ & _). unfold mem in Mx.
    destruct Hin as (_ & Hsy2 & _). unfold mem in Hsy2.
    destruct Hsol as [Hnz Heq]. exists y. subst x.
    split; [exact Hsy2 | split; [exact Mx | exact Hnz]]. }
  destruct (BandU ZU CShi) as [yU [HyU [HxU HnzU]]].
  destruct (BandU ZL CSlo) as [yL [HyL [HxL HnzL]]].
  assert (Hmk : forall Y zc, lo (sy s) <= Y <= hi (sy s) -> zc <> 0 ->
     A <= Y/zc <= B -> ZL <= zc <= ZU -> exists x z, in_store s x Y z /\ sol x Y z).
  { intros Y zc HY Hnz Hx Hzc. exists (Y/zc), zc.
    split.
    - unfold in_store, mem. repeat split; lia.
    - unfold sol; split; [exact Hnz | reflexivity]. }
  split.
  - rewrite HYlo.
    destruct (Z.max_spec (lo (sy s)) (Ylo A B ZL ZU)) as [[Hlt E]|[Hge E]]; rewrite E.
    + assert (Hlop : lo (sy (propagator s)) = Ylo A B ZL ZU) by (rewrite HYlo; exact E).
      destruct (corner_Ylo A B ZL ZU Hxx Hzz Hzln Hzun) as [zc [Hzc [Hzcnz Hdv]]].
      apply (Hmk (Ylo A B ZL ZU) zc);
        [ lia | exact Hzcnz | exact Hdv | destruct Hzc; subst zc; lia ].
    + destruct (pick_lo A B ZL ZU (lo (sy s)) Hxx Hzz Hzln Hzun Hge
        ltac:(intro Hp; destruct (band_from_pos A B ZU yU Hp HxU) as [_ Hub]; lia)
        ltac:(intro Hp; destruct (band_from_pos A B ZL yL Hp HxL) as [_ Hub]; lia)
        ltac:(intro Hn; destruct (band_from_neg A B ZL yL Hn HxL) as [Hub _]; lia)
        ltac:(intro Hn; destruct (band_from_neg A B ZU yU Hn HxU) as [Hub _]; lia))
        as [zc [Hzcrng [Hzcnz Hdv]]].
      apply (Hmk (lo (sy s)) zc); [ lia | exact Hzcnz | exact Hdv | exact Hzcrng ].
  - rewrite HYhi.
    destruct (Z.min_spec (hi (sy s)) (Yhi A B ZL ZU)) as [[Hle E]|[Hlt E]]; rewrite E.
    + destruct (pick_hi A B ZL ZU (hi (sy s)) Hxx Hzz Hzln Hzun ltac:(lia)
        ltac:(intro Hp; destruct (band_from_pos A B ZU yU Hp HxU) as [Hlb _]; lia)
        ltac:(intro Hp; destruct (band_from_pos A B ZL yL Hp HxL) as [Hlb _]; lia)
        ltac:(intro Hn; destruct (band_from_neg A B ZL yL Hn HxL) as [_ Hlb]; lia)
        ltac:(intro Hn; destruct (band_from_neg A B ZU yU Hn HxU) as [_ Hlb]; lia))
        as [zc [Hzcrng [Hzcnz Hdv]]].
      apply (Hmk (hi (sy s)) zc); [ lia | exact Hzcnz | exact Hdv | exact Hzcrng ].
    + assert (Hhip : hi (sy (propagator s)) = Yhi A B ZL ZU) by (rewrite HYhi; exact E).
      destruct (corner_Yhi A B ZL ZU Hxx Hzz Hzln Hzun) as [zc [Hzc [Hzcnz Hdv]]].
      apply (Hmk (Yhi A B ZL ZU) zc);
        [ lia | exact Hzcnz | exact Hdv | destruct Hzc; subst zc; lia ].
Qed.
