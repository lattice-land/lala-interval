From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ---- order on intervals / stores ---- *)
Definition ile (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.   (* i included in j *)
Definition sle (a b : store) : Prop :=
  ile (sx a) (sx b) /\ ile (sy a) (sy b) /\ ile (sz a) (sz b).
Definition Cx (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).
Lemma ijoin_ile : forall i j k, ile i k -> ile j k -> ile (ijoin i j) k.
Proof. unfold ile, ijoin; cbn [lo hi]; intros i j k [??] [??]; lia. Qed.

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
Proof. intros s vx vy vz H Hs. apply fdiv_propagator_sound; assumption. Qed.

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

(* NOTE: the literal statement WITHOUT [lo ix <= hi ix] and [lo iy <= hi iy]
   is FALSE (machine-checked counterexample): with ix = [2,1] (empty),
   iy = [0,3], iz = [1,3] we get fden = [1,1] (nonempty), tightness and
   0 < lo iz hold, yet ix is empty so no witness x exists.  The completeness
   statement is only meaningful for non-empty (well-formed) input intervals,
   which the propagator maintains, so those two hypotheses are added. *)
Lemma fden_opt_pos : forall ix iy iz,
  0 < lo iz ->
  lo ix <= hi ix ->
  lo iy <= hi iy ->
  ile ix (Cx iy iz) ->
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
  intros ix iy iz Hsign Hnx Hny Htight Hne.
  unfold mem, sol, ile, Cx in *. unfold fden in *; cbv zeta in *.
  destruct Htight as [HtL HtU].
  revert Hne.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end; cbn iota).
  all: intro Hne.
  all: repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (_ && _)%bool = false |- _ => apply andb_false_iff in H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    end.
  all: cbn [lo hi] in *.
  all: set (a := lo ix) in *; set (b := hi ix) in *;
       set (c := lo iy) in *; set (d := hi iy) in *;
       set (zl := lo iz) in *; set (zu := hi iz) in *.
  (* 1. M0 x M0 -> iz *)
  - split; apply witness_pos; solve [lia|exact Hnx|exact Hny|nia].
  (* 2. P1 x P *)
  - assert (Hb1 : 0 < b + 1) by lia.
    assert (Hmd : a * (d / a) <= d) by (apply Z.mul_div_le; lia).
    assert (Hsucc : Z.max 1 c < (b+1) * (Z.max 1 c/(b+1)+1)) by (apply Z.mul_succ_div_gt; lia).
    assert (Hcmax : c <= Z.max 1 c) by apply Z.le_max_r.
    assert (HzlL : zl <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_l.
    assert (HTL : Z.max 1 c/(b+1)+1 <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_r.
    assert (HHd : Z.min zu (d/a) <= d/a) by apply Z.le_min_r.
    split; apply witness_pos; solve [lia | exact Hnx | exact Hny | nia].
  (* 3. P1 x N -> empty (Hne contradictory) *)
  - exfalso; assert (Hdiv : 0 <= (-(Z.min (-1) d))/(b+1)) by (apply Z.div_pos; lia);
    assert (HcdivLe : cdiv (Z.min (-1) d) (b+1) <= 0) by (unfold cdiv; lia);
    assert (HHle : Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= cdiv (Z.min (-1) d) (b+1) - 1) by apply Z.le_min_r;
    assert (HzlL : zl <= Z.max zl (cdiv c a)) by apply Z.le_max_l; lia.
  (* 4. P1 x M/Z *)
  - destruct (Z_le_gt_dec d 0) as [Hd|Hd];
    [ exfalso; assert (Hda : d / a <= 0) by (rewrite <- (Z.div_0_l a) by lia; apply Z.div_le_mono; lia);
      assert (HH : Z.min zu (d/a) <= d/a) by apply Z.le_min_r;
      assert (HL : zl <= Z.max zl (cdiv c a)) by apply Z.le_max_l; lia
    | assert (Hc : c < 0) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hc0]; [assumption|exfalso; assert (((0<=?c)&&(0<?d))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia); congruence]);
      assert (Hmd : a*(d/a) <= d) by (apply Z.mul_div_le; lia);
      assert (HHd : Z.min zu (d/a) <= d/a) by apply Z.le_min_r;
      assert (HzlL : zl <= Z.max zl (cdiv c a)) by apply Z.le_max_l;
      split; apply witness_pos; solve [lia | exact Hnx | exact Hny | nia] ].
  (* 5. N'1 x P -> empty *)
  - exfalso; assert (Hca : c / a <= 0) by (apply (fdiv_ub_neg c a 0); lia);
    assert (HH : Z.min zu (c/a) <= c/a) by apply Z.le_min_r;
    assert (HL : zl <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_l; lia.
  (* 6. N'1 x N *)
  - assert (HdivL : cdiv d a <= Z.max zl (cdiv d a)) by apply Z.le_max_r;
    assert (HzlL : zl <= Z.max zl (cdiv d a)) by apply Z.le_max_l;
    assert (HdivH : Z.min zu (cdiv c (b+1) - 1) <= cdiv c (b+1) - 1) by apply Z.le_min_r;
    assert (Hbneg : b + 1 < 0) by lia; assert (Haneg : a < 0) by lia;
    assert (Haz : forall z, cdiv d a <= z -> a*z <= d) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-d) a ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-d) a Haneg) as B; set (q := (-d)/a) in *; nia);
    assert (Hcb : forall z, z + 1 <= cdiv c (b+1) -> c <= (b+1)*z - 1) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-c) (b+1) ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-c) (b+1) Hbneg) as B; set (q := (-c)/(b+1)) in *; nia);
    split; apply witness_pos; [lia|exact Hnx|exact Hny|apply Haz; lia|apply Hcb; lia|lia|exact Hnx|exact Hny|apply Haz; lia|apply Hcb; lia].
  (* 7. N'1 x M/Z *)
  - destruct (Z_le_gt_dec d 0) as [Hd|Hd];
    [ exfalso; assert (Hc0 : 0 <= c) by (destruct (Z_lt_le_dec c 0) as [Hcc|];[exfalso; assert (((c<?0)&&(d<=?0))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence|assumption]);
      assert (Hpos : 0 <= (-c)/(b+1)) by (apply (fdiv_lb_neg (-c) (b+1) 0); lia);
      assert (HcdivH : cdiv c (b+1) <= 0) by (unfold cdiv; lia);
      assert (Hhi : Z.min zu (cdiv c (b+1) - 1) <= cdiv c (b+1) - 1) by apply Z.le_min_r;
      assert (Hlo : zl <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_l; lia
    | assert (Hc : c < 0) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hc0];[assumption|exfalso; assert (((0<=?c)&&(0<?d))%bool=true) by (apply andb_true_intro; split;[apply Z.leb_le|apply Z.ltb_lt];lia); congruence]);
      assert (Haneg : a < 0) by lia; assert (Hbneg : b + 1 < 0) by lia;
      assert (Hcb : forall z, z+1 <= cdiv c (b+1) -> c <= (b+1)*z-1) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-c)(b+1) ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-c)(b+1) Hbneg) as B; set (q:=(-c)/(b+1)) in *; nia);
      assert (HdivH : Z.min zu (cdiv c(b+1)-1) <= cdiv c(b+1)-1) by apply Z.le_min_r;
      assert (Hlo : zl <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_l;
      assert (HL0 : 0 < Z.max zl (d/(b+1)+1)) by lia;
      assert (HH0 : 0 < Z.min zu (cdiv c(b+1)-1)) by lia;
      split; apply witness_pos; [lia|exact Hnx|exact Hny|nia|apply Hcb; lia|lia|exact Hnx|exact Hny|nia|apply Hcb; lia] ].
  (* 8. Z(x=0) x (d<0) -> empty *)
  - exfalso; assert (Hhi : Z.min zu (d-1) <= d-1) by apply Z.le_min_r; lia.
  (* 9. Z(x=0) x (d>=0) *)
  - assert (HcL : c+1 <= Z.max zl (c+1)) by apply Z.le_max_r;
    assert (HzlL : zl <= Z.max zl (c+1)) by apply Z.le_max_l;
    split; apply witness_pos; [lia|exact Hnx|exact Hny|nia|nia|lia|exact Hnx|exact Hny|nia|nia].
  (* 10. N'0,O x N *)
  - assert (Haneg : a < 0) by lia; assert (Hn : Z.min (-1) d <= d) by lia;
    assert (Haz : forall z, cdiv (Z.min (-1) d) a <= z -> a*z <= Z.min (-1) d) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-(Z.min (-1) d)) a ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-(Z.min (-1) d)) a Haneg) as B; set (q:=(-(Z.min (-1) d))/a) in *; nia);
    assert (HdivL : cdiv (Z.min (-1) d) a <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_r;
    assert (HzlL : zl <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_l;
    split; apply witness_pos;
    [lia|exact Hnx|exact Hny| apply Z.le_trans with (Z.min (-1) d); [apply Haz; lia|lia] | nia
    | lia|exact Hnx|exact Hny| apply Z.le_trans with (Z.min (-1) d); [apply Haz; lia|lia] | nia ].
  (* 11. N'0,O x P -> empty *)
  - exfalso; assert (Hmax : 1 <= Z.max 1 c) by apply Z.le_max_l;
    assert (Hca : Z.max 1 c / a <= 0) by (apply (fdiv_ub_neg (Z.max 1 c) a 0); lia);
    assert (HH : Z.min zu (Z.max 1 c / a) <= Z.max 1 c / a) by apply Z.le_min_r; lia.
  (* 12. N'0,O x Z (bottom) *)
  - exfalso; lia.
  (* 13. N'0,O x M -> iz *)
  - assert (Hd : 0 < d) by (destruct (Z_le_gt_dec d 0) as [Hd0|Hd1];[exfalso; assert (Hcpos:0<=c) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hcn];[exfalso; assert (((c<?0)&&(d<=?0))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence|lia]); assert (((c=?0)&&(d=?0))%bool=true) by (apply andb_true_intro; split; apply Z.eqb_eq; lia); congruence|lia]);
    assert (Hc : c < 0) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hcn];[lia|exfalso; assert (((0<?d)&&(0<=?c))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence]);
    split; apply witness_pos; [lia|exact Hnx|exact Hny|nia|nia|lia|exact Hnx|exact Hny|nia|nia].
  (* 14. P0 x N -> empty (Heqb forces d<0) *)
  - exfalso; assert (Hdlt : d < 0) by (destruct (Z_le_gt_dec 0 d) as [Hd|Hd];[|lia]; exfalso; assert (E : ((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool = true) by (apply andb_true_intro; split;[apply andb_true_intro; split;[apply andb_true_intro; split|]|]; apply Z.leb_le; lia); congruence);
    assert (Hn : Z.min (-1) d <= -1) by lia;
    assert (Hdivnp : 0 <= (-(Z.min (-1) d))/(b+1)) by (apply Z.div_pos; lia);
    assert (Hcd : cdiv (Z.min (-1) d) (b+1) <= 0) by (unfold cdiv; lia);
    assert (Hhi : Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= cdiv (Z.min (-1) d) (b+1) - 1) by apply Z.le_min_r; lia.
  (* 15. P0 x P *)
  - assert (Hb1 : 0 < b+1) by lia;
    assert (Hsucc : Z.max 1 c < (b+1)*(Z.max 1 c/(b+1)+1)) by (apply Z.mul_succ_div_gt; lia);
    assert (Hcmax : c <= Z.max 1 c) by apply Z.le_max_r;
    assert (HzlL : zl <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_l;
    assert (HTL : Z.max 1 c/(b+1)+1 <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_r;
    split; apply witness_pos; solve [lia|exact Hnx|exact Hny|nia].
  (* 16. P0 x else -> iz (guards + c<=d contradictory) *)
  - exfalso; destruct (Z_le_gt_dec c 0) as [Hc|Hc];
    [ assert (Hd : d < 0) by (destruct (Z_le_gt_dec 0 d) as [Hd0|Hd1];[exfalso; assert (((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool=true) by (apply andb_true_intro; split;[apply andb_true_intro;split;[apply andb_true_intro;split|]|];apply Z.leb_le;lia); congruence|lia]);
      assert (((c<?0)&&(d<=?0))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence
    | assert (Hd : d <= 0) by (destruct (Z_le_gt_dec d 0) as [Hd0|Hd1];[lia|exfalso; assert (((0<?d)&&(0<=?c))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence]); lia ].
  (* 17. else -> iz (tightness forces contradiction) *)
  - exfalso; assert (Ha1 : a <= -1) by (destruct (Z.eq_dec a 0) as [Ha0|Han];[assert (Hble : b <= 0) by (destruct (Z_le_gt_dec b 0) as [Hb|Hb];[assumption|exfalso; assert (((a=?0)&&(0<?b))%bool=true) by (apply andb_true_intro; split;[apply Z.eqb_eq|apply Z.ltb_lt];lia); congruence]); assert (Hbne : b <> 0) by (intro Hb0; assert (((a=?0)&&(b=?0))%bool=true) by (apply andb_true_intro; split; apply Z.eqb_eq; lia); congruence); lia|lia]);
    assert (Hb0 : 0 <= b) by (destruct (Z_le_gt_dec 0 b) as [Hb|Hb];[assumption|exfalso; assert (((a<=?-1)&&(b=?-1))%bool=true) by (apply andb_true_intro; split;[apply Z.leb_le|apply Z.eqb_eq];lia); congruence]);
    assert (Hzu : 0 < zu) by lia;
    destruct (Z_le_gt_dec c 0) as [Hc|Hc];
    [ assert (Hd : d < 0) by (destruct (Z_le_gt_dec 0 d) as [Hd0|Hd1];[exfalso; assert (((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool=true) by (apply andb_true_intro; split;[apply andb_true_intro;split;[apply andb_true_intro;split|]|];apply Z.leb_le;lia); congruence|lia]);
      assert (Hcorners : forall n m, n < 0 -> 0 < m -> n/m <= -1) by (intros n m Hn Hm; pose proof (Z.div_mod n m ltac:(lia)) as D; pose proof (Z.mod_pos_bound n m Hm) as B; nia);
      assert (HX : Xhi c d zl zu <= -1) by (unfold Xhi; repeat apply Z.max_lub; apply Hcorners; lia); lia
    | assert (Hcorners : forall n m, 0 < n -> 0 < m -> 0 <= n/m) by (intros n m Hn Hm; apply Z.div_pos; lia);
      assert (HX : 0 <= Xlo c d zl zu) by (unfold Xlo; repeat apply Z.min_glb; apply Hcorners; lia); lia ].
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

(* NOTE: the two well-formedness hypotheses [lo ix <= hi ix] and
   [lo iy <= hi iy] are REQUIRED: the statement without them is FALSE
   (e.g. ix=[-5,-4], iy=[5,4] (empty), iz=[-5,-1] satisfies the sign and
   tightness hypotheses and fden nonemptiness, yet iy is empty so no
   witness exists).  These hold for every well-formed interval, which is
   the intended domain (the grid validation only ranges over well-formed
   intervals). *)
Lemma fden_opt_neg : forall ix iy iz,
  lo ix <= hi ix ->
  lo iy <= hi iy ->
  hi iz < 0 ->
  ile ix (Cx iy iz) ->
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
  intros ix iy iz Hix Hiy Hsign Htight Hne.
  unfold ile, Cx in Htight. cbn [lo hi] in Htight.
  unfold mem, sol.
  unfold fden in *; cbv zeta in *.
  set (a := lo ix) in *. set (b := hi ix) in *.
  set (c := lo iy) in *. set (d := hi iy) in *.
  set (zl := lo iz) in *. set (zu := hi iz) in *.
  unfold Xlo, Xhi in Htight.
  destruct Htight as [Hxlo Hxhi].
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end; cbn iota).
  all: cbn [lo hi] in *.
  all: repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (_ && _)%bool = false |- _ => apply andb_false_iff in H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    end.
  all: try (exfalso; lia).
  (* 14 goals remain: M0, P1P, P1N, P1MZ, N1P, N1N, N1MZ, ZdN, N0N, N0P,
     N0else, P0N, P0P, final. *)
  (* --- G1 : M0 x M0 (returns iz) --- *)
  { split; [ exists 0, 0 | exists 0, 0 ];
    (repeat split); try lia; rewrite Z.div_0_l by lia; reflexivity. }
  (* --- G2 : P1 x P (dead) --- *)
  { exfalso.
    assert (Hb1: 0 < b + 1) by lia.
    assert (Hm: 0 <= Z.max 1 c) by (pose proof (Z.le_max_l 1 c); lia).
    assert (Hd: 0 <= Z.max 1 c / (b+1)) by (apply Z.div_pos; lia).
    pose proof (Z.le_max_r zl (Z.max 1 c / (b+1) + 1)).
    pose proof (Z.le_min_l zu (d / a)).
    lia. }
  (* --- G3 : P1 x N --- *)
  { assert (Ha: 0 < a) by exact Heqb1.
    assert (Hb1: 0 < b+1) by lia.
    pose proof (Z.mul_div_le (-c) a Ha) as Bc.
    assert (Ec: a * cdiv c a >= c) by (unfold cdiv; nia).
    destruct (div_bracket_pos (-d) (b+1) Hb1) as [Bd1 Bd2].
    assert (Ed: (b+1)*(cdiv d (b+1) - 1) < d) by (unfold cdiv; nia).
    replace (Z.min (-1) d) with d in * by lia.
    assert (Uzu: Z.min zu (cdiv d (b + 1) - 1) <= zu) by apply Z.le_min_l.
    assert (Ucd: Z.min zu (cdiv d (b + 1) - 1) <= cdiv d (b + 1) - 1) by apply Z.le_min_r.
    assert (Lge: cdiv c a <= Z.max zl (cdiv c a)) by apply Z.le_max_r.
    clear Hxlo Hxhi Bc Bd1 Bd2 Heqb0 Heqb2.
    set (L := Z.max zl (cdiv c a)) in *.
    set (U := Z.min zu (cdiv d (b+1) - 1)) in *.
    assert (HzL: L < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * L) by nia.
    assert (HLd: (b+1) * L < d) by nia.
    assert (HUc: c <= a * U) by nia.
    assert (HUd: (b+1) * U < d) by nia.
    split.
    - apply realize_neg; [ exact HzL | exact Hix | exact Hiy | exact HLc | exact HLd ].
    - apply realize_neg; [ exact HzU | exact Hix | exact Hiy | exact HUc | exact HUd ]. }
  (* --- G4 : P1 x M/Z --- *)
  { assert (Ha: 0 < a) by exact Heqb1.
    assert (Hb1: 0 < b+1) by lia.
    assert (Hd0: 0 <= d).
    { destruct (Z_le_gt_dec 0 d) as [|Hlt]; [assumption|exfalso].
      assert (((d<?0)&&(c<=?0))%bool = true) by
        (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia).
      congruence. }
    pose proof (Z.mul_div_le (-c) a Ha) as Bc.
    assert (Ec: a * cdiv c a >= c) by (unfold cdiv; nia).
    assert (Lge: cdiv c a <= Z.max zl (cdiv c a)) by apply Z.le_max_r.
    assert (Uzu: Z.min zu (d/a) <= zu) by apply Z.le_min_l.
    clear Hxlo Hxhi Bc Heqb0 Heqb2 Heqb3.
    set (L := Z.max zl (cdiv c a)) in *.
    set (U := Z.min zu (d/a)) in *.
    assert (HzL: L < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * L) by nia.
    assert (HLd: (b+1) * L < d) by nia.
    assert (HUc: c <= a * U) by nia.
    assert (HUd: (b+1) * U < d) by nia.
    split.
    - apply realize_neg; [exact HzL|exact Hix|exact Hiy|exact HLc|exact HLd].
    - apply realize_neg; [exact HzU|exact Hix|exact Hiy|exact HUc|exact HUd]. }
  (* --- G5 : N'1 x P --- *)
  { assert (Ha: a < 0) by lia.
    assert (Hb1n: b + 1 < 0) by lia.
    destruct (div_bracket_neg c a Ha) as [Bca1 Bca2].
    destruct (div_bracket_neg d (b+1) Hb1n) as [Bdb1 Bdb2].
    assert (Lge: d/(b+1) + 1 <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_r.
    assert (Uc: Z.min zu (c/a) <= c/a) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (c/a) <= zu) by apply Z.le_min_l.
    clear Hxlo Hxhi Bca1 Bdb2 Heqb0 Heqb2.
    set (L := Z.max zl (d/(b+1)+1)) in *.
    set (U := Z.min zu (c/a)) in *.
    assert (HLca: L <= c/a) by lia.
    assert (HzL: L < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * L) by nia.
    assert (HLd: (b+1) * L < d) by nia.
    assert (HUc: c <= a * U) by nia.
    assert (HUge: d/(b+1)+1 <= U) by lia.
    assert (HUd: (b+1) * U < d).
    { clear Bca2 HLca Uc HLc HUc Lge HLd HzL HzU Uzu Hne. nia. }
    split.
    - apply realize_neg; [exact HzL|exact Hix|exact Hiy|exact HLc|exact HLd].
    - apply realize_neg; [exact HzU|exact Hix|exact Hiy|exact HUc|exact HUd]. }
  (* --- G6 : N'1 x N (dead) --- *)
  { exfalso.
    assert (Hcd0: 0 <= cdiv d a) by (apply (cdiv_lb_neg d a 0); lia).
    pose proof (Z.le_max_r zl (cdiv d a)).
    pose proof (Z.le_min_l zu (cdiv c (b+1) - 1)).
    lia. }
  (* --- G7 : N'1 x M/Z --- *)
  { assert (Ha: a < 0) by lia.
    assert (Hb1n: b + 1 < 0) by lia.
    destruct (Z_lt_le_dec 0 d) as [Hd|Hd].
    - assert (Hc0: c < 0).
      { destruct (Z_le_gt_dec 0 c) as [Hc|]; [exfalso|lia].
        assert (((0<=?c)&&(0<?d))%bool = true) by
          (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        congruence. }
      destruct (div_bracket_neg d (b+1) Hb1n) as [Bdb1 Bdb2].
      assert (Lge: d/(b+1) + 1 <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_r.
      assert (Uzu: Z.min zu (cdiv c (b+1) - 1) <= zu) by apply Z.le_min_l.
      clear Hxlo Hxhi Bdb2 Heqb0 Heqb2 Heqb3 Heqb4.
      set (L := Z.max zl (d/(b+1)+1)) in *.
      set (U := Z.min zu (cdiv c (b+1) - 1)) in *.
      assert (HzL: L < 0) by lia.
      assert (HzU: U < 0) by lia.
      assert (HUge: d/(b+1)+1 <= U) by lia.
      assert (HLd: (b+1) * L < d) by (clear Uzu; nia).
      assert (HUd: (b+1) * U < d) by (clear Uzu Lge HLd HzL; nia).
      assert (HLc: c <= a * L) by (clear Bdb1 Lge HUge HLd HUd Uzu HzU; nia).
      assert (HUc: c <= a * U) by (clear Bdb1 Lge HUge HLd HUd Uzu HzL HLc; nia).
      split.
      + apply realize_neg; [exact HzL|exact Hix|exact Hiy|exact HLc|exact HLd].
      + apply realize_neg; [exact HzU|exact Hix|exact Hiy|exact HUc|exact HUd].
    - exfalso.
      assert (Hc0: 0 <= c).
      { destruct (Z_le_gt_dec 0 c) as [|Hcn]; [lia|exfalso].
        assert (((c<?0)&&(d<=?0))%bool = true) by
          (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia).
        congruence. }
      assert (Hc: c = 0) by lia. assert (Hde: d = 0) by lia.
      rewrite Hc, Hde in Hne.
      assert (E1: 0 / (b+1) = 0) by (apply Z.div_0_l; lia).
      assert (E2: cdiv 0 (b+1) = 0) by (unfold cdiv; rewrite Z.div_0_l; lia).
      rewrite E1, E2 in Hne.
      pose proof (Z.le_max_r zl (0 + 1)).
      pose proof (Z.le_min_r zu (0 - 1)).
      lia. }
  (* --- G8 : Z x (d<0) --- *)
  { assert (HdN: d < 0) by exact Heqb4.
    assert (Uub: Z.min zu (d-1) <= d - 1) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (d-1) <= zu) by apply Z.le_min_l.
    clear Hxlo Hxhi Heqb0.
    set (U := Z.min zu (d-1)) in *.
    assert (HzL: zl < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * zl) by (clear Uub Uzu; nia).
    assert (HLd: (b+1) * zl < d) by (clear Uzu HzU; nia).
    assert (HUc: c <= a * U) by (clear Uub HLc HLd HzL; nia).
    assert (HUd: (b+1) * U < d) by (clear Uzu HzL HLc HLd HUc; nia).
    split.
    - apply realize_neg; [exact HzL|exact Hix|exact Hiy|exact HLc|exact HLd].
    - apply realize_neg; [exact HzU|exact Hix|exact Hiy|exact HUc|exact HUd]. }
  (* --- G9 : N'0,O x N (dead) --- *)
  { exfalso.
    assert (Hmm: Z.min (-1) d <= -1) by apply Z.le_min_l.
    assert (Hc1: 1 <= cdiv (Z.min (-1) d) a) by (apply (cdiv_lb_neg (Z.min (-1) d) a 1); lia).
    pose proof (Z.le_max_r zl (cdiv (Z.min (-1) d) a)).
    lia. }
  (* --- G10 : N'0,O x P --- *)
  { assert (Ha: a < 0) by lia.
    destruct (div_bracket_neg (Z.max 1 c) a Ha) as [Bm1 Bm2].
    assert (Hmc: c <= Z.max 1 c) by apply Z.le_max_r.
    assert (Uc: Z.min zu (Z.max 1 c / a) <= Z.max 1 c / a) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (Z.max 1 c / a) <= zu) by apply Z.le_min_l.
    clear Hxlo Hxhi Bm1 Heqb0 Heqb3 Heqb5.
    set (U := Z.min zu (Z.max 1 c / a)) in *.
    assert (Hzlca: zl <= Z.max 1 c / a) by lia.
    assert (HzL: zl < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * zl) by (clear Uc Uzu; nia).
    assert (HLd: (b+1) * zl < d) by (clear Bm2 Hmc Uc Uzu Hzlca HzU HLc; nia).
    assert (HUc: c <= a * U) by (clear Uzu Hzlca HzL HLc HLd; nia).
    assert (HUd: (b+1) * U < d) by (clear Bm2 Hmc Uc Hzlca HzL HLc HLd HUc; nia).
    split.
    - apply realize_neg; [exact HzL|exact Hix|exact Hiy|exact HLc|exact HLd].
    - apply realize_neg; [exact HzU|exact Hix|exact Hiy|exact HUc|exact HUd]. }
  (* --- G11 : N'0,O x M (spanning y, returns iz) --- *)
  { assert (Hc: c < 0).
    { destruct (Z_lt_le_dec c 0) as [|Hcge]; [assumption|exfalso].
      destruct (Z_lt_le_dec 0 d) as [Hd|Hd].
      - assert (((0<?d)&&(0<=?c))%bool = true) by
          (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia). congruence.
      - assert (((c=?0)&&(d=?0))%bool = true) by
          (apply andb_true_intro; split; apply Z.eqb_eq; lia). congruence. }
    assert (Hd: 0 < d).
    { destruct (Z_lt_le_dec 0 d) as [|Hdle]; [assumption|exfalso].
      assert (((c<?0)&&(d<=?0))%bool = true) by
        (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia). congruence. }
    assert (Ha: a < 0) by lia.
    assert (HzL: zl < 0) by lia.
    assert (HzU: zu < 0) by lia.
    clear Hxlo Hxhi Heqb0 Heqb3 Heqb5 Heqb6 Heqb7.
    split.
    - apply realize_neg; [exact HzL|exact Hix|exact Hiy| nia | nia ].
    - apply realize_neg; [exact HzU|exact Hix|exact Hiy| nia | nia ]. }
  (* --- G12 : P0 x N --- *)
  { assert (Hb1: 0 < b+1) by lia.
    assert (Hmd: Z.min (-1) d <= d) by apply Z.le_min_r.
    destruct (div_bracket_pos (-(Z.min (-1) d)) (b+1) Hb1) as [Bn1 Bn2].
    assert (Ed: (b+1)*(cdiv (Z.min (-1) d) (b+1) - 1) < Z.min (-1) d) by (unfold cdiv; nia).
    assert (Uub: Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= cdiv (Z.min (-1) d) (b+1) - 1) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= zu) by apply Z.le_min_l.
    clear Hxlo Hxhi Bn1 Bn2 Heqb0 Heqb3.
    set (U := Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1)) in *.
    assert (HzL: zl < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * zl) by (clear Ed Uub Hmd; nia).
    assert (HLd: (b+1)*zl < d) by (clear HzU HLc; nia).
    assert (HUc: c <= a * U) by (clear Ed HLc HLd HzL; nia).
    assert (HUd: (b+1)*U < d) by (clear Uzu HzL HLc HLd HUc; nia).
    split.
    - apply realize_neg; [exact HzL|exact Hix|exact Hiy|exact HLc|exact HLd].
    - apply realize_neg; [exact HzU|exact Hix|exact Hiy|exact HUc|exact HUd]. }
  (* --- G13 : P0 x P (dead) --- *)
  { exfalso.
    assert (Hb1: 0 < b + 1) by lia.
    assert (Hm: 0 <= Z.max 1 c) by (pose proof (Z.le_max_l 1 c); lia).
    assert (Hd: 0 <= Z.max 1 c / (b+1)) by (apply Z.div_pos; lia).
    pose proof (Z.le_max_r zl (Z.max 1 c / (b+1) + 1)).
    lia. }
  (* --- G14 : final else (vacuous by tightness) --- *)
  { exfalso.
    assert (Hzl0: zl < 0) by lia.
    assert (Ha1: a <= -1).
    { destruct (Z.eq_dec a 0) as [Hae|Hane]; [exfalso|lia].
      assert (Hb_le0: b <= 0).
      { destruct (Z_le_gt_dec b 0) as [|Hbp]; [assumption|exfalso].
        assert (((a=?0)&&(0<?b))%bool = true) by
          (apply andb_true_intro; split; [apply Z.eqb_eq;lia|apply Z.ltb_lt;lia]).
        congruence. }
      assert (Hbne: b <> 0).
      { intro. assert (((a=?0)&&(b=?0))%bool = true) by
          (apply andb_true_intro; split; apply Z.eqb_eq; lia). congruence. }
      lia. }
    assert (Hb0: 0 <= b).
    { assert (Hbne1: b <> -1).
      { intro. assert (((a<=?-1)&&(b=?-1))%bool = true) by
          (apply andb_true_intro; split; [apply Z.leb_le;lia|apply Z.eqb_eq;lia]). congruence. }
      lia. }
    destruct (Z_lt_le_dec 0 c) as [Hc|Hc].
    - assert (c/zl < 0) by (apply (fdiv_lt_neg c zl 0); lia).
      assert (c/zu < 0) by (apply (fdiv_lt_neg c zu 0); lia).
      assert (d/zl < 0) by (apply (fdiv_lt_neg d zl 0); lia).
      assert (d/zu < 0) by (apply (fdiv_lt_neg d zu 0); lia).
      assert (HX: Z.max (Z.max (c/zl) (c/zu)) (Z.max (d/zl) (d/zu)) < 0)
        by (repeat apply Z.max_lub_lt; lia).
      lia.
    - assert (Hd: d < 0).
      { destruct (Z_lt_le_dec d 0) as [|Hdn]; [assumption|exfalso].
        assert (((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool = true) by
          (apply andb_true_intro; split;
           [apply andb_true_intro; split;
            [apply andb_true_intro; split; apply Z.leb_le; lia | apply Z.leb_le; lia]
           | apply Z.leb_le; lia]).
        congruence. }
      assert (0 <= c/zl) by (rewrite <- (Z.div_opp_opp c zl) by lia; apply Z.div_pos; lia).
      assert (0 <= c/zu) by (rewrite <- (Z.div_opp_opp c zu) by lia; apply Z.div_pos; lia).
      assert (0 <= d/zl) by (rewrite <- (Z.div_opp_opp d zl) by lia; apply Z.div_pos; lia).
      assert (0 <= d/zu) by (rewrite <- (Z.div_opp_opp d zu) by lia; apply Z.div_pos; lia).
      assert (HX: 0 <= Z.min (Z.min (c/zl) (c/zu)) (Z.min (d/zl) (d/zu)))
        by (repeat apply Z.min_glb; lia).
      lia. }
Qed.

(* fden z-optimality, both signs combined. *)
Lemma fden_opt : forall ix iy iz,
  (0 < lo iz \/ hi iz < 0) -> lo ix <= hi ix -> lo iy <= hi iy ->
  ile ix (Cx iy iz) -> lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
  intros ix iy iz Hsign Hix Hiy Ht Hne. destruct Hsign as [Hpos|Hneg];
    [ apply fden_opt_pos | apply fden_opt_neg ]; assumption.
Qed.

(* Branch (x,z) attainment: every x- and z-bound of [fdivxz_pos w] is realised by a
   genuine solution inside w (dual of [fdivxz_pos_sound]).  [proved separately]. *)
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

(* helper: fden output is included in the incoming z-interval (when nonempty) *)
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

(* the two branch operators are the same function *)
Lemma fdivxz_neg_eq_pos : forall w, fdivxz_neg w = fdivxz_pos w.
Proof. reflexivity. Qed.

(* y-bounds of the output attained by solutions of the input [proved separately]. *)
Lemma y_attain : forall s, consistent (propagator s) ->
  (exists x z, in_store s x (lo (sy (propagator s))) z /\ sol x (lo (sy (propagator s))) z) /\
  (exists x z, in_store s x (hi (sy (propagator s))) z /\ sol x (hi (sy (propagator s))) z).
Proof. Admitted.

(* infeasibility detection (a by-product of the attainment lemmas). *)
Lemma cons_feasible : forall s, consistent (propagator s) -> feasible s.
Proof. Admitted.

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
Lemma propagator_optimal : forall s, optimal s.
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

(* Idempotency (on consistent outputs) is an immediate corollary of optimality,
   soundness and infeasibility-detection. *)
Theorem propagator_idem : forall s,
  consistent (propagator s) -> propagator (propagator s) = propagator s.
Proof.
  intros s Hc.
  destruct (cons_feasible s Hc) as (x0 & y0 & z0 & Hin0 & Hsol0).
  assert (Hin0p : in_store (propagator s) x0 y0 z0) by (apply prop_sound; assumption).
  apply sle_antisym.
  - apply (propagator_optimal (propagator s)).
    + exists x0, y0, z0; split; assumption.
    + intros vx vy vz H _; exact H.
  - apply (propagator_optimal s).
    + exists x0, y0, z0; split; assumption.
    + intros vx vy vz H Hs.
      apply (prop_sound (propagator s) vx vy vz).
      * apply (prop_sound s vx vy vz H Hs).
      * exact Hs.
Qed.
