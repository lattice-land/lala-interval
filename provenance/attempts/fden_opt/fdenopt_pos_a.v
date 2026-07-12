From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Definition ileD (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.
Definition CxD (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).

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
  ileD ix (CxD iy iz) ->
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
  intros ix iy iz Hsign Hnx Hny Htight Hne.
  unfold mem, sol, ileD, CxD in *. unfold fden in *; cbv zeta in *.
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
