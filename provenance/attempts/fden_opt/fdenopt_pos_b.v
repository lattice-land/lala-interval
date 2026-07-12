From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Definition ileD (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.
Definition CxD (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).

(* Uniform witness builder for a positive target divisor [z0]: the witness
   quotient is [x0 = min (hi ix) (hi iy / z0)] and the witness numerator is
   [max (lo iy) (z0*x0)].  Reduces attainment of [z0] to two bracket facts. *)
Lemma attain_pos2 : forall (ix iy : itv) z0,
  0 < z0 -> lo ix <= hi ix -> lo iy <= hi iy ->
  z0 * lo ix <= hi iy -> lo iy < z0 * (hi ix + 1) ->
  exists x y, mem ix x /\ mem iy y /\ sol x y z0.
Proof.
  intros ix iy z0 Hz0 Hab Hcd Hub Hlb.
  exists (Z.min (hi ix) (hi iy / z0)), (Z.max (lo iy) (z0 * (Z.min (hi ix) (hi iy / z0)))).
  set (x0 := Z.min (hi ix) (hi iy / z0)) in *.
  assert (Hx0b : x0 <= hi ix) by apply Z.le_min_l.
  assert (Hx0d : x0 <= hi iy / z0) by apply Z.le_min_r.
  assert (Hax0 : lo ix <= x0).
  { apply Z.min_glb; [exact Hab|]. apply Z.div_le_lower_bound; [lia|lia]. }
  assert (Hub2 : z0 * x0 <= hi iy).
  { apply Z.le_trans with (z0 * (hi iy / z0)); [nia|]. apply Z.mul_div_le; lia. }
  unfold mem, sol.
  split; [split; [exact Hax0|exact Hx0b]|].
  split.
  - split; [apply Z.le_max_l| apply Z.max_lub; lia].
  - split; [lia|].
    destruct (Z.max_spec (lo iy) (z0 * x0)) as [[Hlt E]|[Hge E]]; rewrite E.
    + rewrite Z.mul_comm. rewrite Z.div_mul; [reflexivity|lia].
    + assert (Hle1 : lo iy / z0 <= x0).
      { apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|].
        destruct (Z.min_spec (hi ix) (hi iy / z0)) as [[H E2]|[H E2]].
        - unfold x0; rewrite E2. lia.
        - unfold x0; rewrite E2.
          assert (hi iy < z0 * (hi iy / z0 + 1)) by (apply Z.mul_succ_div_gt; lia). lia. }
      assert (Hge1 : x0 <= lo iy / z0).
      { apply Z.div_le_lower_bound; [lia|]. lia. }
      lia.
Qed.

(* z-optimality (completeness) of the fden denominator table, positive-z case.
   Requires ix and iy nonempty (as the propagator guarantees); the incoming
   [ix] is quotient-tight ([ix] subset of [CxD iy iz]).  Then both returned
   z-bounds are attained by an actual solution. *)
Lemma fden_opt_pos : forall ix iy iz,
  0 < lo iz ->
  ileD ix (CxD iy iz) ->
  lo ix <= hi ix ->
  lo iy <= hi iy ->
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
  intros ix iy iz Hsign [Htlo Hthi] Hab Hcd.
  unfold CxD in Htlo, Hthi; cbn [lo hi] in Htlo, Hthi.
  unfold fden; cbv zeta.
  set (a := lo ix) in *. set (b := hi ix) in *.
  set (c := lo iy) in *. set (d := hi iy) in *.
  set (zl := lo iz) in *. set (zu := hi iz) in *.
  repeat (match goal with |- context[if ?bb then _ else _] => destruct bb eqn:? end;
          cbn iota).
  all: cbn [lo hi].
  all: intro Hne.
  all: repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    end.
  (* --- M0 x M0 --- *)
  1:{ split; (apply attain_pos2; [lia|lia|lia|nia|nia]). }
  (* --- P1 x P --- *)
  1:{ split.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (Z.max 1 c/(b+1)+1)); lia.
      + lia.
      + lia.
      + assert (Hz0 : Z.max zl (Z.max 1 c/(b+1)+1) <= d/a) by (apply Z.le_trans with (Z.min zu (d/a)); [exact Hne| apply Z.le_min_r]).
        assert (Hmd : a*(d/a) <= d) by (apply Z.mul_div_le; lia). nia.
      + assert (Ht : Z.max 1 c/(b+1)+1 <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_r.
        assert (Hsucc : Z.max 1 c < (b+1)*(Z.max 1 c/(b+1)+1)) by (apply Z.mul_succ_div_gt; lia).
        assert (Hcm : c <= Z.max 1 c) by apply Z.le_max_r. nia.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (Z.max 1 c/(b+1)+1)); lia.
      + lia.
      + lia.
      + assert (Hz0 : Z.min zu (d/a) <= d/a) by apply Z.le_min_r.
        assert (Hmd : a*(d/a) <= d) by (apply Z.mul_div_le; lia). nia.
      + assert (Ht : Z.max 1 c/(b+1)+1 <= Z.min zu (d/a)).
        { apply Z.le_trans with (Z.max zl (Z.max 1 c/(b+1)+1)); [apply Z.le_max_r|exact Hne]. }
        assert (Hsucc : Z.max 1 c < (b+1)*(Z.max 1 c/(b+1)+1)) by (apply Z.mul_succ_div_gt; lia).
        assert (Hcm : c <= Z.max 1 c) by apply Z.le_max_r. nia.
  }
  (* --- P1 x N (vacuous) --- *)
  1:{ exfalso.
    assert (Hzu : 0 < zu).
    { assert (zl <= Z.max zl (cdiv c a)) by apply Z.le_max_l.
      assert (Z.min zu (cdiv (Z.min (-1) d) (b+1) -1) <= zu) by apply Z.le_min_l. lia. }
    assert (HX : Xhi c d zl zu < 0).
    { unfold Xhi. repeat apply Z.max_lub_lt; apply Z.div_lt_upper_bound; lia. }
    lia. }
  (* --- P1 x M/Z --- *)
  1:{ assert (Hc0 : c <= 0).
    { destruct (Z_le_gt_dec c 0) as [|Hcg]; [assumption|].
      exfalso. assert (Hcon : ((0 <=? c) && (0 <? d))%bool = true).
      { apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      congruence. }
    assert (Hmd : a*(d/a) <= d) by (apply Z.mul_div_le; lia).
    split.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (cdiv c a)); lia.
      + lia.
      + lia.
      + assert (Z.max zl (cdiv c a) <= d/a) by (apply Z.le_trans with (Z.min zu (d/a)); [exact Hne|apply Z.le_min_r]). nia.
      + pose proof (Z.le_max_l zl (cdiv c a)). nia.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (cdiv c a)); lia.
      + lia.
      + lia.
      + assert (Z.min zu (d/a) <= d/a) by apply Z.le_min_r. nia.
      + assert (zl <= Z.min zu (d/a)) by (apply Z.le_trans with (Z.max zl (cdiv c a)); [apply Z.le_max_l|exact Hne]). nia.
  }
  (* --- N'1 x P (vacuous) --- *)
  1:{ exfalso.
    assert (Hzu : 0 < zu).
    { assert (zl <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_l.
      assert (Z.min zu (c/a) <= zu) by apply Z.le_min_l. lia. }
    assert (HX : 0 <= Xlo c d zl zu).
    { unfold Xlo. repeat apply Z.min_glb; apply Z.div_pos; lia. }
    lia. }
  (* --- N'1 x N --- *)
  1:{ clear Htlo Hthi.
    assert (Hb1 : b + 1 < 0) by lia.
    assert (Ha : a < 0) by lia.
    assert (Hcm : a * cdiv d a <= d).
    { unfold cdiv. pose proof (div_bracket_neg (-d) a ltac:(lia)) as [_ HB]. nia. }
    assert (Hclb : c < (b+1) * (cdiv c (b+1) - 1)).
    { unfold cdiv. pose proof (div_bracket_neg (-c) (b+1) ltac:(lia)) as [HB _]. nia. }
    split.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (cdiv d a)); lia.
      + lia.
      + lia.
      + assert (cdiv d a <= Z.max zl (cdiv d a)) by apply Z.le_max_r. clear Hclb. nia.
      + assert (Z.max zl (cdiv d a) <= cdiv c (b+1) - 1).
        { apply Z.le_trans with (Z.min zu (cdiv c (b+1)-1)); [exact Hne| apply Z.le_min_r]. } clear Hcm. nia.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (cdiv d a)); lia.
      + lia.
      + lia.
      + assert (cdiv d a <= Z.min zu (cdiv c (b+1)-1)).
        { apply Z.le_trans with (Z.max zl (cdiv d a)); [apply Z.le_max_r|exact Hne]. } clear Hclb. nia.
      + assert (Z.min zu (cdiv c (b+1)-1) <= cdiv c (b+1)-1) by apply Z.le_min_r. clear Hcm. nia.
  }
  (* --- N'1 x M/Z --- *)
  1:{ clear Htlo Hthi.
    assert (Hb1 : b+1<0) by lia.
    assert (Ha : a<0) by lia.
    assert (Hd0 : 0 <= d).
    { destruct (Z_le_gt_dec 0 d) as [|Hdg]; [assumption|]. exfalso.
      assert (((c <? 0) && (d <=? 0))%bool = true) by (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia). congruence. }
    assert (Hclb : c < (b+1)*(cdiv c (b+1) - 1)).
    { unfold cdiv. pose proof (div_bracket_neg (-c)(b+1) ltac:(lia)) as [HB _]. nia. }
    split.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (d/(b+1)+1)); lia.
      + lia.
      + lia.
      + pose proof (Z.le_max_l zl (d/(b+1)+1)). clear Hclb. nia.
      + assert (Z.max zl (d/(b+1)+1) <= cdiv c (b+1)-1).
        { apply Z.le_trans with (Z.min zu (cdiv c(b+1)-1)); [exact Hne|apply Z.le_min_r]. } nia.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (d/(b+1)+1)); lia.
      + lia.
      + lia.
      + assert (0 < Z.min zu (cdiv c (b+1)-1)).
        { pose proof (Z.le_max_l zl (d/(b+1)+1)); lia. } clear Hclb. nia.
      + assert (Z.min zu (cdiv c(b+1)-1) <= cdiv c(b+1)-1) by apply Z.le_min_r. nia.
  }
  (* --- Z (x=[0,0]) x (d<0) (vacuous) --- *)
  1:{ exfalso.
    assert (Hzu : 0 < zu).
    { assert (Z.min zu (d-1) <= zu) by apply Z.le_min_l. lia. }
    assert (HX : Xhi c d zl zu < 0).
    { unfold Xhi. repeat apply Z.max_lub_lt; apply Z.div_lt_upper_bound; lia. }
    lia. }
  (* --- Z (x=[0,0]) x (d>=0) --- *)
  1:{ clear Htlo Hthi. split.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (c+1)); lia.
      + lia.
      + lia.
      + nia.
      + pose proof (Z.le_max_r zl (c+1)); nia.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (c+1)); lia.
      + lia.
      + lia.
      + nia.
      + pose proof (Z.le_max_l zl (c+1)); nia.
  }
  (* --- N'0,O x N --- *)
  1:{ clear Htlo Hthi.
    assert (Ha : a < 0) by lia.
    assert (Hm : Z.min (-1) d <= d) by apply Z.le_min_r.
    assert (Hcm : a * cdiv (Z.min (-1) d) a <= Z.min (-1) d).
    { unfold cdiv. pose proof (div_bracket_neg (-(Z.min (-1) d)) a ltac:(lia)) as [_ HB]. nia. }
    split.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (cdiv (Z.min (-1) d) a)); lia.
      + lia.
      + lia.
      + assert (cdiv (Z.min (-1) d) a <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_r. nia.
      + nia.
    - apply attain_pos2.
      + assert (zl <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_l. lia.
      + lia.
      + lia.
      + assert (cdiv (Z.min (-1) d) a <= zu).
        { apply Z.le_trans with (Z.max zl (cdiv (Z.min (-1) d) a)); [apply Z.le_max_r|exact Hne]. } nia.
      + nia.
  }
  (* --- N'0,O x P (vacuous) --- *)
  1:{ exfalso.
    assert (Hzu : 0 < zu).
    { assert (Z.min zu (Z.max 1 c / a) <= zu) by apply Z.le_min_l. lia. }
    assert (HX : 0 <= Xlo c d zl zu).
    { unfold Xlo. repeat apply Z.min_glb; apply Z.div_pos; lia. }
    lia. }
  (* --- N'0,O x Z (bottom) --- *)
  1:{ exfalso; lia. }
  (* --- N'0,O x M --- *)
  1:{ clear Htlo Hthi.
    assert (Hd0 : 0 <= d).
    { destruct (Z_le_gt_dec 0 d) as [|Hg]; [assumption|]. exfalso.
      assert (((c <? 0) && (d <=? 0))%bool = true) by (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia). congruence. }
    assert (Hc : c < 0).
    { destruct (Z_lt_le_dec c 0) as [|Hg]; [assumption|]. exfalso.
      destruct (Z_lt_le_dec 0 d) as [Hd|Hd].
      - assert (((0 <? d) && (0 <=? c))%bool = true) by (apply andb_true_intro; split; [apply Z.ltb_lt|apply Z.leb_le]; lia). congruence.
      - assert (((c =? 0) && (d =? 0))%bool = true) by (apply andb_true_intro; split; apply Z.eqb_eq; lia). congruence. }
    split; (apply attain_pos2; [lia|lia|lia|nia|nia]).
  }
  (* --- P0 x N (vacuous) --- *)
  1:{ exfalso.
    assert (Hzu : 0 < zu).
    { assert (Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= zu) by apply Z.le_min_l. lia. }
    assert (HX : Xhi c d zl zu <= 0).
    { unfold Xhi. repeat apply Z.max_lub; apply Z.div_le_upper_bound; lia. }
    lia. }
  (* --- P0 x P --- *)
  1:{ clear Htlo Hthi.
    assert (Hsucc : Z.max 1 c < (b+1)*(Z.max 1 c/(b+1)+1)) by (apply Z.mul_succ_div_gt; lia).
    assert (Hcm : c <= Z.max 1 c) by apply Z.le_max_r.
    split.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (Z.max 1 c/(b+1)+1)); lia.
      + lia.
      + lia.
      + nia.
      + pose proof (Z.le_max_r zl (Z.max 1 c/(b+1)+1)). nia.
    - apply attain_pos2.
      + pose proof (Z.le_max_l zl (Z.max 1 c/(b+1)+1)); lia.
      + lia.
      + lia.
      + nia.
      + assert (Z.max 1 c/(b+1)+1 <= zu).
        { apply Z.le_trans with (Z.max zl (Z.max 1 c/(b+1)+1)); [apply Z.le_max_r|exact Hne]. } nia.
  }
  (* --- P0 x M --- *)
  1:{ clear Htlo Hthi.
    assert (Hd0 : 0<=d).
    { destruct (Z_le_gt_dec 0 d) as [|Hg];[assumption|]. exfalso.
      assert (((c<?0)&&(d<=?0))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia). congruence. }
    assert (Hc0 : c<=0).
    { destruct (Z_le_gt_dec c 0) as [|Hg];[assumption|]. exfalso.
      assert (((0<?d)&&(0<=?c))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia). congruence. }
    split; (apply attain_pos2; [lia|lia|lia|nia|nia]).
  }
  (* --- else (x straddles 0, y does not) (vacuous) --- *)
  exfalso.
  assert (Hbge : 0 <= b).
  { destruct (Z_le_gt_dec 0 b) as [|Hbg]; [assumption|].
    assert (((a <=? -1) && (b =? -1))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le; lia| apply Z.eqb_eq; lia]). congruence. }
  assert (Ha1 : a <= -1).
  { destruct (Z_le_gt_dec a (-1)) as [|Hag]; [assumption|].
    destruct (Z_le_gt_dec b 0) as [Hb0|Hbp].
    - assert (((a=?0)&&(b=?0))%bool=true) by (apply andb_true_intro; split; apply Z.eqb_eq; lia). congruence.
    - assert (((a=?0)&&(0<?b))%bool=true) by (apply andb_true_intro; split; [apply Z.eqb_eq; lia| apply Z.ltb_lt; lia]). congruence. }
  assert (Hzu : 0 < zu) by lia.
  destruct (Z_le_gt_dec c 0) as [Hcle|Hcgt].
  - assert (Hd : d < 0).
    { destruct (Z_le_gt_dec 0 d) as [Hd0|]; [|lia]. exfalso.
      assert (((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool=true).
      { apply andb_true_intro; split; [apply andb_true_intro; split; [apply andb_true_intro; split; apply Z.leb_le; lia| apply Z.leb_le; lia]| apply Z.leb_le; lia]. } congruence. }
    assert (HX : Xhi c d zl zu < 0).
    { unfold Xhi. repeat apply Z.max_lub_lt; apply Z.div_lt_upper_bound; lia. }
    lia.
  - assert (HX : 0 <= Xlo c d zl zu).
    { unfold Xlo. repeat apply Z.min_glb; apply Z.div_pos; lia. }
    lia.
Qed.
