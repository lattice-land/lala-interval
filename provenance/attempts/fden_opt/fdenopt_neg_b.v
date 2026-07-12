From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Definition ileD (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.
Definition CxD (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).

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
  ileD ix (CxD iy iz) ->
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
  intros ix iy iz Hix Hiy Hsign Htight Hne.
  unfold ileD, CxD in Htight. cbn [lo hi] in Htight.
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
