From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase.
From LalaInterval Require Import optbase2.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma min_dup : forall a b, Z.min a (Z.min a b) = Z.min a b. Proof. intros; lia. Qed.
Lemma max_dup : forall a b, Z.max a (Z.max a b) = Z.max a b. Proof. intros; lia. Qed.

(* ================================================================= *)
(*  Core fden band facts (positive-divisor branch), mirroring        *)
(*  fden_opt_pos: for the refined divisor interval iz' = iz meet fden,*)
(*  the incoming x-corners lo ix / hi ix are compatible with y.       *)
(* ================================================================= *)
Lemma fden_ix_conds_pos : forall ix iy iz,
  0 < lo iz -> lo ix <= hi ix -> lo iy <= hi iy -> ile ix (Cx iy iz) ->
  lo (inter iz (fden ix iy iz)) <= hi (inter iz (fden ix iy iz)) ->
  lo ix * hi (inter iz (fden ix iy iz)) <= hi iy /\
  lo ix * lo (inter iz (fden ix iy iz)) <= hi iy /\
  lo iy <= (hi ix + 1) * hi (inter iz (fden ix iy iz)) - 1 /\
  lo iy <= (hi ix + 1) * lo (inter iz (fden ix iy iz)) - 1.
Proof.
  intros ix iy iz Hsign Hnx Hny Htight Hne.
  unfold ile, Cx in Htight. destruct Htight as [HtL HtU].
  unfold inter in Hne |- *. cbn [lo hi] in Hne |- *.
  unfold fden in *; cbv zeta in *.
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
  all: rewrite ?min_dup, ?max_dup, ?Z.min_id, ?Z.max_id in Hne |- *.
  all: set (a := lo ix) in *; set (b := hi ix) in *;
       set (c := lo iy) in *; set (d := hi iy) in *;
       set (zl := lo iz) in *; set (zu := hi iz) in *.
  - repeat split; nia.
  - assert (Hb1 : 0 < b + 1) by lia.
    assert (Hmd : a * (d / a) <= d) by (apply Z.mul_div_le; lia).
    assert (Hsucc : Z.max 1 c < (b+1) * (Z.max 1 c/(b+1)+1)) by (apply Z.mul_succ_div_gt; lia).
    assert (Hcmax : c <= Z.max 1 c) by apply Z.le_max_r.
    assert (HzlL : zl <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_l.
    assert (HTL : Z.max 1 c/(b+1)+1 <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_r.
    assert (HHd : Z.min zu (d/a) <= d/a) by apply Z.le_min_r.
    repeat split; nia.
  - exfalso.
    assert (Hdiv : 0 <= (-(Z.min (-1) d))/(b+1)) by (apply Z.div_pos; lia).
    assert (HcdivLe : cdiv (Z.min (-1) d) (b+1) <= 0) by (unfold cdiv; lia).
    assert (HHle : Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= cdiv (Z.min (-1) d) (b+1) - 1) by apply Z.le_min_r.
    assert (HzlL : zl <= Z.max zl (cdiv c a)) by apply Z.le_max_l.
    lia.
  - destruct (Z_le_gt_dec d 0) as [Hd|Hd].
    + exfalso.
      assert (Hda : d / a <= 0) by (rewrite <- (Z.div_0_l a) by lia; apply Z.div_le_mono; lia).
      assert (HH : Z.min zu (d/a) <= d/a) by apply Z.le_min_r.
      assert (HL : zl <= Z.max zl (cdiv c a)) by apply Z.le_max_l.
      lia.
    + assert (Hc : c < 0) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hc0]; [assumption|exfalso; assert (((0<=?c)&&(0<?d))%bool = true) by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia); congruence]).
      assert (Hmd : a*(d/a) <= d) by (apply Z.mul_div_le; lia).
      assert (HHd : Z.min zu (d/a) <= d/a) by apply Z.le_min_r.
      assert (HzlL : zl <= Z.max zl (cdiv c a)) by apply Z.le_max_l.
      repeat split; nia.
  - exfalso.
    assert (Hca : c / a <= 0) by (apply (fdiv_ub_neg c a 0); lia).
    assert (HH : Z.min zu (c/a) <= c/a) by apply Z.le_min_r.
    assert (HL : zl <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_l.
    lia.
  - assert (HdivL : cdiv d a <= Z.max zl (cdiv d a)) by apply Z.le_max_r.
    assert (HzlL : zl <= Z.max zl (cdiv d a)) by apply Z.le_max_l.
    assert (HdivH : Z.min zu (cdiv c (b+1) - 1) <= cdiv c (b+1) - 1) by apply Z.le_min_r.
    assert (Hbneg : b + 1 < 0) by lia. assert (Haneg : a < 0) by lia.
    assert (Haz : forall z, cdiv d a <= z -> a*z <= d) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-d) a ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-d) a Haneg) as B; set (q := (-d)/a) in *; nia).
    assert (Hcb : forall z, z + 1 <= cdiv c (b+1) -> c <= (b+1)*z - 1) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-c) (b+1) ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-c) (b+1) Hbneg) as B; set (q := (-c)/(b+1)) in *; nia).
    repeat split; [ apply Haz; lia | apply Haz; lia | apply Hcb; lia | apply Hcb; lia ].
  - destruct (Z_le_gt_dec d 0) as [Hd|Hd].
    + exfalso.
      assert (Hc0 : 0 <= c) by (destruct (Z_lt_le_dec c 0) as [Hcc|]; [exfalso; assert (((c<?0)&&(d<=?0))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence|assumption]).
      assert (Hpos : 0 <= (-c)/(b+1)) by (apply (fdiv_lb_neg (-c) (b+1) 0); lia).
      assert (HcdivH : cdiv c (b+1) <= 0) by (unfold cdiv; lia).
      assert (Hhi : Z.min zu (cdiv c (b+1) - 1) <= cdiv c (b+1) - 1) by apply Z.le_min_r.
      assert (Hlo : zl <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_l.
      lia.
    + assert (Hc : c < 0) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hc0]; [assumption|exfalso; assert (((0<=?c)&&(0<?d))%bool=true) by (apply andb_true_intro; split;[apply Z.leb_le|apply Z.ltb_lt];lia); congruence]).
      assert (Haneg : a < 0) by lia. assert (Hbneg : b + 1 < 0) by lia.
      assert (Hcb : forall z, z+1 <= cdiv c (b+1) -> c <= (b+1)*z-1) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-c)(b+1) ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-c)(b+1) Hbneg) as B; set (q:=(-c)/(b+1)) in *; nia).
      assert (HdivH : Z.min zu (cdiv c(b+1)-1) <= cdiv c(b+1)-1) by apply Z.le_min_r.
      assert (Hlo : zl <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_l.
      assert (HL0 : 0 < Z.max zl (d/(b+1)+1)) by lia.
      assert (HH0 : 0 < Z.min zu (cdiv c(b+1)-1)) by lia.
      repeat split; [ nia | nia | apply Hcb; lia | apply Hcb; lia ].
  - exfalso.
    assert (Hhi : Z.min zu (d-1) <= d-1) by apply Z.le_min_r.
    lia.
  - assert (HcL : c+1 <= Z.max zl (c+1)) by apply Z.le_max_r.
    assert (HzlL : zl <= Z.max zl (c+1)) by apply Z.le_max_l.
    repeat split; nia.
  - assert (Haneg : a < 0) by lia. assert (Hn : Z.min (-1) d <= d) by lia.
    assert (Haz : forall z, cdiv (Z.min (-1) d) a <= z -> a*z <= Z.min (-1) d) by (intros zz Hz; unfold cdiv in Hz; pose proof (Z.div_mod (-(Z.min (-1) d)) a ltac:(lia)) as D; pose proof (Z.mod_neg_bound (-(Z.min (-1) d)) a Haneg) as B; set (q:=(-(Z.min (-1) d))/a) in *; nia).
    assert (HdivL : cdiv (Z.min (-1) d) a <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_r.
    assert (HzlL : zl <= Z.max zl (cdiv (Z.min (-1) d) a)) by apply Z.le_max_l.
    repeat split.
    + apply Z.le_trans with (Z.min (-1) d); [apply Haz; lia | lia].
    + apply Z.le_trans with (Z.min (-1) d); [apply Haz; lia | lia].
    + nia.
    + nia.
  - exfalso.
    assert (Hmax : 1 <= Z.max 1 c) by apply Z.le_max_l.
    assert (Hca : Z.max 1 c / a <= 0) by (apply (fdiv_ub_neg (Z.max 1 c) a 0); lia).
    assert (HH : Z.min zu (Z.max 1 c / a) <= Z.max 1 c / a) by apply Z.le_min_r.
    lia.
  - exfalso. lia.
  - assert (Hd : 0 < d) by (destruct (Z_le_gt_dec d 0) as [Hd0|Hd1];[exfalso; assert (Hcpos:0<=c) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hcn];[exfalso; assert (((c<?0)&&(d<=?0))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence|lia]); assert (((c=?0)&&(d=?0))%bool=true) by (apply andb_true_intro; split; apply Z.eqb_eq; lia); congruence|lia]).
    assert (Hc : c < 0) by (destruct (Z_lt_le_dec c 0) as [Hcc|Hcn];[lia|exfalso; assert (((0<?d)&&(0<=?c))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence]).
    repeat split; nia.
  - exfalso.
    assert (Hdlt : d < 0) by (destruct (Z_le_gt_dec 0 d) as [Hd|Hd];[|lia]; exfalso; assert (E : ((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool = true) by (apply andb_true_intro; split;[apply andb_true_intro; split;[apply andb_true_intro; split|]|]; apply Z.leb_le; lia); congruence).
    assert (Hn : Z.min (-1) d <= -1) by lia.
    assert (Hdivnp : 0 <= (-(Z.min (-1) d))/(b+1)) by (apply Z.div_pos; lia).
    assert (Hcd : cdiv (Z.min (-1) d) (b+1) <= 0) by (unfold cdiv; lia).
    assert (Hhi : Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= cdiv (Z.min (-1) d) (b+1) - 1) by apply Z.le_min_r.
    lia.
  - assert (Hb1 : 0 < b+1) by lia.
    assert (Hsucc : Z.max 1 c < (b+1)*(Z.max 1 c/(b+1)+1)) by (apply Z.mul_succ_div_gt; lia).
    assert (Hcmax : c <= Z.max 1 c) by apply Z.le_max_r.
    assert (HzlL : zl <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_l.
    assert (HTL : Z.max 1 c/(b+1)+1 <= Z.max zl (Z.max 1 c/(b+1)+1)) by apply Z.le_max_r.
    repeat split; nia.
  - exfalso. destruct (Z_le_gt_dec c 0) as [Hc|Hc].
    + assert (Hd : d < 0) by (destruct (Z_le_gt_dec 0 d) as [Hd0|Hd1];[exfalso; assert (((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool=true) by (apply andb_true_intro; split;[apply andb_true_intro;split;[apply andb_true_intro;split|]|];apply Z.leb_le;lia); congruence|lia]).
      assert (((c<?0)&&(d<=?0))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia). congruence.
    + assert (Hd : d <= 0) by (destruct (Z_le_gt_dec d 0) as [Hd0|Hd1];[lia|exfalso; assert (((0<?d)&&(0<=?c))%bool=true) by (apply andb_true_intro; split;[apply Z.ltb_lt|apply Z.leb_le];lia); congruence]). lia.
  - exfalso.
    assert (Ha1 : a <= -1) by (destruct (Z.eq_dec a 0) as [Ha0|Han];[assert (Hble : b <= 0) by (destruct (Z_le_gt_dec b 0) as [Hb|Hb];[assumption|exfalso; assert (((a=?0)&&(0<?b))%bool=true) by (apply andb_true_intro; split;[apply Z.eqb_eq|apply Z.ltb_lt];lia); congruence]); assert (Hbne : b <> 0) by (intro Hb0; assert (((a=?0)&&(b=?0))%bool=true) by (apply andb_true_intro; split; apply Z.eqb_eq; lia); congruence); lia|lia]).
    assert (Hb0 : 0 <= b) by (destruct (Z_le_gt_dec 0 b) as [Hb|Hb];[assumption|exfalso; assert (((a<=?-1)&&(b=?-1))%bool=true) by (apply andb_true_intro; split;[apply Z.leb_le|apply Z.eqb_eq];lia); congruence]).
    assert (Hzu : 0 < zu) by lia.
    destruct (Z_le_gt_dec c 0) as [Hc|Hc].
    + assert (Hd : d < 0) by (destruct (Z_le_gt_dec 0 d) as [Hd0|Hd1];[exfalso; assert (((a<=?0)&&(0<=?b)&&(c<=?0)&&(0<=?d))%bool=true) by (apply andb_true_intro; split;[apply andb_true_intro;split;[apply andb_true_intro;split|]|];apply Z.leb_le;lia); congruence|lia]).
      assert (Hcorners : forall n m, n < 0 -> 0 < m -> n/m <= -1) by (intros n m Hn Hm; pose proof (Z.div_mod n m ltac:(lia)) as D; pose proof (Z.mod_pos_bound n m Hm) as B; nia).
      assert (HX : Xhi c d zl zu <= -1) by (unfold Xhi; repeat apply Z.max_lub; apply Hcorners; lia). lia.
    + assert (Hcorners : forall n m, 0 < n -> 0 < m -> 0 <= n/m) by (intros n m Hn Hm; apply Z.div_pos; lia).
      assert (HX : 0 <= Xlo c d zl zu) by (unfold Xlo; repeat apply Z.min_glb; apply Hcorners; lia). lia.
Qed.

(* ================================================================= *)
(*  Core fden band facts (negative-divisor branch).                  *)
(* ================================================================= *)
Lemma fden_ix_conds_neg : forall ix iy iz,
  hi iz < 0 -> lo ix <= hi ix -> lo iy <= hi iy -> ile ix (Cx iy iz) ->
  lo (inter iz (fden ix iy iz)) <= hi (inter iz (fden ix iy iz)) ->
  (hi ix + 1) * hi (inter iz (fden ix iy iz)) + 1 <= hi iy /\
  (hi ix + 1) * lo (inter iz (fden ix iy iz)) + 1 <= hi iy /\
  lo iy <= lo ix * hi (inter iz (fden ix iy iz)) /\
  lo iy <= lo ix * lo (inter iz (fden ix iy iz)).
Proof.
  intros ix iy iz Hsign Hnx Hny Htight Hne.
  unfold ile, Cx in Htight. destruct Htight as [HtL HtU].
  unfold Xlo, Xhi in HtL, HtU.
  unfold inter in Hne |- *. cbn [lo hi] in Hne |- *.
  unfold fden in *; cbv zeta in *.
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
  all: rewrite ?min_dup, ?max_dup, ?Z.min_id, ?Z.max_id in Hne |- *.
  all: set (a := lo ix) in *; set (b := hi ix) in *;
       set (c := lo iy) in *; set (d := hi iy) in *;
       set (zl := lo iz) in *; set (zu := hi iz) in *.
  all: try (exfalso; lia).
  - repeat split; nia.
  - exfalso.
    assert (Hb1: 0 < b + 1) by lia.
    assert (Hm: 0 <= Z.max 1 c) by (pose proof (Z.le_max_l 1 c); lia).
    assert (Hd: 0 <= Z.max 1 c / (b+1)) by (apply Z.div_pos; lia).
    pose proof (Z.le_max_r zl (Z.max 1 c / (b+1) + 1)).
    pose proof (Z.le_min_l zu (d / a)).
    lia.
  - assert (Ha: 0 < a) by lia.
    assert (Hb1: 0 < b+1) by lia.
    pose proof (Z.mul_div_le (-c) a Ha) as Bc.
    assert (Ec: a * cdiv c a >= c) by (unfold cdiv; nia).
    destruct (div_bracket_pos (-d) (b+1) Hb1) as [Bd1 Bd2].
    assert (Ed: (b+1)*(cdiv d (b+1) - 1) < d) by (unfold cdiv; nia).
    replace (Z.min (-1) d) with d in * by lia.
    assert (Uzu: Z.min zu (cdiv d (b + 1) - 1) <= zu) by apply Z.le_min_l.
    assert (Ucd: Z.min zu (cdiv d (b + 1) - 1) <= cdiv d (b + 1) - 1) by apply Z.le_min_r.
    assert (Lge: cdiv c a <= Z.max zl (cdiv c a)) by apply Z.le_max_r.
    clear HtL HtU Bc Bd1 Bd2.
    set (L := Z.max zl (cdiv c a)) in *.
    set (U := Z.min zu (cdiv d (b+1) - 1)) in *.
    assert (HzL: L < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * L) by (clear Ed Ucd Uzu HzU HzL; nia).
    assert (HLd: (b+1) * L < d) by (clear Ec Lge HLc HzL HzU Uzu; nia).
    assert (HUc: c <= a * U) by (clear Ed Ucd Uzu Lge HLd; nia).
    assert (HUd: (b+1) * U < d) by (clear Ec Lge HLc HLd HzL HUc; nia).
    repeat split; lia.
  - assert (Ha: 0 < a) by lia.
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
    clear HtL HtU Bc.
    set (L := Z.max zl (cdiv c a)) in *.
    set (U := Z.min zu (d/a)) in *.
    assert (HzL: L < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * L) by (clear Uzu HzU HzL Hd0; nia).
    assert (HLd: (b+1) * L < d) by (clear Ec Lge HLc Uzu; nia).
    assert (HUc: c <= a * U) by (clear Ec Lge Uzu HLd HzL; nia).
    assert (HUd: (b+1) * U < d) by (clear Ec Lge HLc HLd HUc HzL; nia).
    repeat split; lia.
  - assert (Ha: a < 0) by lia.
    assert (Hb1n: b + 1 < 0) by lia.
    destruct (div_bracket_neg c a Ha) as [Bca1 Bca2].
    destruct (div_bracket_neg d (b+1) Hb1n) as [Bdb1 Bdb2].
    assert (Lge: d/(b+1) + 1 <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_r.
    assert (Uc: Z.min zu (c/a) <= c/a) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (c/a) <= zu) by apply Z.le_min_l.
    clear HtL HtU Bca1 Bdb2.
    set (L := Z.max zl (d/(b+1)+1)) in *.
    set (U := Z.min zu (c/a)) in *.
    assert (HLca: L <= c/a) by lia.
    assert (HzL: L < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * L) by (clear Lge HzL HzU Uzu; nia).
    assert (HLd: (b+1) * L < d) by (clear Bca2 Uc HLca HLc HzL HzU Uzu; nia).
    assert (HUc: c <= a * U) by (clear Lge HLca HLd HzL HzU Bdb1 HLc; nia).
    assert (HUge: d/(b+1)+1 <= U) by lia.
    assert (HUd: (b+1) * U < d) by (clear Bca2 HLca Uc HLc HUc Lge HLd HzL HzU Uzu Hne; nia).
    repeat split; lia.
  - exfalso.
    assert (Hcd0: 0 <= cdiv d a) by (apply (cdiv_lb_neg d a 0); lia).
    pose proof (Z.le_max_r zl (cdiv d a)).
    pose proof (Z.le_min_l zu (cdiv c (b+1) - 1)).
    lia.
  - assert (Ha: a < 0) by lia.
    assert (Hb1n: b + 1 < 0) by lia.
    destruct (Z_lt_le_dec 0 d) as [Hd|Hd].
    + assert (Hc0: c < 0).
      { destruct (Z_le_gt_dec 0 c) as [Hc|]; [exfalso|lia].
        assert (((0<=?c)&&(0<?d))%bool = true) by
          (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        congruence. }
      destruct (div_bracket_neg d (b+1) Hb1n) as [Bdb1 Bdb2].
      assert (Lge: d/(b+1) + 1 <= Z.max zl (d/(b+1)+1)) by apply Z.le_max_r.
      assert (Uzu: Z.min zu (cdiv c (b+1) - 1) <= zu) by apply Z.le_min_l.
      clear HtL HtU Bdb2.
      set (L := Z.max zl (d/(b+1)+1)) in *.
      set (U := Z.min zu (cdiv c (b+1) - 1)) in *.
      assert (HzL: L < 0) by lia.
      assert (HzU: U < 0) by lia.
      assert (HUge: d/(b+1)+1 <= U) by lia.
      assert (HLd: (b+1) * L < d) by (clear Uzu; nia).
      assert (HUd: (b+1) * U < d) by (clear Uzu Lge HLd HzL; nia).
      assert (HLc: c <= a * L) by (clear Bdb1 Lge HUge HLd HUd Uzu HzU; nia).
      assert (HUc: c <= a * U) by (clear Bdb1 Lge HUge HLd HUd Uzu HzL HLc; nia).
      repeat split; lia.
    + exfalso.
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
      lia.
  - assert (HdN: d < 0) by lia.
    assert (Uub: Z.min zu (d-1) <= d - 1) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (d-1) <= zu) by apply Z.le_min_l.
    clear HtL HtU.
    set (U := Z.min zu (d-1)) in *.
    assert (HzL: zl < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * zl) by (clear Uub Uzu; nia).
    assert (HLd: (b+1) * zl < d) by (clear Uzu HzU; nia).
    assert (HUc: c <= a * U) by (clear Uub HLc HLd HzL; nia).
    assert (HUd: (b+1) * U < d) by (clear Uzu HzL HLc HLd HUc; nia).
    repeat split; lia.
  - exfalso.
    assert (Hmm: Z.min (-1) d <= -1) by apply Z.le_min_l.
    assert (Hc1: 1 <= cdiv (Z.min (-1) d) a) by (apply (cdiv_lb_neg (Z.min (-1) d) a 1); lia).
    pose proof (Z.le_max_r zl (cdiv (Z.min (-1) d) a)).
    lia.
  - assert (Ha: a < 0) by lia.
    destruct (div_bracket_neg (Z.max 1 c) a Ha) as [Bm1 Bm2].
    assert (Hmc: c <= Z.max 1 c) by apply Z.le_max_r.
    assert (Uc: Z.min zu (Z.max 1 c / a) <= Z.max 1 c / a) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (Z.max 1 c / a) <= zu) by apply Z.le_min_l.
    clear HtL HtU Bm1.
    set (U := Z.min zu (Z.max 1 c / a)) in *.
    assert (Hzlca: zl <= Z.max 1 c / a) by lia.
    assert (HzL: zl < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * zl) by (clear Uc Uzu; nia).
    assert (HLd: (b+1) * zl < d) by (clear Bm2 Hmc Uc Uzu Hzlca HzU HLc; nia).
    assert (HUc: c <= a * U) by (clear Uzu Hzlca HzL HLc HLd; nia).
    assert (HUd: (b+1) * U < d) by (clear Bm2 Hmc Uc Hzlca HzL HLc HLd HUc; nia).
    repeat split; lia.
  - assert (Hc: c < 0).
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
    clear HtL HtU.
    repeat split; nia.
  - assert (Hb1: 0 < b+1) by lia.
    assert (Hmd: Z.min (-1) d <= d) by apply Z.le_min_r.
    destruct (div_bracket_pos (-(Z.min (-1) d)) (b+1) Hb1) as [Bn1 Bn2].
    assert (Ed: (b+1)*(cdiv (Z.min (-1) d) (b+1) - 1) < Z.min (-1) d) by (unfold cdiv; nia).
    assert (Uub: Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= cdiv (Z.min (-1) d) (b+1) - 1) by apply Z.le_min_r.
    assert (Uzu: Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1) <= zu) by apply Z.le_min_l.
    clear HtL HtU Bn1 Bn2.
    set (U := Z.min zu (cdiv (Z.min (-1) d) (b+1) - 1)) in *.
    assert (HzL: zl < 0) by lia.
    assert (HzU: U < 0) by lia.
    assert (HLc: c <= a * zl) by (clear Ed Uub Hmd; nia).
    assert (HLd: (b+1)*zl < d) by (clear HzU HLc; nia).
    assert (HUc: c <= a * U) by (clear Ed HLc HLd HzL; nia).
    assert (HUd: (b+1)*U < d) by (clear Uzu HzL HLc HLd HUc; nia).
    repeat split; lia.
  - exfalso.
    assert (Hb1: 0 < b + 1) by lia.
    assert (Hm: 0 <= Z.max 1 c) by (pose proof (Z.le_max_l 1 c); lia).
    assert (Hd: 0 <= Z.max 1 c / (b+1)) by (apply Z.div_pos; lia).
    pose proof (Z.le_max_r zl (Z.max 1 c / (b+1) + 1)).
    lia.
  - exfalso.
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
    + assert (c/zl < 0) by (apply (fdiv_lt_neg c zl 0); lia).
      assert (c/zu < 0) by (apply (fdiv_lt_neg c zu 0); lia).
      assert (d/zl < 0) by (apply (fdiv_lt_neg d zl 0); lia).
      assert (d/zu < 0) by (apply (fdiv_lt_neg d zu 0); lia).
      assert (HX: Z.max (Z.max (c/zl) (c/zu)) (Z.max (d/zl) (d/zu)) < 0)
        by (repeat apply Z.max_lub_lt; lia).
      lia.
    + assert (Hd: d < 0).
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
      lia.
Qed.
