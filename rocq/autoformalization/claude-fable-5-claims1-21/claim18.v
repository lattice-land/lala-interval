(* ========================================================================= *)
(* Claim 18:                                                                 *)
(* "Our propagator is strictly stronger than the one of Apt et al."          *)
(*                                                                           *)
(* We define the multiplication propagator I[**] of Apt et al. (appendix     *)
(* figure) and prove:                                                        *)
(*   (i)  dominance: for every store d, I[*](d) ⊑ I[**](d);                  *)
(*   (ii) strictness: for some store d, I[**](d) ⋢ I[*](d).                  *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical FunctionalExtensionality
  PropExtensionality.
From Paper Require Import claim1 claim2 claim3 claim4 claim8 claim9 claim10
  claim11 claim12 claim15 claim16 claim20 claim17.
Open Scope Z_scope.

(* ==================== Apt et al.'s propagator ==================== *)

Definition zneq0lo (a : Zinf) : Zinf := if zeqb a (Fin 0) then Fin 1 else a.
Definition zneq0hi (b : Zinf) : Zinf := if zeqb b (Fin 0) then Fin (-1) else b.
Definition ineqzero (i : Itv) : Itv := (zneq0lo (fst i), zneq0hi (snd i)).

Definition imulback (i j : Itv) : Itv :=
  if orb (zltb (Fin 0) (fst j)) (zltb (snd j) (Fin 0)) then
    (zmin (zmin (zcdiv (fst i) (fst j)) (zcdiv (fst i) (snd j)))
          (zmin (zcdiv (snd i) (fst j)) (zcdiv (snd i) (snd j))),
     zmax (zmax (zfdiv (fst i) (fst j)) (zfdiv (fst i) (snd j)))
          (zmax (zfdiv (snd i) (fst j)) (zfdiv (snd i) (snd j))))
  else if andb (andb (zltb (fst j) (Fin 0)) (zltb (Fin 0) (snd j)))
               (orb (zltb (Fin 0) (fst i)) (zltb (snd i) (Fin 0))) then
    (zmin (fst i) (zneg (snd i)), zmax (zneg (fst i)) (snd i))
  else (MInf, PInf).

(* The staged algorithm (x-update = the same first step as ours). *)
Definition aptZ1 (d : istore V3) : Itv :=
  if notin0b (mulX d) then imeet (d Vz) (ineqzero (d Vz)) else d Vz.
Definition aptY1 (d : istore V3) : Itv :=
  imeet (d Vy) (imulback (mulX d) (aptZ1 d)).
Definition aptY2 (d : istore V3) : Itv :=
  if notin0b (mulX d) then imeet (aptY1 d) (ineqzero (aptY1 d)) else aptY1 d.
Definition aptZ2 (d : istore V3) : Itv :=
  imeet (aptZ1 d) (imulback (mulX d) (aptY2 d)).

Definition prop_apt (d : istore V3) : istore V3 :=
  if isbotb (mulX d) then vupd d Vx (mulX d)
  else if isbotb (aptZ1 d) then
    vupd (vupd d Vx (mulX d)) Vz (aptZ1 d)
  else if isbotb (aptY1 d) then
    vupd (vupd (vupd d Vx (mulX d)) Vz (aptZ1 d)) Vy (aptY1 d)
  else if isbotb (aptY2 d) then
    vupd (vupd (vupd d Vx (mulX d)) Vz (aptZ1 d)) Vy (aptY2 d)
  else
    vupd (vupd (vupd d Vx (mulX d)) Vz (aptZ2 d)) Vy (aptY2 d).

(* ==================== Small order helpers ==================== *)

Lemma ile_trans : forall i j k, ile i j -> ile j k -> ile i k.
Proof.
  intros i j k [H1 H2] [H3 H4]. split; eapply zle_trans; eauto.
Qed.

Lemma ile_refl : forall i, ile i i.
Proof. intros i. split; apply zle_refl. Qed.

Lemma ile_meet : forall i j1 j2, ile i j1 -> ile i j2 -> ile i (imeet j1 j2).
Proof.
  intros i j1 j2 [H1 H2] [H3 H4]. split; cbn [imeet fst snd].
  - apply zmax_lub; assumption.
  - apply zmin_glb; assumption.
Qed.

Lemma imeet_le_l : forall i j, ile (imeet i j) i.
Proof. intros i j. split; cbn [imeet fst snd]; [apply zmax_ge_l | apply zmin_le_l]. Qed.

Lemma imeet_le_r : forall i j, ile (imeet i j) j.
Proof. intros i j. split; cbn [imeet fst snd]; [apply zmax_ge_r | apply zmin_le_r]. Qed.

Lemma ile_top : forall i, ile i (MInf, PInf).
Proof. intros i. split; cbn [fst snd]; [apply zle_minf | apply zle_pinf]. Qed.

(* Discreteness: strictly positive/negative Z∞ bounds. *)
Lemma zlt_0_ge1 : forall a, zlt (Fin 0) a -> zle (Fin 1) a.
Proof. intros [|x|] H; simpl in *; try tauto; lia. Qed.

Lemma zlt_0_leneg1 : forall a, zlt a (Fin 0) -> zle a (Fin (-1)).
Proof. intros [|x|] H; simpl in *; try tauto; lia. Qed.

Lemma notin0b_false_bounds : forall i,
  notin0b i = false -> zle (fst i) (Fin 0) /\ zle (Fin 0) (snd i).
Proof.
  intros i H. unfold notin0b in H.
  apply Bool.orb_false_iff in H. destruct H as [H1 H2].
  split; [apply zltb_false in H1 | apply zltb_false in H2]; assumption.
Qed.

Lemma notin0b_true_bounds : forall i,
  notin0b i = true -> zle (Fin 1) (fst i) \/ zle (snd i) (Fin (-1)).
Proof.
  intros i H. unfold notin0b in H.
  apply Bool.orb_true_iff in H. destruct H as [H|H].
  - left. apply zltb_lt in H. apply zlt_0_ge1. exact H.
  - right. apply zltb_lt in H. apply zlt_0_leneg1. exact H.
Qed.

(* Membership in a neqzero-clipped interval. *)
Lemma mem_ineqzero : forall (v : Z) i,
  imem v i -> v <> 0 -> imem v (ineqzero i).
Proof.
  intros v [l u] [H1 H2] Hv. unfold ineqzero. cbn [fst snd] in *.
  unfold zneq0lo, zneq0hi. split.
  - destruct (zeqb l (Fin 0)) eqn:E; [|exact H1].
    apply zeqb_eq in E. subst l. simpl in *. lia.
  - destruct (zeqb u (Fin 0)) eqn:E; [|exact H2].
    apply zeqb_eq in E. subst u. simpl in *. lia.
Qed.

(* O ⊑ ineqzero(i) from O ⊑ i plus strict-endpoint facts. *)
Lemma ile_ineqzero : forall o i,
  ile o i ->
  (fst i = Fin 0 -> zle (Fin 1) (fst o)) ->
  (snd i = Fin 0 -> zle (snd o) (Fin (-1))) ->
  ile o (ineqzero i).
Proof.
  intros o [l u] [H1 H2] Hlo Hhi. unfold ineqzero. cbn [fst snd] in *.
  unfold zneq0lo, zneq0hi. split.
  - destruct (zeqb l (Fin 0)) eqn:E; [|exact H1].
    apply zeqb_eq in E. apply Hlo. exact E.
  - destruct (zeqb u (Fin 0)) eqn:E; [|exact H2].
    apply zeqb_eq in E. apply Hhi. exact E.
Qed.

(* ==================== Bound estimates on best hulls ==================== *)

Lemma bestR_lb_ge : forall (R : powerset (Asn V3)) (d : istore V3) (w : V3) (b : Zinf),
  (forall a, ibox d a -> R a -> zle b (Fin (a w))) ->
  zle b (fst (bestR R d w)).
Proof.
  intros R d w b H. unfold bestR, ihull, alphai. cbn [fst].
  apply zinfS_greatest. intros x [v [[asn [[Hb HR] Hv]] Heq]]. subst.
  apply H; assumption.
Qed.

Lemma bestR_ub_le : forall (R : powerset (Asn V3)) (d : istore V3) (w : V3) (b : Zinf),
  (forall a, ibox d a -> R a -> zle (Fin (a w)) b) ->
  zle (snd (bestR R d w)) b.
Proof.
  intros R d w b H. unfold bestR, ihull, alphai. cbn [snd].
  apply zsup_least. intros x [v [[asn [[Hb HR] Hv]] Heq]]. subst.
  apply H; assumption.
Qed.

(* ==================== Integer division: abs bounds ==================== *)

Lemma fdivZ_abs : forall x z, z <> 0 -> - Z.abs x <= fdivZ x z <= Z.abs x.
Proof.
  intros x z Hz.
  destruct (Z_le_gt_dec 1 z) as [Hp|Hp].
  - split.
    + apply fdivZ_lb; [lia|]. nia.
    + apply fdivZ_ub; [lia|]. nia.
  - rewrite <- (fdivZ_opp_opp x z) by lia.
    assert (Hp' : 1 <= - z) by lia.
    split.
    + apply fdivZ_lb; [lia|]. nia.
    + apply fdivZ_ub; [lia|]. nia.
Qed.

Lemma cdivZ_abs : forall x z, z <> 0 -> - Z.abs x <= cdivZ x z <= Z.abs x.
Proof.
  intros x z Hz.
  pose proof (fdivZ_abs (- x) z Hz) as [H1 H2].
  rewrite cdivZ_as_fdiv.
  rewrite Z.abs_opp in *. lia.
Qed.

(* ==================== Integer division: monotonicity ==================== *)

Lemma cdivZ_mono_num : forall x x' z, 1 <= z -> x <= x' -> cdivZ x z <= cdivZ x' z.
Proof.
  intros x x' z Hz H.
  rewrite !cdivZ_as_fdiv.
  pose proof (fdivZ_mono_num (- x') (- x) z Hz ltac:(lia)). lia.
Qed.

Lemma cdivZ_anti_num_neg : forall x x' z, z <= -1 -> x <= x' -> cdivZ x' z <= cdivZ x z.
Proof.
  intros x x' z Hz H.
  rewrite (cdivZ_opp x z) by lia. rewrite (cdivZ_opp x' z) by lia.
  pose proof (fdivZ_mono_num x x' (- z) ltac:(lia) H). lia.
Qed.

Lemma fdivZ_anti_num_neg : forall x x' z, z <= -1 -> x <= x' -> fdivZ x' z <= fdivZ x z.
Proof.
  intros x x' z Hz H.
  rewrite <- (fdivZ_opp_opp x z) by lia. rewrite <- (fdivZ_opp_opp x' z) by lia.
  apply fdivZ_mono_num; lia.
Qed.

(* Divisor-direction monotonicity on negative divisors. *)
Lemma cdivZ_negdiv_anti_pos : forall y q r,
  0 <= y -> q <= r <= -1 -> cdivZ y r <= cdivZ y q.
Proof.
  intros y q r Hy Hq.
  rewrite (cdivZ_opp y q) by lia. rewrite (cdivZ_opp y r) by lia.
  pose proof (fdivZ_antitone_div y (- r) (- q) Hy ltac:(lia)). lia.
Qed.

Lemma cdivZ_negdiv_mono_neg : forall y q r,
  y < 0 -> q <= r <= -1 -> cdivZ y q <= cdivZ y r.
Proof.
  intros y q r Hy Hq.
  rewrite (cdivZ_opp y q) by lia. rewrite (cdivZ_opp y r) by lia.
  pose proof (fdivZ_monotone_div_neg y (- r) (- q) Hy ltac:(lia)). lia.
Qed.

Lemma fdivZ_negdiv_anti_pos : forall y q r,
  0 <= y -> q <= r <= -1 -> fdivZ y r <= fdivZ y q.
Proof.
  intros y q r Hy Hq.
  destruct (Z.eq_dec y 0) as [->|Hy0].
  - rewrite !fdivZ_zero_num by lia. lia.
  - rewrite <- (fdivZ_opp_opp y q) by lia. rewrite <- (fdivZ_opp_opp y r) by lia.
    pose proof (fdivZ_monotone_div_neg (- y) (- r) (- q) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fdivZ_negdiv_mono_neg : forall y q r,
  y < 0 -> q <= r <= -1 -> fdivZ y q <= fdivZ y r.
Proof.
  intros y q r Hy Hq.
  rewrite <- (fdivZ_opp_opp y q) by lia. rewrite <- (fdivZ_opp_opp y r) by lia.
  pose proof (fdivZ_antitone_div (- y) (- r) (- q) ltac:(lia) ltac:(lia)). lia.
Qed.

(* Sign facts. *)
Lemma cdivZ_negnum_negdiv_pos : forall y z, y < 0 -> z <= -1 -> 1 <= cdivZ y z.
Proof.
  intros y z Hy Hz.
  rewrite (cdivZ_opp y z) by lia.
  assert (fdivZ y (- z) <= -1) by (apply fdivZ_ub; [lia | nia]). lia.
Qed.

Lemma fdivZ_posnum_negdiv_neg : forall y z, 0 < y -> z <= -1 -> fdivZ y z <= -1.
Proof.
  intros y z Hy Hz.
  rewrite <- (fdivZ_opp_opp y z) by lia.
  apply fdivZ_ub; [lia | nia].
Qed.

(* ==================== Z∞ division: normal forms ==================== *)

Lemma zcdiv_minf_negfin : forall c : Z, c < 0 -> zcdiv MInf (Fin c) = PInf.
Proof.
  intros c Hc. unfold zcdiv. simpl.
  destruct (0 <? c) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

Lemma zcdiv_pinf_negfin : forall c : Z, c < 0 -> zcdiv PInf (Fin c) = MInf.
Proof.
  intros c Hc. unfold zcdiv. simpl.
  destruct (0 <? c) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

Lemma zfdiv_minf_negfin : forall c : Z, c < 0 -> zfdiv MInf (Fin c) = PInf.
Proof.
  intros c Hc. simpl.
  destruct (0 <? c) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

Lemma zfdiv_pinf_negfin : forall c : Z, c < 0 -> zfdiv PInf (Fin c) = MInf.
Proof.
  intros c Hc. simpl.
  destruct (0 <? c) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

Lemma zcdiv_fin_fin : forall a c : Z, zcdiv (Fin a) (Fin c) = Fin (cdivZ a c).
Proof. reflexivity. Qed.

(* ==================== Z∞ division: numerator monotonicity ==================== *)

Lemma zcdiv_mono_num_z : forall w w' v,
  zle (Fin 1) v -> zle w w' -> zle (zcdiv w v) (zcdiv w' v).
Proof.
  intros w w' v Hv H. unfold zcdiv.
  apply zneg_antitone. apply zfdiv_mono_y; [exact Hv | apply zneg_antitone; exact H].
Qed.

Lemma zcdiv_anti_num_neg_z : forall w w' v,
  zle v (Fin (-1)) -> zle w w' -> zle (zcdiv w' v) (zcdiv w v).
Proof.
  intros w w' [|c|] Hv H; simpl in Hv; [| | contradiction].
  - (* v = MInf *)
    destruct w as [|a|]; destruct w' as [|b|]; simpl in H; try contradiction;
      unfold zcdiv; simpl;
      try (destruct (0 <? - a) eqn:Ea);
      try (destruct (0 <? - b) eqn:Eb);
      simpl;
      repeat match goal with
      | E : (_ <? _) = true |- _ => apply Z.ltb_lt in E
      | E : (_ <? _) = false |- _ => apply Z.ltb_ge in E
      end; try exact I; try lia.
  - (* v = Fin c with c <= -1 *)
    destruct w as [|a|]; destruct w' as [|b|]; simpl in H; try contradiction.
    + rewrite zcdiv_minf_negfin by lia. apply zle_pinf.
    + rewrite zcdiv_minf_negfin by lia. apply zle_pinf.
    + rewrite zcdiv_minf_negfin by lia. apply zle_pinf.
    + rewrite !zcdiv_fin_fin. simpl.
      apply cdivZ_anti_num_neg; lia.
    + rewrite zcdiv_pinf_negfin by lia. apply zle_minf.
    + rewrite zcdiv_pinf_negfin by lia. apply zle_minf.
Qed.

Lemma zfdiv_anti_num_neg_z : forall w w' v,
  zle v (Fin (-1)) -> zle w w' -> zle (zfdiv w' v) (zfdiv w v).
Proof.
  intros w w' [|c|] Hv H; simpl in Hv; [| | contradiction].
  - destruct w as [|a|]; destruct w' as [|b|]; simpl in H; try contradiction;
      simpl;
      try (destruct (0 <? a) eqn:Ea);
      try (destruct (0 <? b) eqn:Eb);
      simpl;
      repeat match goal with
      | E : (_ <? _) = true |- _ => apply Z.ltb_lt in E
      | E : (_ <? _) = false |- _ => apply Z.ltb_ge in E
      end; try exact I; try lia.
  - destruct w as [|a|]; destruct w' as [|b|]; simpl in H; try contradiction.
    + rewrite zfdiv_minf_negfin by lia. apply zle_pinf.
    + rewrite zfdiv_minf_negfin by lia. apply zle_pinf.
    + rewrite zfdiv_minf_negfin by lia. apply zle_pinf.
    + simpl. apply fdivZ_anti_num_neg; lia.
    + rewrite zfdiv_pinf_negfin by lia. apply zle_minf.
    + rewrite zfdiv_pinf_negfin by lia. apply zle_minf.
Qed.

(* ==================== Corner lemmas: single numerator ==================== *)

Lemma zmin_neg : forall a b, zmin (zneg a) (zneg b) = zneg (zmax a b).
Proof.
  intros a b.
  destruct (zmax_case a b) as [[E H]|[E H]]; rewrite E;
    destruct (zmin_case (zneg a) (zneg b)) as [[E2 H2]|[E2 H2]]; rewrite E2;
    try reflexivity.
  - apply zle_antisym; [exact H2 | apply zneg_antitone; exact H].
  - apply zle_antisym; [exact H2 | apply zneg_antitone; exact H].
Qed.

Lemma zcdiv_corner_lb_pos : forall (y : Z) zl zu (z : Z),
  1 <= z -> zle (Fin 1) zl -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (zmin (zcdiv (Fin y) zl) (zcdiv (Fin y) zu)) (Fin (cdivZ y z)).
Proof.
  intros y zl zu z Hz H0 H1 H2.
  change (zcdiv (Fin y) zl) with (zneg (zfdiv (Fin (- y)) zl)).
  change (zcdiv (Fin y) zu) with (zneg (zfdiv (Fin (- y)) zu)).
  rewrite zmin_neg.
  change (Fin (cdivZ y z)) with (zneg (Fin (fdivZ (- y) z))).
  apply zneg_antitone.
  apply zfdiv_corner_ub; assumption.
Qed.

Lemma zcdiv_corner_lb_neg : forall (y : Z) zl zu (z : Z),
  z <= -1 -> zle zu (Fin (-1)) -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (zmin (zcdiv (Fin y) zl) (zcdiv (Fin y) zu)) (Fin (cdivZ y z)).
Proof.
  intros y [|l|] [|u|] z Hz Hu H1 H2; simpl in Hu, H1, H2; try contradiction.
  - (* zl = -inf, zu = Fin u *)
    destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [apply zmin_le_r|].
      rewrite zcdiv_fin_fin. simpl.
      apply cdivZ_negdiv_anti_pos; lia.
    + eapply zle_trans; [apply zmin_le_l|].
      unfold zcdiv. simpl.
      destruct (0 <? - y) eqn:E; [|apply Z.ltb_ge in E; lia].
      simpl. apply cdivZ_negnum_negdiv_pos; lia.
  - (* zl = Fin l, zu = Fin u *)
    destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [apply zmin_le_r|].
      rewrite zcdiv_fin_fin. simpl.
      apply cdivZ_negdiv_anti_pos; lia.
    + eapply zle_trans; [apply zmin_le_l|].
      rewrite zcdiv_fin_fin. simpl.
      apply cdivZ_negdiv_mono_neg; lia.
Qed.

Lemma zfdiv_corner_ub_neg : forall (y : Z) zl zu (z : Z),
  z <= -1 -> zle zu (Fin (-1)) -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (Fin (fdivZ y z)) (zmax (zfdiv (Fin y) zl) (zfdiv (Fin y) zu)).
Proof.
  intros y [|l|] [|u|] z Hz Hu H1 H2; simpl in Hu, H1, H2; try contradiction.
  - (* zl = -inf, zu = Fin u *)
    destruct (Z.lt_trichotomy 0 y) as [Hy|[Hy|Hy]].
    + eapply zle_trans; [|apply zmax_ge_l].
      simpl. destruct (0 <? y) eqn:E; [|apply Z.ltb_ge in E; lia].
      simpl. apply fdivZ_posnum_negdiv_neg; lia.
    + subst y. eapply zle_trans; [|apply zmax_ge_l].
      simpl. destruct (0 <? 0) eqn:E; [discriminate|].
      simpl. rewrite fdivZ_zero_num by lia. lia.
    + eapply zle_trans; [|apply zmax_ge_r].
      simpl. apply fdivZ_negdiv_mono_neg; lia.
  - (* zl = Fin l, zu = Fin u *)
    destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [|apply zmax_ge_l].
      simpl. apply fdivZ_negdiv_anti_pos; lia.
    + eapply zle_trans; [|apply zmax_ge_r].
      simpl. apply fdivZ_negdiv_mono_neg; lia.
Qed.

(* ==================== Corner bounds for imulback ==================== *)

(* Case 1 (sign-definite divisor): the lower bound of imulback is below
   every exact ceiling-division value over the box. *)
Lemma imulback_case1_lb : forall (Xi Zi : Itv) (xv zv : Z),
  orb (zltb (Fin 0) (fst Zi)) (zltb (snd Zi) (Fin 0)) = true ->
  zle (fst Xi) (Fin xv) -> zle (Fin xv) (snd Xi) ->
  zle (fst Zi) (Fin zv) -> zle (Fin zv) (snd Zi) ->
  zle (fst (imulback Xi Zi)) (Fin (cdivZ xv zv)).
Proof.
  intros Xi Zi xv zv Hsd Hx1 Hx2 Hz1 Hz2.
  unfold imulback. rewrite Hsd. cbn [fst].
  apply Bool.orb_true_iff in Hsd. destruct Hsd as [Hp|Hn].
  - (* positive divisor box *)
    apply zltb_lt in Hp. apply zlt_0_ge1 in Hp.
    assert (Hzv : 1 <= zv).
    { assert (Hc : zle (Fin 1) (Fin zv))
        by (eapply zle_trans; [exact Hp | exact Hz1]).
      simpl in Hc. lia. }
    assert (Hsnd : zle (Fin 1) (snd Zi)).
    { eapply zle_trans; [exact Hp|].
      eapply zle_trans; [exact Hz1 | exact Hz2]. }
    apply zle_trans with (b := zmin (zcdiv (Fin xv) (fst Zi))
                                    (zcdiv (Fin xv) (snd Zi))).
    + apply zmin_glb.
      * eapply zle_trans;
          [eapply zle_trans; [apply zmin_le_l | apply zmin_le_l]|].
        apply zcdiv_mono_num_z; [exact Hp | exact Hx1].
      * eapply zle_trans;
          [eapply zle_trans; [apply zmin_le_l | apply zmin_le_r]|].
        apply zcdiv_mono_num_z; [exact Hsnd | exact Hx1].
    + apply zcdiv_corner_lb_pos; assumption.
  - (* negative divisor box *)
    apply zltb_lt in Hn. apply zlt_0_leneg1 in Hn.
    assert (Hzv : zv <= -1).
    { assert (Hc : zle (Fin zv) (Fin (-1)))
        by (eapply zle_trans; [exact Hz2 | exact Hn]).
      simpl in Hc. lia. }
    assert (Hfst : zle (fst Zi) (Fin (-1))).
    { eapply zle_trans; [exact Hz1|].
      eapply zle_trans; [exact Hz2 | exact Hn]. }
    apply zle_trans with (b := zmin (zcdiv (Fin xv) (fst Zi))
                                    (zcdiv (Fin xv) (snd Zi))).
    + apply zmin_glb.
      * eapply zle_trans;
          [eapply zle_trans; [apply zmin_le_r | apply zmin_le_l]|].
        apply zcdiv_anti_num_neg_z; [exact Hfst | exact Hx2].
      * eapply zle_trans;
          [eapply zle_trans; [apply zmin_le_r | apply zmin_le_r]|].
        apply zcdiv_anti_num_neg_z; [exact Hn | exact Hx2].
    + apply zcdiv_corner_lb_neg; assumption.
Qed.

(* Case 1: the upper bound of imulback is above every exact floor-division
   value over the box. *)
Lemma imulback_case1_ub : forall (Xi Zi : Itv) (xv zv : Z),
  orb (zltb (Fin 0) (fst Zi)) (zltb (snd Zi) (Fin 0)) = true ->
  zle (fst Xi) (Fin xv) -> zle (Fin xv) (snd Xi) ->
  zle (fst Zi) (Fin zv) -> zle (Fin zv) (snd Zi) ->
  zle (Fin (fdivZ xv zv)) (snd (imulback Xi Zi)).
Proof.
  intros Xi Zi xv zv Hsd Hx1 Hx2 Hz1 Hz2.
  unfold imulback. rewrite Hsd. cbn [snd].
  apply Bool.orb_true_iff in Hsd. destruct Hsd as [Hp|Hn].
  - apply zltb_lt in Hp. apply zlt_0_ge1 in Hp.
    assert (Hzv : 1 <= zv).
    { assert (Hc : zle (Fin 1) (Fin zv))
        by (eapply zle_trans; [exact Hp | exact Hz1]).
      simpl in Hc. lia. }
    assert (Hsnd : zle (Fin 1) (snd Zi)).
    { eapply zle_trans; [exact Hp|].
      eapply zle_trans; [exact Hz1 | exact Hz2]. }
    apply zle_trans with (b := zmax (zfdiv (Fin xv) (fst Zi))
                                    (zfdiv (Fin xv) (snd Zi))).
    + apply zfdiv_corner_ub; assumption.
    + apply zmax_lub.
      * eapply zle_trans;
          [apply zfdiv_mono_y; [exact Hp | exact Hx2] |].
        eapply zle_trans; [apply zmax_ge_l | apply zmax_ge_r].
      * eapply zle_trans;
          [apply zfdiv_mono_y; [exact Hsnd | exact Hx2] |].
        eapply zle_trans; [apply zmax_ge_r | apply zmax_ge_r].
  - apply zltb_lt in Hn. apply zlt_0_leneg1 in Hn.
    assert (Hzv : zv <= -1).
    { assert (Hc : zle (Fin zv) (Fin (-1)))
        by (eapply zle_trans; [exact Hz2 | exact Hn]).
      simpl in Hc. lia. }
    assert (Hfst : zle (fst Zi) (Fin (-1))).
    { eapply zle_trans; [exact Hz1|].
      eapply zle_trans; [exact Hz2 | exact Hn]. }
    apply zle_trans with (b := zmax (zfdiv (Fin xv) (fst Zi))
                                    (zfdiv (Fin xv) (snd Zi))).
    + apply zfdiv_corner_ub_neg; assumption.
    + apply zmax_lub.
      * eapply zle_trans;
          [apply zfdiv_anti_num_neg_z; [exact Hfst | exact Hx1] |].
        eapply zle_trans; [apply zmax_ge_l | apply zmax_ge_l].
      * eapply zle_trans;
          [apply zfdiv_anti_num_neg_z; [exact Hn | exact Hx1] |].
        eapply zle_trans; [apply zmax_ge_r | apply zmax_ge_l].
Qed.

(* Case 2 (mixed divisor, 0 ∉ x): the |y| ≤ |x| window. *)
Lemma case2_fst : forall (Xi : Itv) (v xv : Z),
  zle (fst Xi) (Fin xv) -> zle (Fin xv) (snd Xi) ->
  - Z.abs xv <= v ->
  zle (zmin (fst Xi) (zneg (snd Xi))) (Fin v).
Proof.
  intros Xi v xv Hx1 Hx2 Hv.
  destruct (Z_le_gt_dec 0 xv) as [Hxv|Hxv].
  - eapply zle_trans; [apply zmin_le_r|].
    apply zle_trans with (b := Fin (- xv)).
    + change (Fin (- xv)) with (zneg (Fin xv)). apply zneg_antitone. exact Hx2.
    + simpl. lia.
  - eapply zle_trans; [apply zmin_le_l|].
    apply zle_trans with (b := Fin xv); [exact Hx1|].
    simpl. lia.
Qed.

Lemma case2_snd : forall (Xi : Itv) (v xv : Z),
  zle (fst Xi) (Fin xv) -> zle (Fin xv) (snd Xi) ->
  v <= Z.abs xv ->
  zle (Fin v) (zmax (zneg (fst Xi)) (snd Xi)).
Proof.
  intros Xi v xv Hx1 Hx2 Hv.
  destruct (Z_le_gt_dec 0 xv) as [Hxv|Hxv].
  - eapply zle_trans; [|apply zmax_ge_r].
    apply zle_trans with (b := Fin xv); [|exact Hx2].
    simpl. lia.
  - eapply zle_trans; [|apply zmax_ge_l].
    apply zle_trans with (b := Fin (- xv)).
    + simpl. lia.
    + change (Fin (- xv)) with (zneg (Fin xv)). apply zneg_antitone. exact Hx1.
Qed.

(* ==================== Dominance: I[*] ⊑ I[**] ==================== *)

Lemma leI_pt : forall (a b : istore V3),
  leI V3 a b -> ~ isbotI V3 a -> forall w, ile (a w) (b w).
Proof.
  intros a b [Hb|Hpt] Hnb w; [contradiction|].
  destruct (Hpt w) as [Hw|Hw]; [|exact Hw].
  exfalso. apply Hnb. exists w. exact Hw.
Qed.

Lemma nb_of_le : forall (a b : istore V3),
  leI V3 a b -> ~ isbotI V3 a -> ~ isbotI V3 b.
Proof. intros a b Hle Hnb Hb. exact (Hnb (leI_bot_out a b Hle Hb)). Qed.

Lemma leI_refl3 : forall a : istore V3, leI V3 a a.
Proof. intros a. right. intros w. apply isle_refl. Qed.

Section Dominance.
  Variable d : istore V3.
  Hypothesis HOnb : ~ isbotI V3 (prop_mul d).

  Lemma Onb_comp : forall w, ~ isbot (prop_mul d w).
  Proof. intros w Hw. apply HOnb. exists w. exact Hw. Qed.

  Lemma EmulX : isbotb (mulX d) = false.
  Proof.
    destruct (isbotb (mulX d)) eqn:E; [|reflexivity].
    exfalso. apply (Onb_comp Vx).
    rewrite (prop_mul_eq1 d E). rewrite vupd_same.
    apply isbotb_isbot. exact E.
  Qed.

  Lemma mulD1_Vx : mulD1 d Vx = mulX d.
  Proof. unfold mulD1. apply vupd_same. Qed.

  Lemma mulD1_Vy : mulD1 d Vy = d Vy.
  Proof. unfold mulD1. apply vupd_other. congruence. Qed.

  Lemma mulD1_Vz : mulD1 d Vz = d Vz.
  Proof. unfold mulD1. apply vupd_other. congruence. Qed.

  (* ⊑-chain through our propagator's stages. *)
  Lemma O_le_D2 : leI V3 (prop_mul d) (mulD2 d).
  Proof.
    rewrite (prop_mul_eq2 d EmulX).
    destruct (orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy))).
    - eapply leI_trans.
      + apply (prop_step_reductive Rfdiv_z Pfdiv_z Pfdiv_z_best).
      + apply (prop_step_reductive Rcdiv_z Pcdiv_z Pcdiv_z_best).
    - apply leI_refl3.
  Qed.

  Lemma D2_le_D1 : leI V3 (mulD2 d) (mulD1 d).
  Proof.
    rewrite (mulD2_eq d).
    destruct (orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz))).
    - eapply leI_trans.
      + apply (prop_step_reductive Rfdiv_y Pfdiv_y Pfdiv_y_best).
      + apply (prop_step_reductive Rcdiv_y Pcdiv_y Pcdiv_y_best).
    - apply leI_refl3.
  Qed.

  Lemma HnbD2 : ~ isbotI V3 (mulD2 d).
  Proof. exact (nb_of_le _ _ O_le_D2 HOnb). Qed.

  Lemma O_pt_D2 : forall w, ile (prop_mul d w) (mulD2 d w).
  Proof. exact (leI_pt _ _ O_le_D2 HOnb). Qed.

  Lemma D2_pt_D1 : forall w, ile (mulD2 d w) (mulD1 d w).
  Proof. exact (leI_pt _ _ D2_le_D1 HnbD2). Qed.

  Lemma O_pt_d : forall w, ile (prop_mul d w) (d w).
  Proof. exact (leI_pt _ _ (claim17_reductive d) HOnb). Qed.

  Lemma D2_pt_d : forall w, ile (mulD2 d w) (d w).
  Proof. exact (leI_pt _ _ (mulD2_reductive d) HnbD2). Qed.

  (* Our x-component is below Apt's x-component. *)
  Lemma O_x_ob : ile (prop_mul d Vx) (mulX d).
  Proof.
    eapply ile_trans; [apply O_pt_D2|].
    eapply ile_trans; [apply D2_pt_D1|].
    rewrite mulD1_Vx. apply ile_refl.
  Qed.

  Lemma D2_x_ob : ile (mulD2 d Vx) (mulX d).
  Proof.
    eapply ile_trans; [apply D2_pt_D1|].
    rewrite mulD1_Vx. apply ile_refl.
  Qed.

  (* ----- the y-block stages, available when its guard fired ----- *)

  Lemma O_le_S1 :
    orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true ->
    leI V3 (prop_mul d) (Pcdiv_y (mulD1 d)).
  Proof.
    intros Hg1. eapply leI_trans; [apply O_le_D2|].
    rewrite (mulD2_eq d), Hg1.
    apply (prop_step_reductive Rfdiv_y Pfdiv_y Pfdiv_y_best).
  Qed.

  Lemma D2_le_S1 :
    orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true ->
    leI V3 (mulD2 d) (Pcdiv_y (mulD1 d)).
  Proof.
    intros Hg1. rewrite (mulD2_eq d), Hg1.
    apply (prop_step_reductive Rfdiv_y Pfdiv_y Pfdiv_y_best).
  Qed.

  Lemma S1_pt :
    orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true ->
    forall w, Pcdiv_y (mulD1 d) w = bestR Rcdiv_y (mulD1 d) w.
  Proof.
    intros Hg1. apply eqI_nonbot_pointwise.
    - exact (nb_of_le _ _ (O_le_S1 Hg1) HOnb).
    - apply Pcdiv_y_best.
  Qed.

  Lemma O_pt_S1 :
    orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true ->
    forall w, ile (prop_mul d w) (Pcdiv_y (mulD1 d) w).
  Proof. intros Hg1. exact (leI_pt _ _ (O_le_S1 Hg1) HOnb). Qed.

  Lemma D2_pt_S1 :
    orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true ->
    forall w, ile (mulD2 d w) (Pcdiv_y (mulD1 d) w).
  Proof. intros Hg1. exact (leI_pt _ _ (D2_le_S1 Hg1) HnbD2). Qed.

  Lemma S1_pt_D1 :
    orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true ->
    forall w, ile (Pcdiv_y (mulD1 d) w) (mulD1 d w).
  Proof.
    intros Hg1.
    apply (leI_pt _ _ (prop_step_reductive Rcdiv_y Pcdiv_y Pcdiv_y_best (mulD1 d))).
    exact (nb_of_le _ _ (O_le_S1 Hg1) HOnb).
  Qed.

  Lemma D2_pt_best :
    orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true ->
    forall w, mulD2 d w = bestR Rfdiv_y (Pcdiv_y (mulD1 d)) w.
  Proof.
    intros Hg1 w.
    assert (E : mulD2 d = Pfdiv_y (Pcdiv_y (mulD1 d)))
      by (rewrite (mulD2_eq d), Hg1; reflexivity).
    rewrite E. apply eqI_nonbot_pointwise.
    - rewrite <- E. exact HnbD2.
    - apply Pfdiv_y_best.
  Qed.

  (* Solutions' z-values enter the (possibly clipped) Apt z-interval. *)
  Lemma sol_z_in_aptZ1 : forall v : Z,
    imem v (d Vz) -> v <> 0 -> imem v (aptZ1 d).
  Proof.
    intros v Hm Hv. unfold aptZ1.
    destruct (notin0b (mulX d)).
    - apply imem_imeet. split; [exact Hm | apply mem_ineqzero; assumption].
    - exact Hm.
  Qed.

  (* ----- Obligation: O(z) is below Apt's clipped z-interval ----- *)

  Lemma O_z1_ob : ile (prop_mul d Vz) (aptZ1 d).
  Proof.
    unfold aptZ1. destruct (notin0b (mulX d)) eqn:EnX; [|apply O_pt_d].
    assert (Hg1 : orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true)
      by (rewrite mulD1_Vx, EnX; reflexivity).
    apply ile_meet; [apply O_pt_d|].
    apply ile_ineqzero; [apply O_pt_d| |].
    - (* lower endpoint of d(z) is 0: our z is at least 1 *)
      intros Hf0.
      eapply zle_trans.
      + apply (bestR_lb_ge Rcdiv_y (mulD1 d) Vz (Fin 1)).
        intros a Hb HR.
        unfold Rcdiv_y, rel in HR. cbn [op_rel cop cx cy cz] in HR.
        destruct HR as [Hz0 _].
        pose proof (Hb Vz) as Hmz. rewrite mulD1_Vz in Hmz.
        destruct Hmz as [Hm1 _]. rewrite Hf0 in Hm1. simpl in Hm1. simpl. lia.
      + rewrite <- (S1_pt Hg1 Vz).
        destruct (O_pt_S1 Hg1 Vz) as [Hf _]. exact Hf.
    - (* upper endpoint of d(z) is 0: our z is at most -1 *)
      intros Hf0.
      eapply zle_trans.
      + destruct (O_pt_S1 Hg1 Vz) as [_ Hs]. exact Hs.
      + rewrite (S1_pt Hg1 Vz).
        apply (bestR_ub_le Rcdiv_y (mulD1 d) Vz (Fin (-1))).
        intros a Hb HR.
        unfold Rcdiv_y, rel in HR. cbn [op_rel cop cx cy cz] in HR.
        destruct HR as [Hz0 _].
        pose proof (Hb Vz) as Hmz. rewrite mulD1_Vz in Hmz.
        destruct Hmz as [_ Hm2]. rewrite Hf0 in Hm2. simpl in Hm2. simpl. lia.
  Qed.


  (* ----- Obligation: our y is below Apt's mulback(x, z) cut ----- *)

  Lemma D2_y_mulback : ile (mulD2 d Vy) (imulback (mulX d) (aptZ1 d)).
  Proof.
    destruct (orb (zltb (Fin 0) (fst (aptZ1 d)))
                  (zltb (snd (aptZ1 d)) (Fin 0))) eqn:Esd.
    - (* branch 1: sign-definite divisor *)
      assert (Hg1 : orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true).
      { pose proof Esd as Esd'. unfold aptZ1 in Esd'.
        destruct (notin0b (mulX d)) eqn:EnX.
        - rewrite mulD1_Vx, EnX. reflexivity.
        - rewrite mulD1_Vx, mulD1_Vz, EnX.
          rewrite Bool.orb_false_l. exact Esd'. }
      split.
      + eapply zle_trans.
        * apply (bestR_lb_ge Rcdiv_y (mulD1 d) Vy
                   (fst (imulback (mulX d) (aptZ1 d)))).
          intros a Hb HR.
          unfold Rcdiv_y, rel in HR. cbn [op_rel cop cx cy cz] in HR.
          destruct HR as [Hz0 Hyv]. rewrite Hyv.
          pose proof (Hb Vx) as Hmx. rewrite mulD1_Vx in Hmx.
          destruct Hmx as [Hx1 Hx2].
          pose proof (Hb Vz) as Hmz. rewrite mulD1_Vz in Hmz.
          pose proof (sol_z_in_aptZ1 (a Vz) Hmz Hz0) as [Hz1 Hz2].
          apply (imulback_case1_lb (mulX d) (aptZ1 d) (a Vx) (a Vz) Esd);
            assumption.
        * rewrite <- (S1_pt Hg1 Vy).
          destruct (D2_pt_S1 Hg1 Vy) as [Hf _]. exact Hf.
      + rewrite (D2_pt_best Hg1 Vy).
        apply (bestR_ub_le Rfdiv_y (Pcdiv_y (mulD1 d)) Vy).
        intros a Hb HR.
        unfold Rfdiv_y, rel in HR. cbn [op_rel cop cx cy cz] in HR.
        destruct HR as [Hz0 Hyv]. rewrite Hyv.
        pose proof (Hb Vx) as Hmx.
        pose proof (imem_ile _ _ _ Hmx (S1_pt_D1 Hg1 Vx)) as Hmx'.
        rewrite mulD1_Vx in Hmx'. destruct Hmx' as [Hx1 Hx2].
        pose proof (Hb Vz) as Hmz.
        pose proof (imem_ile _ _ _ Hmz (S1_pt_D1 Hg1 Vz)) as Hmz'.
        rewrite mulD1_Vz in Hmz'.
        pose proof (sol_z_in_aptZ1 (a Vz) Hmz' Hz0) as [Hz1 Hz2].
        apply (imulback_case1_ub (mulX d) (aptZ1 d) (a Vx) (a Vz) Esd);
          assumption.
    - destruct (andb (andb (zltb (fst (aptZ1 d)) (Fin 0))
                           (zltb (Fin 0) (snd (aptZ1 d))))
                     (orb (zltb (Fin 0) (fst (mulX d)))
                          (zltb (snd (mulX d)) (Fin 0)))) eqn:Eb2.
      + (* branch 2: 0 ∉ x, mixed z *)
        assert (EnX : notin0b (mulX d) = true).
        { apply Bool.andb_true_iff in Eb2. destruct Eb2 as [_ E2]. exact E2. }
        assert (Hg1 : orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)) = true)
          by (rewrite mulD1_Vx, EnX; reflexivity).
        unfold imulback. rewrite Esd, Eb2.
        split; cbn [fst snd].
        * eapply zle_trans.
          -- apply (bestR_lb_ge Rcdiv_y (mulD1 d) Vy
                      (zmin (fst (mulX d)) (zneg (snd (mulX d))))).
             intros a Hb HR.
             unfold Rcdiv_y, rel in HR. cbn [op_rel cop cx cy cz] in HR.
             destruct HR as [Hz0 Hyv]. rewrite Hyv.
             pose proof (Hb Vx) as Hmx. rewrite mulD1_Vx in Hmx.
             destruct Hmx as [Hx1 Hx2].
             apply (case2_fst (mulX d) (cdivZ (a Vx) (a Vz)) (a Vx) Hx1 Hx2).
             pose proof (cdivZ_abs (a Vx) (a Vz) Hz0). lia.
          -- rewrite <- (S1_pt Hg1 Vy).
             destruct (D2_pt_S1 Hg1 Vy) as [Hf _]. exact Hf.
        * eapply zle_trans.
          -- destruct (D2_pt_S1 Hg1 Vy) as [_ Hs]. exact Hs.
          -- rewrite (S1_pt Hg1 Vy).
             apply (bestR_ub_le Rcdiv_y (mulD1 d) Vy).
             intros a Hb HR.
             unfold Rcdiv_y, rel in HR. cbn [op_rel cop cx cy cz] in HR.
             destruct HR as [Hz0 Hyv]. rewrite Hyv.
             pose proof (Hb Vx) as Hmx. rewrite mulD1_Vx in Hmx.
             destruct Hmx as [Hx1 Hx2].
             apply (case2_snd (mulX d) (cdivZ (a Vx) (a Vz)) (a Vx) Hx1 Hx2).
             pose proof (cdivZ_abs (a Vx) (a Vz) Hz0). lia.
      + unfold imulback. rewrite Esd, Eb2. apply ile_top.
  Qed.

  Lemma D2_y1_ob : ile (mulD2 d Vy) (aptY1 d).
  Proof.
    unfold aptY1. apply ile_meet; [apply D2_pt_d | apply D2_y_mulback].
  Qed.

  Lemma O_y1_ob : ile (prop_mul d Vy) (aptY1 d).
  Proof. eapply ile_trans; [apply O_pt_D2 | apply D2_y1_ob]. Qed.


  (* ----- the z-block stages, available when its guard fired ----- *)

  Lemma guard2_of_EnX :
    notin0b (mulX d) = true ->
    orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)) = true.
  Proof.
    intros EnX. apply Bool.orb_true_iff. left.
    exact (notin0_anti (mulD2 d Vx) (mulX d) D2_x_ob EnX).
  Qed.

  Lemma O_le_T1 :
    orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)) = true ->
    leI V3 (prop_mul d) (Pcdiv_z (mulD2 d)).
  Proof.
    intros Hg2. rewrite (prop_mul_eq2 d EmulX), Hg2.
    apply (prop_step_reductive Rfdiv_z Pfdiv_z Pfdiv_z_best).
  Qed.

  Lemma T1_pt :
    orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)) = true ->
    forall w, Pcdiv_z (mulD2 d) w = bestR Rcdiv_z (mulD2 d) w.
  Proof.
    intros Hg2. apply eqI_nonbot_pointwise.
    - exact (nb_of_le _ _ (O_le_T1 Hg2) HOnb).
    - apply Pcdiv_z_best.
  Qed.

  Lemma O_pt_T1 :
    orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)) = true ->
    forall w, ile (prop_mul d w) (Pcdiv_z (mulD2 d) w).
  Proof. intros Hg2. exact (leI_pt _ _ (O_le_T1 Hg2) HOnb). Qed.

  Lemma T1_pt_D2 :
    orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)) = true ->
    forall w, ile (Pcdiv_z (mulD2 d) w) (mulD2 d w).
  Proof.
    intros Hg2.
    apply (leI_pt _ _ (prop_step_reductive Rcdiv_z Pcdiv_z Pcdiv_z_best (mulD2 d))).
    exact (nb_of_le _ _ (O_le_T1 Hg2) HOnb).
  Qed.

  Lemma O_pt_best_T2 :
    orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)) = true ->
    forall w, prop_mul d w = bestR Rfdiv_z (Pcdiv_z (mulD2 d)) w.
  Proof.
    intros Hg2 w.
    assert (E : prop_mul d = Pfdiv_z (Pcdiv_z (mulD2 d)))
      by (rewrite (prop_mul_eq2 d EmulX), Hg2; reflexivity).
    rewrite E. apply eqI_nonbot_pointwise.
    - rewrite <- E. exact HOnb.
    - apply Pfdiv_z_best.
  Qed.

  (* ----- Obligation: our y is below Apt's clipped y ----- *)

  Lemma O_y2_ob : ile (prop_mul d Vy) (aptY2 d).
  Proof.
    unfold aptY2. destruct (notin0b (mulX d)) eqn:EnX; [|exact O_y1_ob].
    pose proof (guard2_of_EnX EnX) as Hg2.
    apply ile_meet; [exact O_y1_ob|].
    apply ile_ineqzero; [exact O_y1_ob| |].
    - intros Hf0.
      eapply zle_trans.
      + apply (bestR_lb_ge Rcdiv_z (mulD2 d) Vy (Fin 1)).
        intros a Hb HR.
        unfold Rcdiv_z, rel in HR. cbn [op_rel cop cx cy cz] in HR.
        destruct HR as [Hy0 _].
        pose proof (imem_ile _ _ _ (Hb Vy) D2_y1_ob) as [Hm1 _].
        rewrite Hf0 in Hm1. simpl in Hm1. simpl. lia.
      + rewrite <- (T1_pt Hg2 Vy).
        destruct (O_pt_T1 Hg2 Vy) as [Hf _]. exact Hf.
    - intros Hf0.
      eapply zle_trans.
      + destruct (O_pt_T1 Hg2 Vy) as [_ Hs]. exact Hs.
      + rewrite (T1_pt Hg2 Vy).
        apply (bestR_ub_le Rcdiv_z (mulD2 d) Vy (Fin (-1))).
        intros a Hb HR.
        unfold Rcdiv_z, rel in HR. cbn [op_rel cop cx cy cz] in HR.
        destruct HR as [Hy0 _].
        pose proof (imem_ile _ _ _ (Hb Vy) D2_y1_ob) as [_ Hm2].
        rewrite Hf0 in Hm2. simpl in Hm2. simpl. lia.
  Qed.

  (* Solutions' y-values enter Apt's clipped y-interval. *)
  Lemma sol_y_in_aptY2 : forall v : Z,
    imem v (mulD2 d Vy) -> v <> 0 -> imem v (aptY2 d).
  Proof.
    intros v Hm Hv.
    pose proof (imem_ile _ _ _ Hm D2_y1_ob) as Hm1.
    unfold aptY2. destruct (notin0b (mulX d)).
    - apply imem_imeet. split; [exact Hm1 | apply mem_ineqzero; assumption].
    - exact Hm1.
  Qed.

  (* ----- Obligation: our z is below Apt's final mulback(x, y) cut ----- *)

  Lemma O_z2_mulback : ile (prop_mul d Vz) (imulback (mulX d) (aptY2 d)).
  Proof.
    destruct (orb (zltb (Fin 0) (fst (aptY2 d)))
                  (zltb (snd (aptY2 d)) (Fin 0))) eqn:Esd.
    - (* branch 1 *)
      assert (Hg2 : orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)) = true).
      { pose proof Esd as Esd'. unfold aptY2 in Esd'.
        destruct (notin0b (mulX d)) eqn:EnX.
        - exact (guard2_of_EnX EnX).
        - apply Bool.orb_true_iff. right.
          exact (notin0_anti (mulD2 d Vy) (aptY1 d) D2_y1_ob Esd'). }
      split.
      + eapply zle_trans.
        * apply (bestR_lb_ge Rcdiv_z (mulD2 d) Vz
                   (fst (imulback (mulX d) (aptY2 d)))).
          intros a Hb HR.
          unfold Rcdiv_z, rel in HR. cbn [op_rel cop cx cy cz] in HR.
          destruct HR as [Hy0 Hzv]. rewrite Hzv.
          pose proof (imem_ile _ _ _ (Hb Vx) D2_x_ob) as [Hx1 Hx2].
          pose proof (sol_y_in_aptY2 (a Vy) (Hb Vy) Hy0) as [Hy1 Hy2].
          apply (imulback_case1_lb (mulX d) (aptY2 d) (a Vx) (a Vy) Esd);
            assumption.
        * rewrite <- (T1_pt Hg2 Vz).
          destruct (O_pt_T1 Hg2 Vz) as [Hf _]. exact Hf.
      + rewrite (O_pt_best_T2 Hg2 Vz).
        apply (bestR_ub_le Rfdiv_z (Pcdiv_z (mulD2 d)) Vz).
        intros a Hb HR.
        unfold Rfdiv_z, rel in HR. cbn [op_rel cop cx cy cz] in HR.
        destruct HR as [Hy0 Hzv]. rewrite Hzv.
        pose proof (imem_ile _ _ _ (Hb Vx) (T1_pt_D2 Hg2 Vx)) as Hmx'.
        pose proof (imem_ile _ _ _ Hmx' D2_x_ob) as [Hx1 Hx2].
        pose proof (imem_ile _ _ _ (Hb Vy) (T1_pt_D2 Hg2 Vy)) as Hmy'.
        pose proof (sol_y_in_aptY2 (a Vy) Hmy' Hy0) as [Hy1 Hy2].
        apply (imulback_case1_ub (mulX d) (aptY2 d) (a Vx) (a Vy) Esd);
          assumption.
    - destruct (andb (andb (zltb (fst (aptY2 d)) (Fin 0))
                           (zltb (Fin 0) (snd (aptY2 d))))
                     (orb (zltb (Fin 0) (fst (mulX d)))
                          (zltb (snd (mulX d)) (Fin 0)))) eqn:Eb2.
      + (* branch 2 *)
        assert (EnX : notin0b (mulX d) = true).
        { apply Bool.andb_true_iff in Eb2. destruct Eb2 as [_ E2]. exact E2. }
        pose proof (guard2_of_EnX EnX) as Hg2.
        unfold imulback. rewrite Esd, Eb2.
        split; cbn [fst snd].
        * eapply zle_trans.
          -- apply (bestR_lb_ge Rcdiv_z (mulD2 d) Vz
                      (zmin (fst (mulX d)) (zneg (snd (mulX d))))).
             intros a Hb HR.
             unfold Rcdiv_z, rel in HR. cbn [op_rel cop cx cy cz] in HR.
             destruct HR as [Hy0 Hzv]. rewrite Hzv.
             pose proof (imem_ile _ _ _ (Hb Vx) D2_x_ob) as [Hx1 Hx2].
             apply (case2_fst (mulX d) (cdivZ (a Vx) (a Vy)) (a Vx) Hx1 Hx2).
             pose proof (cdivZ_abs (a Vx) (a Vy) Hy0). lia.
          -- rewrite <- (T1_pt Hg2 Vz).
             destruct (O_pt_T1 Hg2 Vz) as [Hf _]. exact Hf.
        * eapply zle_trans.
          -- destruct (O_pt_T1 Hg2 Vz) as [_ Hs]. exact Hs.
          -- rewrite (T1_pt Hg2 Vz).
             apply (bestR_ub_le Rcdiv_z (mulD2 d) Vz).
             intros a Hb HR.
             unfold Rcdiv_z, rel in HR. cbn [op_rel cop cx cy cz] in HR.
             destruct HR as [Hy0 Hzv]. rewrite Hzv.
             pose proof (imem_ile _ _ _ (Hb Vx) D2_x_ob) as [Hx1 Hx2].
             apply (case2_snd (mulX d) (cdivZ (a Vx) (a Vy)) (a Vx) Hx1 Hx2).
             pose proof (cdivZ_abs (a Vx) (a Vy) Hy0). lia.
      + unfold imulback. rewrite Esd, Eb2. apply ile_top.
  Qed.

  Lemma O_z2_ob : ile (prop_mul d Vz) (aptZ2 d).
  Proof.
    unfold aptZ2. apply ile_meet; [apply O_z1_ob | apply O_z2_mulback].
  Qed.

  (* ----- Assembling: Apt's tests all pass, and pointwise dominance ----- *)

  Lemma O_le_apt : leI V3 (prop_mul d) (prop_apt d).
  Proof.
    right. intros w.
    unfold prop_apt. rewrite EmulX.
    assert (EZ1 : isbotb (aptZ1 d) = false).
    { apply isbotb_false.
      exact (ile_not_isbot _ _ O_z1_ob (Onb_comp Vz)). }
    assert (EY1 : isbotb (aptY1 d) = false).
    { apply isbotb_false.
      exact (ile_not_isbot _ _ O_y1_ob (Onb_comp Vy)). }
    assert (EY2 : isbotb (aptY2 d) = false).
    { apply isbotb_false.
      exact (ile_not_isbot _ _ O_y2_ob (Onb_comp Vy)). }
    rewrite EZ1, EY1, EY2.
    right.
    destruct w.
    - rewrite (vupd_other _ Vy _ Vx) by congruence.
      rewrite (vupd_other _ Vz _ Vx) by congruence.
      rewrite vupd_same. exact O_x_ob.
    - rewrite vupd_same. exact O_y2_ob.
    - rewrite (vupd_other _ Vy _ Vz) by congruence.
      rewrite vupd_same. exact O_z2_ob.
  Qed.

End Dominance.

(* ======================= Dominance theorem ======================= *)

Theorem apt_dominates : forall d : istore V3,
  leI V3 (prop_mul d) (prop_apt d).
Proof.
  intros d.
  destruct (classic (isbotI V3 (prop_mul d))) as [Hb|Hnb].
  - left. exact Hb.
  - exact (O_le_apt d Hnb).
Qed.

(* ======================= Strictness witness ======================= *)
(* x = [4,4], y = z = [-3,3]: division-based propagation shrinks y and z
   to [-2,2] (no divisor of 4 has absolute value 3 with the cofactor in
   range), while Apt et al.'s mulback falls into its mixed-sign case and
   keeps [-3,3]. *)

Definition d18 : istore V3 :=
  fun w => match w with
           | Vx => (Fin 4, Fin 4)
           | Vy => (Fin (-3), Fin 3)
           | Vz => (Fin (-3), Fin 3)
           end.

Lemma strict18 : ~ leI V3 (prop_apt d18) (prop_mul d18).
Proof.
  intros [Hb|Hpt].
  - destruct Hb as [w Hw]. destruct w; vm_compute in Hw;
      destruct Hw as [Hw|[Hw|Hw]]; first [exact Hw | discriminate Hw | lia].
  - specialize (Hpt Vz). vm_compute in Hpt.
    destruct Hpt as [[H|[H|H]]|[H1 H2]];
      first [exact H | discriminate H | lia
            | exact (H1 eq_refl) | exact (H2 eq_refl)].
Qed.

(* ======================= CLAIM 18 ======================= *)
(* Our multiplication propagator is strictly stronger than Apt et al.'s. *)
Theorem claim18 :
  (forall d : istore V3, leI V3 (prop_mul d) (prop_apt d)) /\
  (exists d : istore V3, ~ leI V3 (prop_apt d) (prop_mul d)).
Proof.
  split.
  - exact apt_dominates.
  - exists d18. exact strict18.
Qed.
