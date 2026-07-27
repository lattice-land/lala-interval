(* ========================================================================= *)
(* Claim 17: the multiplication propagator (Figure IV) is sound, best on     *)
(* assignments, reductive and monotone.                                      *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical FunctionalExtensionality
  PropExtensionality.
From Paper Require Import claim1 claim2 claim3 claim4 claim8 claim9 claim10
  claim11 claim12 claim15 claim16 claim20.
Open Scope Z_scope.

(* ==================== Definitions ==================== *)

Definition imul (i j : Itv) : Itv :=
  (zmin (zmin (zmul (fst i) (fst j)) (zmul (fst i) (snd j)))
        (zmin (zmul (snd i) (fst j)) (zmul (snd i) (snd j))),
   zmax (zmax (zmul (fst i) (fst j)) (zmul (fst i) (snd j)))
        (zmax (zmul (snd i) (fst j)) (zmul (snd i) (snd j)))).

Definition notin0b (i : Itv) : bool :=
  zltb (Fin 0) (fst i) || zltb (snd i) (Fin 0).

Definition mulX (d : istore V3) : Itv := imeet (d Vx) (imul (d Vy) (d Vz)).

Definition mulD1 (d : istore V3) : istore V3 := vupd d Vx (mulX d).

Definition mulD2 (d : istore V3) : istore V3 :=
  if orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz))
  then prop_fdiv Vy Vx Vz (prop_cdiv Vy Vx Vz (mulD1 d))
  else mulD1 d.

Definition prop_mul (d : istore V3) : istore V3 :=
  if isbotb (mulX d) then vupd d Vx (mulX d)
  else if orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy))
       then prop_fdiv Vz Vx Vy (prop_cdiv Vz Vx Vy (mulD2 d))
       else mulD2 d.

Definition c_mul3 : constraint V3 := MkC Vx Vy Vz OMul.

(* ==================== Basic guard lemmas ==================== *)

Lemma notin0_no_zero : forall i (v : Z),
  notin0b i = true -> imem v i -> v <> 0.
Proof.
  intros [l u] v Hg [H1 H2] Hv. subst v. cbn [fst snd] in *.
  unfold notin0b in Hg. cbn [fst snd] in Hg.
  apply Bool.orb_true_iff in Hg. destruct Hg as [Hg|Hg]; apply zltb_lt in Hg.
  - exact (zlt_nle _ _ Hg H1).
  - exact (zlt_nle _ _ Hg H2).
Qed.

Lemma notin0_anti : forall i i',
  ile i i' -> notin0b i' = true -> notin0b i = true.
Proof.
  intros [l u] [l' u'] [H1 H2] Hg.
  unfold notin0b in *. cbn [fst snd] in *.
  apply Bool.orb_true_iff in Hg. apply Bool.orb_true_iff.
  destruct Hg as [Hg|Hg]; apply zltb_lt in Hg.
  - left. apply zltb_lt. eapply zlt_le_trans; [exact Hg | exact H1].
  - right. apply zltb_lt. eapply zle_lt_trans; [exact H2 | exact Hg].
Qed.

(* ==================== Small Zinf helpers ==================== *)

Lemma zmax_id : forall x, zmax x x = x.
Proof. intros x. unfold zmax. destruct (zleb x x); reflexivity. Qed.

Lemma zmul_fin0_r : forall x, zmul x (Fin 0) = Fin 0.
Proof.
  intros [|a|]; simpl; try reflexivity.
  f_equal. ring.
Qed.

Lemma zmul_comm : forall x y, zmul x y = zmul y x.
Proof.
  intros [|a|] [|b|]; simpl; try reflexivity.
  f_equal. ring.
Qed.

Lemma zmul_minf_neg : forall z : Z, z < 0 -> zmul MInf (Fin z) = PInf.
Proof.
  intros z Hz. simpl. destruct (z =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? z) eqn:E2; [apply Z.ltb_lt in E2; lia | reflexivity].
Qed.

Lemma zmul_pinf_neg : forall z : Z, z < 0 -> zmul PInf (Fin z) = MInf.
Proof.
  intros z Hz. simpl. destruct (z =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? z) eqn:E2; [apply Z.ltb_lt in E2; lia | reflexivity].
Qed.

Lemma zmin_mono : forall a a' b b',
  zle a a' -> zle b b' -> zle (zmin a b) (zmin a' b').
Proof.
  intros a a' b b' Ha Hb. apply zmin_glb.
  - eapply zle_trans; [apply zmin_le_l | exact Ha].
  - eapply zle_trans; [apply zmin_le_r | exact Hb].
Qed.

Lemma zmax_mono : forall a a' b b',
  zle a a' -> zle b b' -> zle (zmax a b) (zmax a' b').
Proof.
  intros a a' b b' Ha Hb. apply zmax_lub.
  - eapply zle_trans; [exact Ha | apply zmax_ge_l].
  - eapply zle_trans; [exact Hb | apply zmax_ge_r].
Qed.

Lemma imeet_mono : forall i i' j j',
  ile i i' -> ile j j' -> ile (imeet i j) (imeet i' j').
Proof.
  intros [a b] [a' b'] [c e] [c' e'] [H1 H2] [H3 H4].
  unfold imeet, ile. cbn [fst snd] in *.
  split; [apply zmax_mono; assumption | apply zmin_mono; assumption].
Qed.

(* ==================== Zinf multiplication monotonicity ==================== *)

Lemma zmul_anti_neg : forall x x' (c : Z),
  c < 0 -> zle x x' -> zle (zmul x' (Fin c)) (zmul x (Fin c)).
Proof.
  intros [|a|] [|b|] c Hc H; simpl in H; try contradiction.
  - rewrite zmul_minf_neg by lia. apply zle_pinf.
  - rewrite zmul_minf_neg by lia. apply zle_pinf.
  - rewrite zmul_minf_neg by lia. apply zle_pinf.
  - simpl. nia.
  - rewrite zmul_pinf_neg by lia. apply zle_minf.
  - rewrite zmul_pinf_neg by lia. apply zle_refl.
Qed.

Lemma zmul_mono_pinf : forall x x', zle x x' -> zle (zmul x PInf) (zmul x' PInf).
Proof.
  intros x x' H.
  destruct x as [|a|]; destruct x' as [|b|]; simpl in H; try contradiction.
  - apply zle_refl.
  - change (zmul MInf PInf) with MInf. apply zle_minf.
  - change (zmul MInf PInf) with MInf. apply zle_minf.
  - destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
    + rewrite (zmul_fin_pinf_neg a Ha). apply zle_minf.
    + subst a. rewrite zmul_fin0_l.
      destruct (Z.lt_trichotomy b 0) as [Hb|[Hb|Hb]]; [exfalso; lia| |].
      * subst b. rewrite zmul_fin0_l. apply zle_refl.
      * rewrite (zmul_fin_pinf_pos b Hb). exact I.
    + rewrite (zmul_fin_pinf_pos a Ha).
      assert (Hb : 0 < b) by lia.
      rewrite (zmul_fin_pinf_pos b Hb). apply zle_refl.
  - change (zmul PInf PInf) with PInf. apply zle_pinf.
  - apply zle_refl.
Qed.

Lemma zmul_anti_minf : forall x x', zle x x' -> zle (zmul x' MInf) (zmul x MInf).
Proof.
  intros x x' H.
  destruct x as [|a|]; destruct x' as [|b|]; simpl in H; try contradiction.
  - apply zle_refl.
  - change (zmul MInf MInf) with PInf. apply zle_pinf.
  - change (zmul MInf MInf) with PInf. apply zle_pinf.
  - destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
    + rewrite (zmul_fin_minf_neg a Ha). apply zle_pinf.
    + subst a. rewrite zmul_fin0_l.
      destruct (Z.lt_trichotomy b 0) as [Hb|[Hb|Hb]]; [exfalso; lia| |].
      * subst b. rewrite zmul_fin0_l. apply zle_refl.
      * rewrite (zmul_fin_minf_pos b Hb). apply zle_minf.
    + rewrite (zmul_fin_minf_pos a Ha).
      assert (Hb : 0 < b) by lia.
      rewrite (zmul_fin_minf_pos b Hb). apply zle_refl.
  - change (zmul PInf MInf) with MInf. apply zle_minf.
  - apply zle_refl.
Qed.

(* One-variable between lemmas. *)
Lemma zmul_between_l : forall l u v w,
  zle l v -> zle v u ->
  zle (zmin (zmul l w) (zmul u w)) (zmul v w) /\
  zle (zmul v w) (zmax (zmul l w) (zmul u w)).
Proof.
  intros l u v w Hlv Hvu. destruct w as [|c|].
  - split.
    + eapply zle_trans; [apply zmin_le_r | apply zmul_anti_minf; exact Hvu].
    + eapply zle_trans; [apply zmul_anti_minf; exact Hlv | apply zmax_ge_l].
  - destruct (Z.lt_trichotomy c 0) as [Hc|[Hc|Hc]].
    + split.
      * eapply zle_trans;
          [apply zmin_le_r | apply zmul_anti_neg; [exact Hc | exact Hvu]].
      * eapply zle_trans;
          [apply zmul_anti_neg; [exact Hc | exact Hlv] | apply zmax_ge_l].
    + subst c. rewrite !zmul_fin0_r, zmin_id, zmax_id.
      split; apply zle_refl.
    + split.
      * eapply zle_trans;
          [apply zmin_le_l | apply zmul_mono2; [exact Hlv | lia]].
      * eapply zle_trans;
          [apply zmul_mono2; [exact Hvu | lia] | apply zmax_ge_r].
  - split.
    + eapply zle_trans; [apply zmin_le_l | apply zmul_mono_pinf; exact Hlv].
    + eapply zle_trans; [apply zmul_mono_pinf; exact Hvu | apply zmax_ge_r].
Qed.

Lemma zmul_between_r : forall l u v w,
  zle l v -> zle v u ->
  zle (zmin (zmul w l) (zmul w u)) (zmul w v) /\
  zle (zmul w v) (zmax (zmul w l) (zmul w u)).
Proof.
  intros l u v w Hlv Hvu.
  rewrite (zmul_comm w l), (zmul_comm w u), (zmul_comm w v).
  apply zmul_between_l; assumption.
Qed.

(* ==================== 2D corner bounds for imul ==================== *)

Lemma imul_corner : forall yl yu zl zu v w,
  zle yl v -> zle v yu -> zle zl w -> zle w zu ->
  zle (fst (imul (yl, yu) (zl, zu))) (zmul v w) /\
  zle (zmul v w) (snd (imul (yl, yu) (zl, zu))).
Proof.
  intros yl yu zl zu v w Hy1 Hy2 Hz1 Hz2.
  unfold imul. cbn [fst snd].
  split.
  - eapply zle_trans;
      [| apply (proj1 (zmul_between_r zl zu w v Hz1 Hz2)) ].
    apply zmin_glb.
    + eapply zle_trans;
        [| apply (proj1 (zmul_between_l yl yu v zl Hy1 Hy2)) ].
      apply zmin_glb.
      * eapply zle_trans; [apply zmin_le_l | apply zmin_le_l].
      * eapply zle_trans; [apply zmin_le_r | apply zmin_le_l].
    + eapply zle_trans;
        [| apply (proj1 (zmul_between_l yl yu v zu Hy1 Hy2)) ].
      apply zmin_glb.
      * eapply zle_trans; [apply zmin_le_l | apply zmin_le_r].
      * eapply zle_trans; [apply zmin_le_r | apply zmin_le_r].
  - eapply zle_trans;
      [ apply (proj2 (zmul_between_r zl zu w v Hz1 Hz2)) |].
    apply zmax_lub.
    + eapply zle_trans;
        [ apply (proj2 (zmul_between_l yl yu v zl Hy1 Hy2)) |].
      apply zmax_lub.
      * eapply zle_trans; [apply zmax_ge_l | apply zmax_ge_l].
      * eapply zle_trans; [apply zmax_ge_l | apply zmax_ge_r].
    + eapply zle_trans;
        [ apply (proj2 (zmul_between_l yl yu v zu Hy1 Hy2)) |].
      apply zmax_lub.
      * eapply zle_trans; [apply zmax_ge_r | apply zmax_ge_l].
      * eapply zle_trans; [apply zmax_ge_r | apply zmax_ge_r].
Qed.

Lemma imul_mem_intro : forall (b c : Z) (Yi Zi : Itv),
  imem b Yi -> imem c Zi -> imem (b * c) (imul Yi Zi).
Proof.
  intros b c [yl yu] [zl zu] [H1 H2] [H3 H4]. cbn [fst snd] in *.
  destruct (imul_corner yl yu zl zu (Fin b) (Fin c) H1 H2 H3 H4) as [Hlo Hhi].
  split.
  - exact Hlo.
  - exact Hhi.
Qed.

Lemma imul_mono : forall (Yi Yi' Zi Zi' : Itv),
  zle (fst Yi) (snd Yi) -> zle (fst Zi) (snd Zi) ->
  ile Yi Yi' -> ile Zi Zi' ->
  ile (imul Yi Zi) (imul Yi' Zi').
Proof.
  intros [yl yu] [yl' yu'] [zl zu] [zl' zu'] Hy Hz [Hy1 Hy2] [Hz1 Hz2].
  cbn [fst snd] in *.
  assert (Hyl : zle yl' yl /\ zle yl yu').
  { split; [exact Hy1 | eapply zle_trans; [exact Hy | exact Hy2]]. }
  assert (Hyu : zle yl' yu /\ zle yu yu').
  { split; [eapply zle_trans; [exact Hy1 | exact Hy] | exact Hy2]. }
  assert (Hzl : zle zl' zl /\ zle zl zu').
  { split; [exact Hz1 | eapply zle_trans; [exact Hz | exact Hz2]]. }
  assert (Hzu : zle zl' zu /\ zle zu zu').
  { split; [eapply zle_trans; [exact Hz1 | exact Hz] | exact Hz2]. }
  split.
  - cbn [imul fst snd].
    apply zmin_glb; apply zmin_glb.
    + exact (proj1 (imul_corner yl' yu' zl' zu' yl zl
               (proj1 Hyl) (proj2 Hyl) (proj1 Hzl) (proj2 Hzl))).
    + exact (proj1 (imul_corner yl' yu' zl' zu' yl zu
               (proj1 Hyl) (proj2 Hyl) (proj1 Hzu) (proj2 Hzu))).
    + exact (proj1 (imul_corner yl' yu' zl' zu' yu zl
               (proj1 Hyu) (proj2 Hyu) (proj1 Hzl) (proj2 Hzl))).
    + exact (proj1 (imul_corner yl' yu' zl' zu' yu zu
               (proj1 Hyu) (proj2 Hyu) (proj1 Hzu) (proj2 Hzu))).
  - cbn [imul fst snd].
    apply zmax_lub; apply zmax_lub.
    + exact (proj2 (imul_corner yl' yu' zl' zu' yl zl
               (proj1 Hyl) (proj2 Hyl) (proj1 Hzl) (proj2 Hzl))).
    + exact (proj2 (imul_corner yl' yu' zl' zu' yl zu
               (proj1 Hyl) (proj2 Hyl) (proj1 Hzu) (proj2 Hzu))).
    + exact (proj2 (imul_corner yl' yu' zl' zu' yu zl
               (proj1 Hyu) (proj2 Hyu) (proj1 Hzl) (proj2 Hzl))).
    + exact (proj2 (imul_corner yl' yu' zl' zu' yu zu
               (proj1 Hyu) (proj2 Hyu) (proj1 Hzu) (proj2 Hzu))).
Qed.

Lemma imul_singleton : forall b c : Z,
  imul (Fin b, Fin b) (Fin c, Fin c) = (Fin (b * c), Fin (b * c)).
Proof.
  intros b c. unfold imul. cbn [fst snd].
  change (zmul (Fin b) (Fin c)) with (Fin (b * c)).
  rewrite !zmin_id, !zmax_id. reflexivity.
Qed.

(* ==================== Generic best-step machinery ==================== *)

Lemma leI_trans : forall (a b c : istore V3),
  leI V3 a b -> leI V3 b c -> leI V3 a c.
Proof. exact (ole_trans (o := I_OSet V3)). Qed.

Lemma leI_eq_l : forall (a a' b : istore V3),
  eqI V3 a a' -> leI V3 a' b -> leI V3 a b.
Proof. exact (ole_eq_l (I_OSet V3)). Qed.

Lemma leI_eq_r : forall (a b b' : istore V3),
  eqI V3 b b' -> leI V3 a b' -> leI V3 a b.
Proof. exact (ole_eq_r (I_OSet V3)). Qed.

Lemma leI_bot_out : forall (e d : istore V3),
  leI V3 e d -> isbotI V3 d -> isbotI V3 e.
Proof.
  intros e d [Hb|Hpt] Hd; [exact Hb|].
  destruct Hd as [w Hw]. exists w. exact (isle_isbot _ _ (Hpt w) Hw).
Qed.

Lemma best_preserves : forall (R : powerset (Asn V3)) (P : istore V3 -> istore V3),
  (forall d, eqI V3 (P d) (bestR R d)) ->
  forall d asn, ibox d asn -> R asn -> forall w, imem (asn w) (P d w).
Proof.
  intros R P Hbest d asn Hb HR w.
  pose proof (sol_in_bestR R d asn Hb HR) as Hin.
  destruct (Hbest d) as [[_ Hbot]|Hpt].
  - exfalso. destruct Hbot as [w0 Hw0].
    exact (imem_not_isbot _ _ (Hin w0) Hw0).
  - destruct (Hpt w) as [[_ Hbot]|Heq].
    + exfalso. exact (imem_not_isbot _ _ (Hin w) Hbot).
    + rewrite Heq. exact (Hin w).
Qed.

Lemma bestR_ile_d : forall (R : powerset (Asn V3)) (d : istore V3) w,
  ile (bestR R d w) (d w).
Proof.
  intros R d w. unfold bestR, ihull, alphai. split; cbn [fst snd].
  - apply zinfS_greatest. intros x [v [[asn [[Hbox HR] Hv]] Heq]].
    subst x v. destruct (Hbox w) as [H1 _]. exact H1.
  - apply zsup_least. intros x [v [[asn [[Hbox HR] Hv]] Heq]].
    subst x v. destruct (Hbox w) as [_ H2]. exact H2.
Qed.

Lemma bestR_reductive : forall (R : powerset (Asn V3)) d, leI V3 (bestR R d) d.
Proof. intros R d. right. intros w. right. apply bestR_ile_d. Qed.

Lemma ibox_mono : forall (d d' : istore V3) asn,
  (forall w, isle (d w) (d' w)) -> ibox d asn -> ibox d' asn.
Proof.
  intros d d' asn Hle Hb w.
  destruct (Hle w) as [Hbot|Hile].
  - exfalso. exact (isbot_no_mem _ Hbot _ (Hb w)).
  - exact (imem_ile _ _ _ (Hb w) Hile).
Qed.

Lemma bestR_monotone : forall (R : powerset (Asn V3)) d d',
  leI V3 d d' -> leI V3 (bestR R d) (bestR R d').
Proof.
  intros R d d' [Hbot|Hpt].
  - left. destruct Hbot as [w0 Hw0].
    apply (no_sol_bestR_bot R d Vx).
    intros asn Hb _. exact (isbot_no_mem _ Hw0 _ (Hb w0)).
  - right. intros w. right.
    unfold bestR, ihull, alphai. split; cbn [fst snd].
    + apply zinfS_greatest. intros x [v [[asn [[Hbox HR] Hv]] Heq]].
      subst x v.
      apply zinfS_lb. exists (asn w). split; [|reflexivity].
      exists asn.
      split; [split; [exact (ibox_mono d d' asn Hpt Hbox) | exact HR]
             | reflexivity].
    + apply zsup_least. intros x [v [[asn [[Hbox HR] Hv]] Heq]].
      subst x v.
      apply zsup_ub. exists (asn w). split; [|reflexivity].
      exists asn.
      split; [split; [exact (ibox_mono d d' asn Hpt Hbox) | exact HR]
             | reflexivity].
Qed.

Lemma prop_step_reductive :
  forall (R : powerset (Asn V3)) (P : istore V3 -> istore V3),
  (forall d, eqI V3 (P d) (bestR R d)) ->
  forall d, leI V3 (P d) d.
Proof.
  intros R P Hbest d.
  apply (leI_eq_l (P d) (bestR R d) d (Hbest d)).
  apply bestR_reductive.
Qed.

Lemma prop_step_monotone :
  forall (R : powerset (Asn V3)) (P : istore V3 -> istore V3),
  (forall d, eqI V3 (P d) (bestR R d)) ->
  forall d d', leI V3 d d' -> leI V3 (P d) (P d').
Proof.
  intros R P Hbest d d' Hle.
  apply (leI_eq_l (P d) (bestR R d) (P d') (Hbest d)).
  apply (leI_eq_r (bestR R d) (P d') (bestR R d') (Hbest d')).
  apply bestR_monotone. exact Hle.
Qed.

(* ==================== The four division steps ==================== *)

Definition Pcdiv_y : istore V3 -> istore V3 := prop_cdiv Vy Vx Vz.
Definition Pfdiv_y : istore V3 -> istore V3 := prop_fdiv Vy Vx Vz.
Definition Pcdiv_z : istore V3 -> istore V3 := prop_cdiv Vz Vx Vy.
Definition Pfdiv_z : istore V3 -> istore V3 := prop_fdiv Vz Vx Vy.

Definition Rcdiv_y : powerset (Asn V3) := rel (MkC Vy Vx Vz OCdiv).
Definition Rfdiv_y : powerset (Asn V3) := rel (MkC Vy Vx Vz OFdiv).
Definition Rcdiv_z : powerset (Asn V3) := rel (MkC Vz Vx Vy OCdiv).
Definition Rfdiv_z : powerset (Asn V3) := rel (MkC Vz Vx Vy OFdiv).

Lemma Pcdiv_y_best : forall d, eqI V3 (Pcdiv_y d) (bestR Rcdiv_y d).
Proof.
  intros d. unfold Pcdiv_y, Rcdiv_y. rewrite <- bestI_is_bestR.
  apply prop_cdiv_best; congruence.
Qed.

Lemma Pfdiv_y_best : forall d, eqI V3 (Pfdiv_y d) (bestR Rfdiv_y d).
Proof.
  intros d. unfold Pfdiv_y, Rfdiv_y. rewrite <- bestI_is_bestR.
  apply prop_fdiv_best; congruence.
Qed.

Lemma Pcdiv_z_best : forall d, eqI V3 (Pcdiv_z d) (bestR Rcdiv_z d).
Proof.
  intros d. unfold Pcdiv_z, Rcdiv_z. rewrite <- bestI_is_bestR.
  apply prop_cdiv_best; congruence.
Qed.

Lemma Pfdiv_z_best : forall d, eqI V3 (Pfdiv_z d) (bestR Rfdiv_z d).
Proof.
  intros d. unfold Pfdiv_z, Rfdiv_z. rewrite <- bestI_is_bestR.
  apply prop_fdiv_best; congruence.
Qed.

(* ==================== Integer division facts ==================== *)

Lemma fdivZ_mul_cancel : forall y z : Z, z <> 0 -> fdivZ (y * z) z = y.
Proof. intros y z Hz. unfold fdivZ. apply Z.div_mul. exact Hz. Qed.

Lemma cdivZ_mul_cancel : forall y z : Z, z <> 0 -> cdivZ (y * z) z = y.
Proof.
  intros y z Hz. unfold cdivZ.
  replace (- (y * z)) with ((- y) * z) by ring.
  rewrite Z.div_mul by exact Hz. lia.
Qed.

(* ==================== Soundness ==================== *)

Lemma rel_mul3_char : forall asn, rel c_mul3 asn <-> asn Vx = asn Vy * asn Vz.
Proof.
  intros asn. unfold rel, c_mul3. cbn [op_rel cop cx cy cz]. tauto.
Qed.

(* The relations of the four division steps hold of any solution with the
   corresponding non-zero divisor. *)
Lemma sol_Rcdiv_y : forall asn,
  asn Vx = asn Vy * asn Vz -> asn Vz <> 0 -> Rcdiv_y asn.
Proof.
  intros asn Heq Hz. unfold Rcdiv_y, rel. cbn [op_rel cop cx cy cz].
  split; [exact Hz|]. rewrite Heq. symmetry. apply cdivZ_mul_cancel. exact Hz.
Qed.

Lemma sol_Rfdiv_y : forall asn,
  asn Vx = asn Vy * asn Vz -> asn Vz <> 0 -> Rfdiv_y asn.
Proof.
  intros asn Heq Hz. unfold Rfdiv_y, rel. cbn [op_rel cop cx cy cz].
  split; [exact Hz|]. rewrite Heq. symmetry. apply fdivZ_mul_cancel. exact Hz.
Qed.

Lemma sol_Rcdiv_z : forall asn,
  asn Vx = asn Vy * asn Vz -> asn Vy <> 0 -> Rcdiv_z asn.
Proof.
  intros asn Heq Hy. unfold Rcdiv_z, rel. cbn [op_rel cop cx cy cz].
  split; [exact Hy|]. rewrite Heq.
  replace (asn Vy * asn Vz) with (asn Vz * asn Vy) by ring.
  symmetry. apply cdivZ_mul_cancel. exact Hy.
Qed.

Lemma sol_Rfdiv_z : forall asn,
  asn Vx = asn Vy * asn Vz -> asn Vy <> 0 -> Rfdiv_z asn.
Proof.
  intros asn Heq Hy. unfold Rfdiv_z, rel. cbn [op_rel cop cx cy cz].
  split; [exact Hy|]. rewrite Heq.
  replace (asn Vy * asn Vz) with (asn Vz * asn Vy) by ring.
  symmetry. apply fdivZ_mul_cancel. exact Hy.
Qed.

(* A solution in the box lies in the meet interval for Vx. *)
Lemma sol_mem_mulX : forall d asn,
  ibox d asn -> asn Vx = asn Vy * asn Vz -> imem (asn Vx) (mulX d).
Proof.
  intros d asn Hb Heq. unfold mulX. apply imem_imeet. split; [apply Hb|].
  rewrite Heq. apply imul_mem_intro; apply Hb.
Qed.

Lemma sol_ibox_mulD1 : forall d asn,
  ibox d asn -> asn Vx = asn Vy * asn Vz -> ibox (mulD1 d) asn.
Proof.
  intros d asn Hb Heq w. unfold mulD1, vupd.
  destruct (V3_eq_dec w Vx) as [->|Hne].
  - exact (sol_mem_mulX d asn Hb Heq).
  - apply Hb.
Qed.

(* Guards give non-zeroness of the relevant variable. *)
Lemma guard_yz_nonzero : forall (e : istore V3) asn,
  ibox e asn -> asn Vx = asn Vy * asn Vz ->
  orb (notin0b (e Vx)) (notin0b (e Vz)) = true ->
  asn Vz <> 0.
Proof.
  intros e asn Hb Heq Hg.
  apply Bool.orb_true_iff in Hg. destruct Hg as [Hg|Hg].
  - pose proof (notin0_no_zero _ _ Hg (Hb Vx)) as Hx. rewrite Heq in Hx.
    intros Hc. apply Hx. rewrite Hc. ring.
  - exact (notin0_no_zero _ _ Hg (Hb Vz)).
Qed.

Lemma guard_zy_nonzero : forall (e : istore V3) asn,
  ibox e asn -> asn Vx = asn Vy * asn Vz ->
  orb (notin0b (e Vx)) (notin0b (e Vy)) = true ->
  asn Vy <> 0.
Proof.
  intros e asn Hb Heq Hg.
  apply Bool.orb_true_iff in Hg. destruct Hg as [Hg|Hg].
  - pose proof (notin0_no_zero _ _ Hg (Hb Vx)) as Hx. rewrite Heq in Hx.
    intros Hc. apply Hx. rewrite Hc. ring.
  - exact (notin0_no_zero _ _ Hg (Hb Vy)).
Qed.

Lemma sol_ibox_mulD2 : forall d asn,
  ibox d asn -> asn Vx = asn Vy * asn Vz -> ibox (mulD2 d) asn.
Proof.
  intros d asn Hb Heq. unfold mulD2.
  pose proof (sol_ibox_mulD1 d asn Hb Heq) as Hb1.
  destruct (orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz))) eqn:Eg;
    [|exact Hb1].
  assert (Hz : asn Vz <> 0) by exact (guard_yz_nonzero (mulD1 d) asn Hb1 Heq Eg).
  assert (Hc : ibox (Pcdiv_y (mulD1 d)) asn).
  { intros w. exact (best_preserves Rcdiv_y Pcdiv_y Pcdiv_y_best
                       (mulD1 d) asn Hb1 (sol_Rcdiv_y asn Heq Hz) w). }
  intros w.
  exact (best_preserves Rfdiv_y Pfdiv_y Pfdiv_y_best
           (Pcdiv_y (mulD1 d)) asn Hc (sol_Rfdiv_y asn Heq Hz) w).
Qed.

Lemma sol_ibox_prop_mul : forall d asn,
  ibox d asn -> asn Vx = asn Vy * asn Vz -> ibox (prop_mul d) asn.
Proof.
  intros d asn Hb Heq. unfold prop_mul.
  destruct (isbotb (mulX d)) eqn:EB.
  { exfalso. apply isbotb_isbot in EB.
    exact (imem_not_isbot _ _ (sol_mem_mulX d asn Hb Heq) EB). }
  pose proof (sol_ibox_mulD2 d asn Hb Heq) as Hb2.
  destruct (orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy))) eqn:Eg;
    [|exact Hb2].
  assert (Hy : asn Vy <> 0) by exact (guard_zy_nonzero (mulD2 d) asn Hb2 Heq Eg).
  assert (Hc : ibox (Pcdiv_z (mulD2 d)) asn).
  { intros w. exact (best_preserves Rcdiv_z Pcdiv_z Pcdiv_z_best
                       (mulD2 d) asn Hb2 (sol_Rcdiv_z asn Heq Hy) w). }
  intros w.
  exact (best_preserves Rfdiv_z Pfdiv_z Pfdiv_z_best
           (Pcdiv_z (mulD2 d)) asn Hc (sol_Rfdiv_z asn Heq Hy) w).
Qed.

Theorem claim17_sound : forall d, leI V3 (bestI c_mul3 d) (prop_mul d).
Proof.
  intros d. rewrite bestI_is_bestR.
  apply (sols_preserved_sound_R (rel c_mul3) Vx).
  intros asn Hb HR w.
  apply rel_mul3_char in HR.
  exact (sol_ibox_prop_mul d asn Hb HR w).
Qed.

(* ==================== Reductivity ==================== *)

Lemma mulD1_reductive : forall d, leI V3 (mulD1 d) d.
Proof.
  intros d. right. intros w. unfold mulD1, vupd.
  destruct (V3_eq_dec w Vx) as [->|Hne]; [|apply isle_refl].
  right. unfold mulX, imeet, ile. cbn [fst snd].
  split; [apply zmax_ge_l | apply zmin_le_l].
Qed.

Lemma Pcdiv_y_red : forall d, leI V3 (Pcdiv_y d) d.
Proof. exact (prop_step_reductive Rcdiv_y Pcdiv_y Pcdiv_y_best). Qed.
Lemma Pfdiv_y_red : forall d, leI V3 (Pfdiv_y d) d.
Proof. exact (prop_step_reductive Rfdiv_y Pfdiv_y Pfdiv_y_best). Qed.
Lemma Pcdiv_z_red : forall d, leI V3 (Pcdiv_z d) d.
Proof. exact (prop_step_reductive Rcdiv_z Pcdiv_z Pcdiv_z_best). Qed.
Lemma Pfdiv_z_red : forall d, leI V3 (Pfdiv_z d) d.
Proof. exact (prop_step_reductive Rfdiv_z Pfdiv_z Pfdiv_z_best). Qed.

Lemma mulD2_reductive : forall d, leI V3 (mulD2 d) d.
Proof.
  intros d. unfold mulD2.
  destruct (orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz)));
    [|apply mulD1_reductive].
  eapply leI_trans; [apply (Pfdiv_y_red (Pcdiv_y (mulD1 d)))|].
  eapply leI_trans; [apply (Pcdiv_y_red (mulD1 d))|].
  apply mulD1_reductive.
Qed.

Theorem claim17_reductive : forall d, leI V3 (prop_mul d) d.
Proof.
  intros d. unfold prop_mul.
  destruct (isbotb (mulX d)) eqn:EB.
  { right. intros w. unfold vupd.
    destruct (V3_eq_dec w Vx) as [->|Hne]; [|apply isle_refl].
    left. apply isbotb_isbot. exact EB. }
  destruct (orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy)));
    [|apply mulD2_reductive].
  eapply leI_trans; [apply (Pfdiv_z_red (Pcdiv_z (mulD2 d)))|].
  eapply leI_trans; [apply (Pcdiv_z_red (mulD2 d))|].
  apply mulD2_reductive.
Qed.

Lemma prop_mul_bot_component : forall d,
  isbotI V3 d -> isbotI V3 (prop_mul d).
Proof.
  intros d Hb. exact (leI_bot_out (prop_mul d) d (claim17_reductive d) Hb).
Qed.

(* ==================== Monotonicity helpers ==================== *)

Lemma not_isbot_le : forall i, ~ isbot i -> zle (fst i) (snd i).
Proof. intros [l u] H. apply not_isbot_char in H. cbn [fst snd]. tauto. Qed.

Lemma ile_not_isbot : forall i j, ile i j -> ~ isbot i -> ~ isbot j.
Proof.
  intros i j Hij Hi Hj. exact (Hi (ile_isbot i j Hij Hj)).
Qed.

Lemma guard_le : forall (e e' : istore V3) (w1 w2 : V3),
  (forall w, ile (e w) (e' w)) ->
  orb (notin0b (e' w1)) (notin0b (e' w2)) = true ->
  orb (notin0b (e w1)) (notin0b (e w2)) = true.
Proof.
  intros e e' w1 w2 Hile Hg.
  apply Bool.orb_true_iff in Hg. apply Bool.orb_true_iff.
  destruct Hg as [Hg|Hg].
  - left. exact (notin0_anti _ _ (Hile w1) Hg).
  - right. exact (notin0_anti _ _ (Hile w2) Hg).
Qed.

Lemma guarded_bot :
  forall (R1 R2 : powerset (Asn V3)) (P1 P2 : istore V3 -> istore V3)
         (b : bool) (e : istore V3),
  (forall d, eqI V3 (P1 d) (bestR R1 d)) ->
  (forall d, eqI V3 (P2 d) (bestR R2 d)) ->
  isbotI V3 e -> isbotI V3 (if b then P2 (P1 e) else e).
Proof.
  intros R1 R2 P1 P2 b e H1 H2 Hb. destruct b; [|exact Hb].
  apply (leI_bot_out (P2 (P1 e)) (P1 e) (prop_step_reductive R2 P2 H2 (P1 e))).
  exact (leI_bot_out (P1 e) e (prop_step_reductive R1 P1 H1 e) Hb).
Qed.

Lemma guarded_mono :
  forall (R1 R2 : powerset (Asn V3)) (P1 P2 : istore V3 -> istore V3)
         (b b' : bool) (e e' : istore V3),
  (forall d, eqI V3 (P1 d) (bestR R1 d)) ->
  (forall d, eqI V3 (P2 d) (bestR R2 d)) ->
  leI V3 e e' -> (b' = true -> b = true) ->
  leI V3 (if b then P2 (P1 e) else e) (if b' then P2 (P1 e') else e').
Proof.
  intros R1 R2 P1 P2 b b' e e' H1 H2 Hle Himp.
  destruct b; destruct b'.
  - apply (prop_step_monotone R2 P2 H2).
    apply (prop_step_monotone R1 P1 H1). exact Hle.
  - eapply leI_trans; [apply (prop_step_reductive R2 P2 H2 (P1 e))|].
    eapply leI_trans; [apply (prop_step_reductive R1 P1 H1 e)|]. exact Hle.
  - discriminate (Himp eq_refl).
  - exact Hle.
Qed.

Lemma mulD2_eq : forall d,
  mulD2 d = (if orb (notin0b (mulD1 d Vx)) (notin0b (mulD1 d Vz))
             then Pfdiv_y (Pcdiv_y (mulD1 d)) else mulD1 d).
Proof. reflexivity. Qed.

Lemma prop_mul_eq1 : forall d,
  isbotb (mulX d) = true -> prop_mul d = vupd d Vx (mulX d).
Proof. intros d H. unfold prop_mul. rewrite H. reflexivity. Qed.

Lemma prop_mul_eq2 : forall d,
  isbotb (mulX d) = false ->
  prop_mul d = (if orb (notin0b (mulD2 d Vx)) (notin0b (mulD2 d Vy))
                then Pfdiv_z (Pcdiv_z (mulD2 d)) else mulD2 d).
Proof. intros d H. unfold prop_mul. rewrite H. reflexivity. Qed.

Theorem claim17_monotone : forall d d',
  leI V3 d d' -> leI V3 (prop_mul d) (prop_mul d').
Proof.
  intros d d' Hle.
  destruct (classic (isbotI V3 d)) as [Hbot|Hnb].
  { left. apply prop_mul_bot_component. exact Hbot. }
  assert (Hpt : forall w, isle (d w) (d' w)).
  { destruct Hle as [Hb|Hp]; [contradiction | exact Hp]. }
  assert (Hnbw : forall w, ~ isbot (d w)).
  { intros w Hw. apply Hnb. exists w. exact Hw. }
  assert (Hile : forall w, ile (d w) (d' w)).
  { intros w. destruct (Hpt w) as [Hb|Hi];
      [exfalso; exact (Hnbw w Hb) | exact Hi]. }
  assert (HmulX : ile (mulX d) (mulX d')).
  { unfold mulX. apply imeet_mono; [apply Hile|].
    apply imul_mono;
      [apply not_isbot_le, Hnbw | apply not_isbot_le, Hnbw
       | apply Hile | apply Hile]. }
  destruct (isbotb (mulX d)) eqn:EB.
  { left. rewrite (prop_mul_eq1 d EB). exists Vx.
    rewrite vupd_same. apply isbotb_isbot. exact EB. }
  assert (EB' : isbotb (mulX d') = false).
  { apply isbotb_false. intros Hc. apply isbotb_false in EB. apply EB.
    exact (ile_isbot _ _ HmulX Hc). }
  rewrite (prop_mul_eq2 d EB), (prop_mul_eq2 d' EB').
  assert (Hile1 : forall w, ile (mulD1 d w) (mulD1 d' w)).
  { intros w. unfold mulD1, vupd. destruct (V3_eq_dec w Vx) as [->|Hne].
    - exact HmulX.
    - apply Hile. }
  assert (Hle1 : leI V3 (mulD1 d) (mulD1 d')).
  { right. intros w. right. apply Hile1. }
  assert (Hle2 : leI V3 (mulD2 d) (mulD2 d')).
  { rewrite (mulD2_eq d), (mulD2_eq d').
    apply (guarded_mono Rcdiv_y Rfdiv_y Pcdiv_y Pfdiv_y);
      [exact Pcdiv_y_best | exact Pfdiv_y_best | exact Hle1 |].
    intros Hg'. exact (guard_le (mulD1 d) (mulD1 d') Vx Vz Hile1 Hg'). }
  destruct (classic (isbotI V3 (mulD2 d))) as [Hb2|Hnb2].
  { left. exact (guarded_bot Rcdiv_z Rfdiv_z Pcdiv_z Pfdiv_z _ (mulD2 d)
                   Pcdiv_z_best Pfdiv_z_best Hb2). }
  assert (Hile2 : forall w, ile (mulD2 d w) (mulD2 d' w)).
  { intros w. destruct Hle2 as [Hb|Hp]; [contradiction|].
    destruct (Hp w) as [Hb|Hi];
      [exfalso; apply Hnb2; exists w; exact Hb | exact Hi]. }
  apply (guarded_mono Rcdiv_z Rfdiv_z Pcdiv_z Pfdiv_z);
    [exact Pcdiv_z_best | exact Pfdiv_z_best | exact Hle2 |].
  intros Hg'. exact (guard_le (mulD2 d) (mulD2 d') Vx Vy Hile2 Hg').
Qed.

(* ==================== Best on assignment ==================== *)

Lemma fin_pair_not_bot : forall v : Z, ~ isbot (Fin v, Fin v).
Proof.
  intros v. apply not_isbot_char. split; [apply zle_refl|].
  split; discriminate.
Qed.

Lemma singleton_shape : forall (d : istore V3) (asn : Asn V3),
  (forall a', ibox d a' <-> a' = asn) ->
  forall w, d w = (Fin (asn w), Fin (asn w)).
Proof.
  intros d asn Hsing w.
  assert (Hbox : ibox d asn) by (apply Hsing; reflexivity).
  assert (Huniq : forall v, imem v (d w) -> v = asn w).
  { intros v Hv.
    set (a := fun u => if V3_eq_dec u w then v else asn u).
    assert (Hab : ibox d a).
    { intros u. unfold a. destruct (V3_eq_dec u w) as [->|Hne];
        [exact Hv | apply Hbox]. }
    apply Hsing in Hab.
    assert (Haw : a w = asn w) by (rewrite Hab; reflexivity).
    unfold a in Haw. destruct (V3_eq_dec w w) as [_|Hc]; congruence. }
  pose proof (Hbox w) as Hm.
  destruct (d w) as [l u] eqn:Ed.
  destruct Hm as [Hlo Hhi]. cbn [fst snd] in Hlo, Hhi.
  assert (Hl : l = Fin (asn w)).
  { destruct l as [|a|].
    - exfalso.
      assert (Hmm : imem (asn w - 1) (MInf, u)).
      { split; cbn [fst snd]; [exact I|].
        eapply zle_trans; [|exact Hhi]. simpl. lia. }
      apply Huniq in Hmm. lia.
    - assert (Hmm : imem a (Fin a, u)).
      { split; cbn [fst snd]; [apply zle_refl|].
        eapply zle_trans; [|exact Hhi]. exact Hlo. }
      apply Huniq in Hmm. rewrite Hmm. reflexivity.
    - simpl in Hlo. contradiction. }
  assert (Hu : u = Fin (asn w)).
  { destruct u as [|b|].
    - simpl in Hhi. contradiction.
    - assert (Hmm : imem b (l, Fin b)).
      { split; cbn [fst snd]; [|apply zle_refl].
        eapply zle_trans; [exact Hlo | exact Hhi]. }
      apply Huniq in Hmm. rewrite Hmm. reflexivity.
    - exfalso.
      assert (Hmm : imem (asn w + 1) (l, PInf)).
      { split; cbn [fst snd]; [|exact I].
        eapply zle_trans; [exact Hlo|]. simpl. lia. }
      apply Huniq in Hmm. lia. }
  rewrite Hl, Hu. reflexivity.
Qed.

Lemma bestR_singleton : forall (R : powerset (Asn V3)) (d : istore V3) asn,
  (forall a', ibox d a' <-> a' = asn) -> R asn ->
  forall w, bestR R d w = (Fin (asn w), Fin (asn w)).
Proof.
  intros R d asn Hsing HR w.
  assert (Hbox : ibox d asn) by (apply Hsing; reflexivity).
  assert (Hset : forall v : Z,
    (exists a', (ibox d a' /\ R a') /\ a' w = v) <-> v = asn w).
  { intros v. split.
    - intros [a' [[Hb _] Hv]]. apply Hsing in Hb. subst a'. congruence.
    - intros ->. exists asn. split; [split; assumption | reflexivity]. }
  unfold bestR, ihull, alphai. f_equal.
  - apply zle_antisym.
    + apply zinfS_lb. exists (asn w).
      split; [apply Hset; reflexivity | reflexivity].
    + apply zinfS_greatest. intros x [v [Hv Heq]]. subst x.
      apply Hset in Hv. subst v. apply zle_refl.
  - apply zle_antisym.
    + apply zsup_least. intros x [v [Hv Heq]]. subst x.
      apply Hset in Hv. subst v. apply zle_refl.
    + apply zsup_ub. exists (asn w).
      split; [apply Hset; reflexivity | reflexivity].
Qed.

Lemma step_id : forall (R : powerset (Asn V3)) (P : istore V3 -> istore V3) d asn,
  (forall d0, eqI V3 (P d0) (bestR R d0)) ->
  (forall a', ibox d a' <-> a' = asn) -> R asn ->
  P d = d.
Proof.
  intros R P d asn Hbest Hsing HR.
  pose proof (bestR_singleton R d asn Hsing HR) as Hbs.
  pose proof (singleton_shape d asn Hsing) as Hds.
  assert (Hnb : ~ isbotI V3 (bestR R d)).
  { intros [w Hw]. rewrite Hbs in Hw. exact (fin_pair_not_bot (asn w) Hw). }
  apply functional_extensionality. intros w.
  destruct (Hbest d) as [[_ Hb]|Hp]; [contradiction|].
  destruct (Hp w) as [[_ Hb]|Heq].
  - exfalso. apply Hnb. exists w. exact Hb.
  - rewrite Heq, Hbs, Hds. reflexivity.
Qed.

Lemma imeet_same_singleton : forall v : Z,
  imeet (Fin v, Fin v) (Fin v, Fin v) = (Fin v, Fin v).
Proof.
  intros v. unfold imeet. cbn [fst snd]. rewrite zmax_id, zmin_id. reflexivity.
Qed.

Lemma imeet_singletons_bot : forall a b : Z,
  a <> b -> isbot (imeet (Fin a, Fin a) (Fin b, Fin b)).
Proof.
  intros a b Hab. unfold isbot, imeet, zmin, zmax. cbn [fst snd zleb].
  left. destruct (a <=? b) eqn:E.
  - apply Z.leb_le in E. simpl. lia.
  - apply Z.leb_gt in E. simpl. lia.
Qed.

Theorem claim17_best_on_assignment : forall (d : istore V3) (asn : Asn V3),
  (forall a' : Asn V3, ibox d a' <-> a' = asn) ->
  eqI V3 (prop_mul d) (bestI c_mul3 d).
Proof.
  intros d asn Hsing.
  pose proof (singleton_shape d asn Hsing) as Hds.
  assert (Hbox : ibox d asn) by (apply Hsing; reflexivity).
  destruct (classic (asn Vx = asn Vy * asn Vz)) as [Heq|Hneq].
  - assert (HmX : mulX d = d Vx).
    { unfold mulX. rewrite (Hds Vx), (Hds Vy), (Hds Vz), imul_singleton.
      rewrite <- Heq. apply imeet_same_singleton. }
    assert (HD1 : mulD1 d = d).
    { apply functional_extensionality. intros w. unfold mulD1, vupd.
      destruct (V3_eq_dec w Vx) as [->|Hne]; [exact HmX | reflexivity]. }
    assert (Hbotf : isbotb (mulX d) = false).
    { apply isbotb_false. rewrite HmX, (Hds Vx). apply fin_pair_not_bot. }
    assert (HD2 : mulD2 d = d).
    { rewrite mulD2_eq, HD1.
      destruct (orb (notin0b (d Vx)) (notin0b (d Vz))) eqn:Eg; [|reflexivity].
      assert (Hz : asn Vz <> 0) by exact (guard_yz_nonzero d asn Hbox Heq Eg).
      rewrite (step_id Rcdiv_y Pcdiv_y d asn Pcdiv_y_best Hsing
                 (sol_Rcdiv_y asn Heq Hz)).
      exact (step_id Rfdiv_y Pfdiv_y d asn Pfdiv_y_best Hsing
               (sol_Rfdiv_y asn Heq Hz)). }
    assert (HPM : prop_mul d = d).
    { rewrite (prop_mul_eq2 d Hbotf), HD2.
      destruct (orb (notin0b (d Vx)) (notin0b (d Vy))) eqn:Eg; [|reflexivity].
      assert (Hy : asn Vy <> 0) by exact (guard_zy_nonzero d asn Hbox Heq Eg).
      rewrite (step_id Rcdiv_z Pcdiv_z d asn Pcdiv_z_best Hsing
                 (sol_Rcdiv_z asn Heq Hy)).
      exact (step_id Rfdiv_z Pfdiv_z d asn Pfdiv_z_best Hsing
               (sol_Rfdiv_z asn Heq Hy)). }
    right. intros w. right.
    rewrite HPM, bestI_is_bestR.
    rewrite (bestR_singleton (rel c_mul3) d asn Hsing
               (proj2 (rel_mul3_char asn) Heq) w).
    exact (Hds w).
  - assert (Hbotm : isbot (mulX d)).
    { unfold mulX. rewrite (Hds Vx), (Hds Vy), (Hds Vz), imul_singleton.
      apply imeet_singletons_bot. exact Hneq. }
    left. split.
    + rewrite (prop_mul_eq1 d (proj2 (isbotb_isbot (mulX d)) Hbotm)).
      exists Vx. rewrite vupd_same. exact Hbotm.
    + rewrite bestI_is_bestR. apply (no_sol_bestR_bot (rel c_mul3) d Vx).
      intros a' Hb HR. apply Hsing in Hb. subst a'.
      apply Hneq. apply rel_mul3_char. exact HR.
Qed.

(* ======================= CLAIM 17 ======================= *)
Theorem claim17 :
  (forall d, leI V3 (bestI c_mul3 d) (prop_mul d)) /\
  (forall d, leI V3 (prop_mul d) d) /\
  (forall d d', leI V3 d d' -> leI V3 (prop_mul d) (prop_mul d')) /\
  (forall (d : istore V3) (asn : Asn V3),
     (forall a' : Asn V3, ibox d a' <-> a' = asn) ->
     eqI V3 (prop_mul d) (bestI c_mul3 d)).
Proof.
  split; [exact claim17_sound|].
  split; [exact claim17_reductive|].
  split; [exact claim17_monotone | exact claim17_best_on_assignment].
Qed.
