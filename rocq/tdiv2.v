(** * tdiv2: the truncated-division propagator, built from floor and ceiling

    Truncated division ([Z.quot], the C/GPU [/] on integers) agrees with
    floor division when the operands have the same sign, and with ceiling
    division when they have opposite signs:

        y >= 0, z >= 1 :  y quot z = y / z          (floor)
        y <= 0, z <= -1:  y quot z = y / z          (floor)
        y >= 0, z <= -1:  y quot z = cdiv y z       (ceiling)
        y <= 0, z >= 1 :  y quot z = cdiv y z       (ceiling)

    The truncated-division propagator therefore splits the input box into the
    four sign quadrants of (y,z), runs the verified floor propagator
    ([fdiv2.propagator]) on the same-sign quadrants and the verified ceiling
    propagator ([cdiv2.cpropagator]) on the mixed-sign quadrants, and joins
    the four results with the bottom-absorbing join [sqcupbot].

    We prove:
      - soundness  : [tdiv_soundness]
      - optimality : [tdiv_best]  (best abstract transformer on feasible boxes)
*)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv2 cdiv2.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Truncated solutions and the sign-case equivalences               *)
(* ------------------------------------------------------------------ *)

Definition tsol (x y z : Z) : Prop := z <> 0 /\ x = Z.quot y z.

(** Equality form of the four sign cases. *)
Lemma tquot_pp : forall y z, 0 <= y -> 0 < z -> Z.quot y z = y / z.
Proof. intros y z Hy Hz. apply Z.quot_div_nonneg; assumption. Qed.

Lemma tquot_nn : forall y z, y <= 0 -> z < 0 -> Z.quot y z = y / z.
Proof.
  intros y z Hy Hz.
  rewrite <- (Z.quot_opp_opp y z) by lia.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_opp_opp; lia.
Qed.

Lemma tquot_pn : forall y z, 0 <= y -> z < 0 -> Z.quot y z = cdiv y z.
Proof.
  intros y z Hy Hz. unfold cdiv.
  pose proof (Z.quot_opp_r y (- z) ltac:(lia)) as E2.
  replace (- - z) with z in E2 by lia.
  rewrite E2.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_opp_opp y (- z) ltac:(lia)) as E3.
  replace (- - z) with z in E3 by lia.
  rewrite <- E3. reflexivity.
Qed.

Lemma tquot_np : forall y z, y <= 0 -> 0 < z -> Z.quot y z = cdiv y z.
Proof.
  intros y z Hy Hz. unfold cdiv.
  pose proof (Z.quot_opp_l (- y) z ltac:(lia)) as E.
  replace (- - y) with y in E by lia.
  rewrite E.
  rewrite Z.quot_div_nonneg by lia.
  reflexivity.
Qed.

(** Iff form, as advertised. *)
Lemma tsol_pp : forall x y z, 0 <= y -> 0 < z -> (x = Z.quot y z <-> x = y / z).
Proof. intros x y z Hy Hz. rewrite (tquot_pp y z Hy Hz). tauto. Qed.

Lemma tsol_nn : forall x y z, y <= 0 -> z < 0 -> (x = Z.quot y z <-> x = y / z).
Proof. intros x y z Hy Hz. rewrite (tquot_nn y z Hy Hz). tauto. Qed.

Lemma tsol_pn : forall x y z, 0 <= y -> z < 0 -> (x = Z.quot y z <-> x = cdiv y z).
Proof. intros x y z Hy Hz. rewrite (tquot_pn y z Hy Hz). tauto. Qed.

Lemma tsol_np : forall x y z, y <= 0 -> 0 < z -> (x = Z.quot y z <-> x = cdiv y z).
Proof. intros x y z Hy Hz. rewrite (tquot_np y z Hy Hz). tauto. Qed.

(* ------------------------------------------------------------------ *)
(** ** Quadrant restrictions and the propagator                         *)
(* ------------------------------------------------------------------ *)

Definition restrict_y_pos (s : store) : store :=
  St (sx s) (inter (sy s) (Itv 0 (hi (sy s)))) (sz s).
Definition restrict_y_neg (s : store) : store :=
  St (sx s) (inter (sy s) (Itv (lo (sy s)) 0)) (sz s).

Definition Q1 (s : store) : store := restrict_z_pos (restrict_y_pos s).  (* y>=0, z>=1  *)
Definition Q2 (s : store) : store := restrict_z_neg (restrict_y_pos s).  (* y>=0, z<=-1 *)
Definition Q3 (s : store) : store := restrict_z_pos (restrict_y_neg s).  (* y<=0, z>=1  *)
Definition Q4 (s : store) : store := restrict_z_neg (restrict_y_neg s).  (* y<=0, z<=-1 *)

Definition tpropagator (s : store) : store :=
  sqcupbot (sqcupbot (propagator (Q4 s)) (cpropagator (Q3 s)))
           (sqcupbot (cpropagator (Q2 s)) (propagator (Q1 s))).

(* ------------------------------------------------------------------ *)
(** ** Quadrant membership, in and out                                  *)
(* ------------------------------------------------------------------ *)

Lemma in_Q1 : forall s vx vy vz,
  in_store s vx vy vz -> 0 <= vy -> 0 < vz -> in_store (Q1 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Hy0 Hz0.
  unfold Q1, restrict_z_pos, restrict_y_pos, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

Lemma in_Q2 : forall s vx vy vz,
  in_store s vx vy vz -> 0 <= vy -> vz < 0 -> in_store (Q2 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Hy0 Hz0.
  unfold Q2, restrict_z_neg, restrict_y_pos, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

Lemma in_Q3 : forall s vx vy vz,
  in_store s vx vy vz -> vy <= 0 -> 0 < vz -> in_store (Q3 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Hy0 Hz0.
  unfold Q3, restrict_z_pos, restrict_y_neg, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

Lemma in_Q4 : forall s vx vy vz,
  in_store s vx vy vz -> vy <= 0 -> vz < 0 -> in_store (Q4 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Hy0 Hz0.
  unfold Q4, restrict_z_neg, restrict_y_neg, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

Lemma Q1_proj : forall s vx vy vz,
  in_store (Q1 s) vx vy vz -> in_store s vx vy vz /\ 0 <= vy /\ 0 < vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz).
  unfold Q1, restrict_z_pos, restrict_y_pos, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

Lemma Q2_proj : forall s vx vy vz,
  in_store (Q2 s) vx vy vz -> in_store s vx vy vz /\ 0 <= vy /\ vz < 0.
Proof.
  intros s vx vy vz (Hx & Hy & Hz).
  unfold Q2, restrict_z_neg, restrict_y_pos, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

Lemma Q3_proj : forall s vx vy vz,
  in_store (Q3 s) vx vy vz -> in_store s vx vy vz /\ vy <= 0 /\ 0 < vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz).
  unfold Q3, restrict_z_pos, restrict_y_neg, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

Lemma Q4_proj : forall s vx vy vz,
  in_store (Q4 s) vx vy vz -> in_store s vx vy vz /\ vy <= 0 /\ vz < 0.
Proof.
  intros s vx vy vz (Hx & Hy & Hz).
  unfold Q4, restrict_z_neg, restrict_y_neg, in_store, mem, inter in *; cbn in *.
  repeat split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Soundness                                                        *)
(* ------------------------------------------------------------------ *)

Theorem tdiv_soundness : forall s vx vy vz,
  in_store s vx vy vz -> tsol vx vy vz -> in_store (tpropagator s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hts.
  destruct Hts as [Hnz Hq].
  unfold tpropagator.
  destruct (Z.le_ge_cases 0 vy) as [Hy|Hy];
  destruct (Z.lt_trichotomy vz 0) as [Hz|[Hz|Hz]]; try (exfalso; lia).
  - (* 0 <= vy, vz < 0 : Q2, ceiling *)
    apply sqcupbot_pres_r. apply sqcupbot_pres_l.
    apply cdiv_soundness.
    + apply in_Q2; auto.
    + split; [exact Hnz|]. rewrite <- (tquot_pn vy vz Hy Hz). exact Hq.
  - (* 0 <= vy, 0 < vz : Q1, floor *)
    apply sqcupbot_pres_r. apply sqcupbot_pres_r.
    apply fdiv_soundness.
    + apply in_Q1; auto.
    + split; [exact Hnz|]. rewrite <- (tquot_pp vy vz Hy Hz). exact Hq.
  - (* vy <= 0, vz < 0 : Q4, floor *)
    apply sqcupbot_pres_l. apply sqcupbot_pres_l.
    apply fdiv_soundness.
    + apply in_Q4; auto.
    + split; [exact Hnz|]. rewrite <- (tquot_nn vy vz Hy Hz). exact Hq.
  - (* vy <= 0, 0 < vz : Q3, ceiling *)
    apply sqcupbot_pres_l. apply sqcupbot_pres_r.
    apply cdiv_soundness.
    + apply in_Q3; auto.
    + split; [exact Hnz|]. rewrite <- (tquot_np vy vz Hy Hz). exact Hq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Optimality (best abstract transformer)                           *)
(* ------------------------------------------------------------------ *)

Definition contains_tsols (s t : store) : Prop :=
  forall vx vy vz, in_store s vx vy vz -> tsol vx vy vz -> in_store t vx vy vz.
Definition tfeasible (s : store) : Prop :=
  exists vx vy vz, in_store s vx vy vz /\ tsol vx vy vz.

(** New brick: a non-empty floor-propagator output certifies feasibility of
    its input (the propagator's y-bounds are attained by actual solutions). *)
Lemma fdiv_ne_feasible : forall s, ne_store (propagator s) = true -> feasible s.
Proof.
  intros s Hne.
  destruct (ne_store_bounds _ Hne) as (Hx & Hy & Hz).
  assert (Hcons : consistent (propagator s)) by (split; [exact Hx | split; assumption]).
  destruct (y_attain s Hcons) as [(x & z & Hin & Hsol) _].
  exists x, (lo (sy (propagator s))), z. split; assumption.
Qed.

Lemma cdiv_ne_feasible : forall s, ne_store (cpropagator s) = true -> cfeasible s.
Proof.
  intros s Hne.
  unfold cpropagator in Hne. rewrite ne_negs in Hne.
  apply <- cfeasible_feasible. apply fdiv_ne_feasible. exact Hne.
Qed.

(** Any floor solution of a quadrant store is a truncated solution of [s]. *)
Lemma contains_tsols_Q1 : forall s t, contains_tsols s t -> contains_sols (Q1 s) t.
Proof.
  intros s t H vx vy vz Hin [Hnz He].
  destruct (Q1_proj _ _ _ _ Hin) as (Hin' & Hy & Hz).
  apply H; [exact Hin'|].
  split; [exact Hnz|]. rewrite (tquot_pp vy vz Hy Hz). exact He.
Qed.

Lemma contains_tsols_Q2 : forall s t, contains_tsols s t -> contains_csols (Q2 s) t.
Proof.
  intros s t H vx vy vz Hin [Hnz He].
  destruct (Q2_proj _ _ _ _ Hin) as (Hin' & Hy & Hz).
  apply H; [exact Hin'|].
  split; [exact Hnz|]. rewrite (tquot_pn vy vz Hy Hz). exact He.
Qed.

Lemma contains_tsols_Q3 : forall s t, contains_tsols s t -> contains_csols (Q3 s) t.
Proof.
  intros s t H vx vy vz Hin [Hnz He].
  destruct (Q3_proj _ _ _ _ Hin) as (Hin' & Hy & Hz).
  apply H; [exact Hin'|].
  split; [exact Hnz|]. rewrite (tquot_np vy vz Hy Hz). exact He.
Qed.

Lemma contains_tsols_Q4 : forall s t, contains_tsols s t -> contains_sols (Q4 s) t.
Proof.
  intros s t H vx vy vz Hin [Hnz He].
  destruct (Q4_proj _ _ _ _ Hin) as (Hin' & Hy & Hz).
  apply H; [exact Hin'|].
  split; [exact Hnz|]. rewrite (tquot_nn vy vz Hy Hz). exact He.
Qed.

(** Case dispatch for a bottom-absorbing join known to be non-empty. *)
Lemma sqcupbot_sle_cases : forall a b t,
  (ne_store a = true -> sle a t) ->
  (ne_store b = true -> sle b t) ->
  ne_store (sqcupbot a b) = true ->
  sle (sqcupbot a b) t.
Proof.
  intros a b t Ha Hb Hne.
  destruct (ne_store a) eqn:Ea.
  - destruct (ne_store b) eqn:Eb.
    + apply sqcupbot_ile; [apply Ha; reflexivity | apply Hb; reflexivity].
    + assert (E : sqcupbot a b = a) by (unfold sqcupbot; rewrite Ea, Eb; reflexivity).
      rewrite E. apply Ha; reflexivity.
  - assert (E : sqcupbot a b = b) by (unfold sqcupbot; rewrite Ea; reflexivity).
    rewrite E in Hne. rewrite E. apply Hb; exact Hne.
Qed.

Theorem tdiv_best : forall s, tfeasible s -> forall t, contains_tsols s t ->
  sle (tpropagator s) t.
Proof.
  intros s Hf t Hct.
  assert (HneT : ne_store (tpropagator s) = true).
  { destruct Hf as (vx & vy & vz & Hin & Hts).
    exact (ne_store_true _ _ _ _ (tdiv_soundness _ _ _ _ Hin Hts)). }
  unfold tpropagator in HneT |- *.
  apply sqcupbot_sle_cases; [ | | exact HneT ].
  - intro E. apply sqcupbot_sle_cases; [ | | exact E ].
    + intro E'.
      exact (fdiv_best (Q4 s) (fdiv_ne_feasible _ E') t (contains_tsols_Q4 s t Hct)).
    + intro E'.
      exact (cdiv_best (Q3 s) (cdiv_ne_feasible _ E') t (contains_tsols_Q3 s t Hct)).
  - intro E. apply sqcupbot_sle_cases; [ | | exact E ].
    + intro E'.
      exact (cdiv_best (Q2 s) (cdiv_ne_feasible _ E') t (contains_tsols_Q2 s t Hct)).
    + intro E'.
      exact (fdiv_best (Q1 s) (fdiv_ne_feasible _ E') t (contains_tsols_Q1 s t Hct)).
Qed.
