From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Export ZItv.
Open Scope Z_scope.

Record zitv3 := ZItv3 { x : zitv ; sy3 : zitv ; sz3 : zitv }.

Definition in_zitv3 (s : zitv3) (vx vy vz : Z) : Prop :=
  contains (x s) vx /\ contains (sy3 s) vy /\ contains (sz3 s) vz.

Definition ne_zitv3 (s : zitv3) : bool :=
  (is_not_bot_zitv (x s) && is_not_bot_zitv (sy3 s) && is_not_bot_zitv (sz3 s))%bool.

Definition sjoin3 (s t : zitv3) : zitv3 :=
  ZItv3 (join_nobot_zitv (x s) (x t)) (join_nobot_zitv (sy3 s) (sy3 t)) (join_nobot_zitv (sz3 s) (sz3 t)).

Definition sqcupbot3 (s t : zitv3) : zitv3 :=
  if ne_zitv3 s
  then (if ne_zitv3 t then sjoin3 s t else s)
  else t.

(* interval order (containment) and store order — QUOTIENTED: every empty
   interval / failed store is identified with bottom and sits below all,
   matching the lattice \widetilde{I} and \mathbf{I} of the paper (the
   [is_not_bot_zitv(a,b) \/ ...] / [isboti(d) \/ ...] disjunctions). *)
Definition sle3 (a b : zitv3) : Prop :=
  ne_zitv3 a = false \/
  (leq_zitv (x a) (x b) /\ leq_zitv (sy3 a) (sy3 b) /\ leq_zitv (sz3 a) (sz3 b)).


Lemma sle3_intro : forall a b,
  leq_zitv (x a) (x b) -> leq_zitv (sy3 a) (sy3 b) -> leq_zitv (sz3 a) (sz3 b) -> sle3 a b.
Proof. intros a b Hx Hy Hz; right; split; [exact Hx | split; [exact Hy | exact Hz]]. Qed.

Lemma sle3_bot : forall a b, ne_zitv3 a = false -> sle3 a b.
Proof. intros a b H; left; exact H. Qed.

Lemma sle3_ne_inv : forall a b, ne_zitv3 a = true -> sle3 a b ->
  leq_zitv (x a) (x b) /\ leq_zitv (sy3 a) (sy3 b) /\ leq_zitv (sz3 a) (sz3 b).
Proof. intros a b Hne [Hb | Hraw]; [ rewrite Hne in Hb; discriminate | exact Hraw ]. Qed.

Lemma ne_zitv3_parts : forall s, ne_zitv3 s = true ->
  is_not_bot_zitv (x s) = true /\ is_not_bot_zitv (sy3 s) = true /\ is_not_bot_zitv (sz3 s) = true.
Proof.
  intros s H. unfold ne_zitv3 in H.
  apply andb_true_iff in H as [H Hz]. apply andb_true_iff in H as [Hx Hy].
  split; [exact Hx | split; [exact Hy | exact Hz]].
Qed.

Lemma ile3_refl : forall i, leq_zitv i i.
Proof. intro i; apply leq_zitv_intro; apply leq_zinf_refl. Qed.

Lemma ile3_trans : forall i j k, leq_zitv i j -> leq_zitv j k -> leq_zitv i k.
Proof.
  intros i j k H1 H2.
  destruct (is_not_bot_zitv i) eqn:Ei; [ | apply bot_is_leq_all_zitv; exact Ei ].
  apply (all_is_geq_bot_zitv i j Ei) in H1 as [Hl1 Hh1].
  assert (Enj : is_not_bot_zitv j = true) by (apply (contains_not_bot_implies_not_bot_zitv i j Ei Hl1 Hh1)).
  apply (all_is_geq_bot_zitv j k Enj) in H2 as [Hl2 Hh2].
  apply leq_zitv_intro; eapply leq_zinf_trans; eassumption.
Qed.

Lemma inter3_ile3_l : forall i j, leq_zitv (meet_zitv i j) i.
Proof.
  intros i j; apply leq_zitv_intro; unfold meet_zitv; cbn [lb ub];
  [ apply leq_zinf_max_zinf_l | apply leq_zinf_min_zinf_l ].
Qed.

(* the NAIVE join is a LUB only when both inputs are non-empty (the quotient
   order collapses empties, so [join_nobot_zitv] may overshoot on an empty input) *)
Lemma ijoin3_ile3 : forall i j k,
  is_not_bot_zitv i = true -> is_not_bot_zitv j = true ->
  leq_zitv i k -> leq_zitv j k -> leq_zitv (join_nobot_zitv i j) k.
Proof.
  intros i j k Ei Ej H1 H2.
  apply (all_is_geq_bot_zitv i k Ei) in H1 as [Hli Hhi].
  apply (all_is_geq_bot_zitv j k Ej) in H2 as [Hlj Hhj].
  apply leq_zitv_intro; unfold join_nobot_zitv; cbn [lb ub].
  - apply leq_zinf_min_zinf_glb; assumption.
  - apply max_zinf_lub; assumption.
Qed.

Lemma sle3_trans : forall a b c, sle3 a b -> sle3 b c -> sle3 a c.
Proof.
  intros a b c H1 H2.
  destruct (ne_zitv3 a) eqn:Ea; [ | apply sle3_bot; exact Ea ].
  apply (sle3_ne_inv a b Ea) in H1 as (Hx1 & Hy1 & Hz1).
  apply ne_zitv3_parts in Ea as (Eax & Eay & Eaz).
  assert (Ebx : is_not_bot_zitv (x b) = true).
  { apply (all_is_geq_bot_zitv _ _ Eax) in Hx1 as [Hl Hh]. apply (contains_not_bot_implies_not_bot_zitv _ _ Eax Hl Hh). }
  assert (Eby : is_not_bot_zitv (sy3 b) = true).
  { apply (all_is_geq_bot_zitv _ _ Eay) in Hy1 as [Hl Hh]. apply (contains_not_bot_implies_not_bot_zitv _ _ Eay Hl Hh). }
  assert (Ebz : is_not_bot_zitv (sz3 b) = true).
  { apply (all_is_geq_bot_zitv _ _ Eaz) in Hz1 as [Hl Hh]. apply (contains_not_bot_implies_not_bot_zitv _ _ Eaz Hl Hh). }
  assert (Eb : ne_zitv3 b = true)
    by (unfold ne_zitv3; rewrite Ebx, Eby, Ebz; reflexivity).
  apply (sle3_ne_inv b c Eb) in H2 as (Hx2 & Hy2 & Hz2).
  apply sle3_intro; eapply ile3_trans; eassumption.
Qed.


Lemma sqcupbot3_ile : forall a b t, sle3 a t -> sle3 b t -> sle3 (sqcupbot3 a b) t.
Proof.
  intros a b t Ha Hb. unfold sqcupbot3.
  destruct (ne_zitv3 a) eqn:Ea; destruct (ne_zitv3 b) eqn:Eb; cbn iota; try assumption.
  apply ne_zitv3_parts in Ea as (Eax & Eay & Eaz).
  apply ne_zitv3_parts in Eb as (Ebx & Eby & Ebz).
  apply (sle3_ne_inv a t) in Ha; [ | unfold ne_zitv3; rewrite Eax,Eay,Eaz; reflexivity ].
  apply (sle3_ne_inv b t) in Hb; [ | unfold ne_zitv3; rewrite Ebx,Eby,Ebz; reflexivity ].
  destruct Ha as (Hax & Hay & Haz). destruct Hb as (Hbx & Hby & Hbz).
  apply sle3_intro; unfold sjoin3; cbn [x sy3 sz3]; apply ijoin3_ile3; assumption.
Qed.


Lemma ne_inter3 : forall i j, is_not_bot_zitv (meet_zitv i j) = true -> is_not_bot_zitv i = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]]; cbn; intros H; try reflexivity; try discriminate;
    apply Z.leb_le; apply Z.leb_le in H; lia.
Qed.

(* ================================================================== *)
(** ** Generic closure machinery over the QUOTIENT order.

    Any propagator that is sound, a best transformer (complete), and
    ne-feasible is UNCONDITIONALLY a lower closure operator: reductive,
    monotone, and idempotent up to the bottom equivalence (mutual
    [sle3]).  This is the payoff of quotienting: no feasibility guard. *)
(* ================================================================== *)

Definition contains3 (P : Z -> Z -> Z -> Prop) (s t : zitv3) : Prop :=
  forall vx vy vz, in_zitv3 s vx vy vz -> P vx vy vz -> in_zitv3 t vx vy vz.
Definition feasible3 (P : Z -> Z -> Z -> Prop) (s : zitv3) : Prop :=
  exists vx vy vz, in_zitv3 s vx vy vz /\ P vx vy vz.

Lemma contains_nonempty : forall i v, contains i v -> is_not_bot_zitv i = true.
Proof. intros [[a| |] [b| |]] v [H1 H2]; cbn in *; try easy; apply Z.leb_le; lia. Qed.

Lemma contains_ile3 : forall i j v, leq_zitv i j -> contains i v -> contains j v.
Proof.
  intros i j v Hij Hm. pose proof (contains_nonempty _ _ Hm) as Hne.
  apply (all_is_geq_bot_zitv i j Hne) in Hij as [Hl Hh]. destruct Hm as [M1 M2].
  split; [ eapply leq_zinf_trans; [exact Hl | exact M1] | eapply leq_zinf_trans; [exact M2 | exact Hh] ].
Qed.

Lemma in_zitv3_sle3 : forall s t vx vy vz,
  sle3 s t -> in_zitv3 s vx vy vz -> in_zitv3 t vx vy vz.
Proof.
  intros s t vx vy vz Hst (Hx & Hy & Hz).
  assert (Ene : ne_zitv3 s = true) by
    (unfold ne_zitv3; rewrite (contains_nonempty _ _ Hx),(contains_nonempty _ _ Hy),(contains_nonempty _ _ Hz); reflexivity).
  apply (sle3_ne_inv s t Ene) in Hst as (Hix & Hiy & Hiz).
  split; [ apply (contains_ile3 _ _ _ Hix Hx)
         | split; [ apply (contains_ile3 _ _ _ Hiy Hy) | apply (contains_ile3 _ _ _ Hiz Hz) ] ].
Qed.

Lemma closure_laws :
  forall (P : Z -> Z -> Z -> Prop) (f : zitv3 -> zitv3),
  (forall s vx vy vz, in_zitv3 s vx vy vz -> P vx vy vz -> in_zitv3 (f s) vx vy vz) ->
  (forall s, feasible3 P s -> forall t, contains3 P s t -> sle3 (f s) t) ->
  (forall s, ne_zitv3 (f s) = true -> feasible3 P s) ->
  (forall s, sle3 (f s) s)
  /\ (forall s t, sle3 s t -> sle3 (f s) (f t))
  /\ (forall s, sle3 (f (f s)) (f s) /\ sle3 (f s) (f (f s))).
Proof.
  intros P f Hsound Hbest Hnef.
  assert (Hred : forall s, sle3 (f s) s).
  { intro s. destruct (ne_zitv3 (f s)) eqn:E; [ | apply sle3_bot; exact E ].
    apply Hbest; [ apply Hnef; exact E | ]. intros vx vy vz Hin _; exact Hin. }
  split; [ exact Hred | ]. split.
  - intros s t Hst. destruct (ne_zitv3 (f s)) eqn:E; [ | apply sle3_bot; exact E ].
    apply Hbest; [ apply Hnef; exact E | ].
    intros vx vy vz Hin HP.
    apply (Hsound t); [ apply (in_zitv3_sle3 s t _ _ _ Hst Hin) | exact HP ].
  - intro s. split; [ apply Hred | ].
    destruct (ne_zitv3 (f s)) eqn:E; [ | apply sle3_bot; exact E ].
    apply Hbest; [ apply Hnef; exact E | ].
    intros vx vy vz Hin HP.
    apply (Hsound (f s)); [ apply (Hsound s _ _ _ Hin HP) | exact HP ].
Qed.
