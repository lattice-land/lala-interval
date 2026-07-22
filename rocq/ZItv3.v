From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Export ZItv.
Open Scope Z_scope.

Record zitv3 := ZItv3 { x : zitv ; y : zitv ; z : zitv }.

Definition in_zitv3 (s : zitv3) (vx vy vz : Z) : Prop :=
  in_zitv (x s) vx /\ in_zitv (y s) vy /\ in_zitv (z s) vz.

Definition is_not_bot_zitv3 (s : zitv3) : bool :=
  (is_not_bot_zitv (x s) && is_not_bot_zitv (y s) && is_not_bot_zitv (z s))%bool.

Definition join_nobot_zitv3 (s t : zitv3) : zitv3 :=
  ZItv3 (join_nobot_zitv (x s) (x t)) (join_nobot_zitv (y s) (y t)) (join_nobot_zitv (z s) (z t)).

Definition join_zitv3 (a b : zitv3) : zitv3 :=
  if negb (is_not_bot_zitv3 a) then b
  else if negb (is_not_bot_zitv3 b) then a
  else join_nobot_zitv3 a b.

(* interval order (containment) and store order — QUOTIENTED: every empty
   interval / failed store is identified with bottom and sits below all,
   matching the lattice \widetilde{I} and \mathbf{I} of the paper (the
   [is_not_bot_zitv(a,b) \/ ...] / [isboti(d) \/ ...] disjunctions). *)
Definition leq_zitv3 (a b : zitv3) : Prop :=
  is_not_bot_zitv3 a = false \/
  (leq_zitv (x a) (x b) /\ leq_zitv (y a) (y b) /\ leq_zitv (z a) (z b)).

Lemma leq_zitv3_intro : forall a b,
  leq_zitv (x a) (x b) -> leq_zitv (y a) (y b) -> leq_zitv (z a) (z b) -> leq_zitv3 a b.
Proof. intros a b Hx Hy Hz; right; split; [exact Hx | split; [exact Hy | exact Hz]]. Qed.

Lemma bot_is_leq_all_zitv3 : forall a b, is_not_bot_zitv3 a = false -> leq_zitv3 a b.
Proof. intros a b H; left; exact H. Qed.

Lemma leq_zitv3_nobot_inv : forall a b, is_not_bot_zitv3 a = true -> leq_zitv3 a b ->
  leq_zitv (x a) (x b) /\ leq_zitv (y a) (y b) /\ leq_zitv (z a) (z b).
Proof. intros a b Hne [Hb | Hraw]; [ rewrite Hne in Hb; discriminate | exact Hraw ]. Qed.

(* cw = component-wise *)
Lemma not_bot_zitv3_distributes_cw : forall s, is_not_bot_zitv3 s = true ->
  is_not_bot_zitv (x s) = true /\ is_not_bot_zitv (y s) = true /\ is_not_bot_zitv (z s) = true.
Proof.
  intros s H. unfold is_not_bot_zitv3 in H.
  apply andb_true_iff in H as [H Hz]. apply andb_true_iff in H as [Hx Hy].
  split; [exact Hx | split; [exact Hy | exact Hz]].
Qed.

(* ---- non-emptiness from membership ---- *)
Lemma nonempty_is_not_bot_zitv3 : forall s a b c, in_zitv3 s a b c -> is_not_bot_zitv3 s = true.
Proof.
  intros s a b c (Hx & Hy & Hz). unfold is_not_bot_zitv3.
  rewrite (nonempty_is_not_bot_zitv _ _ Hx), (nonempty_is_not_bot_zitv _ _ Hy), (nonempty_is_not_bot_zitv _ _ Hz).
  reflexivity.
Qed.

(* Convenience functions to negate some variables in the store. *)
Definition neg_yz_zitv3 (s : zitv3) : zitv3 :=
  ZItv3 (x s) (neg_zitv (y s)) (neg_zitv (z s)).
Definition neg_xy_zitv3 (s : zitv3) : zitv3 :=
  ZItv3 (neg_zitv (x s)) (neg_zitv (y s)) (z s).
Definition neg_xz_zitv3 (s : zitv3) : zitv3 :=
  ZItv3 (neg_zitv (x s)) (y s) (neg_zitv (z s)).

(* TODO: following lemmas are not fully renamed yet. *)

(* the NAIVE join is a LUB only when both inputs are non-empty (the quotient
   order collapses empties, so [join_nobot_zitv] may overshoot on an empty input) *)
Lemma ijoin_leq_zitv3 : forall i j k,
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

Lemma leq_zitv_transitivityitivity : forall a b c, leq_zitv3 a b -> leq_zitv3 b c -> leq_zitv3 a c.
Proof.
  intros a b c H1 H2.
  destruct (is_not_bot_zitv3 a) eqn:Ea; [ | apply bot_is_leq_all_zitv3; exact Ea ].
  apply (leq_zitv3_nobot_inv a b Ea) in H1 as (Hx1 & Hy1 & Hz1).
  apply not_bot_zitv3_distributes_cw in Ea as (Eax & Eay & Eaz).
  assert (Ebx : is_not_bot_zitv (x b) = true).
  { apply (all_is_geq_bot_zitv _ _ Eax) in Hx1 as [Hl Hh]. apply (contains_not_bot_implies_not_bot_zitv _ _ Eax Hl Hh). }
  assert (Eby : is_not_bot_zitv (y b) = true).
  { apply (all_is_geq_bot_zitv _ _ Eay) in Hy1 as [Hl Hh]. apply (contains_not_bot_implies_not_bot_zitv _ _ Eay Hl Hh). }
  assert (Ebz : is_not_bot_zitv (z b) = true).
  { apply (all_is_geq_bot_zitv _ _ Eaz) in Hz1 as [Hl Hh]. apply (contains_not_bot_implies_not_bot_zitv _ _ Eaz Hl Hh). }
  assert (Eb : is_not_bot_zitv3 b = true)
    by (unfold is_not_bot_zitv3; rewrite Ebx, Eby, Ebz; reflexivity).
  apply (leq_zitv3_nobot_inv b c Eb) in H2 as (Hx2 & Hy2 & Hz2).
  apply leq_zitv3_intro; eapply leq_zitv_transitivity; eassumption.
Qed.


Lemma sqcupbot3_ile : forall a b t, leq_zitv3 a t -> leq_zitv3 b t -> leq_zitv3 (join_zitv3 a b) t.
Proof.
  intros a b t Ha Hb. unfold join_zitv3.
  destruct (is_not_bot_zitv3 a) eqn:Ea; destruct (is_not_bot_zitv3 b) eqn:Eb; cbn iota; try assumption.
  apply not_bot_zitv3_distributes_cw in Ea as (Eax & Eay & Eaz).
  apply not_bot_zitv3_distributes_cw in Eb as (Ebx & Eby & Ebz).
  apply (leq_zitv3_nobot_inv a t) in Ha; [ | unfold is_not_bot_zitv3; rewrite Eax,Eay,Eaz; reflexivity ].
  apply (leq_zitv3_nobot_inv b t) in Hb; [ | unfold is_not_bot_zitv3; rewrite Ebx,Eby,Ebz; reflexivity ].
  destruct Ha as (Hax & Hay & Haz). destruct Hb as (Hbx & Hby & Hbz).
  apply leq_zitv3_intro; unfold join_nobot_zitv3; cbn [x y z]; apply ijoin_leq_zitv3; assumption.
Qed.

(* ================================================================== *)
(** ** Generic closure machinery over the QUOTIENT order.

    Any propagator that is sound, a best transformer (complete), and
    ne-feasible is UNCONDITIONALLY a lower closure operator: reductive,
    monotone, and idempotent up to the bottom equivalence (mutual
    [leq_zitv3]).  This is the payoff of quotienting: no feasibility guard. *)
(* ================================================================== *)

Definition preserve_solutions (P : Z -> Z -> Z -> Prop) (s t : zitv3) : Prop :=
  forall vx vy vz, in_zitv3 s vx vy vz -> P vx vy vz -> in_zitv3 t vx vy vz.
Definition feasible (P : Z -> Z -> Z -> Prop) (s : zitv3) : Prop :=
  exists vx vy vz, in_zitv3 s vx vy vz /\ P vx vy vz.

Lemma contains_nonempty : forall i v, in_zitv i v -> is_not_bot_zitv i = true.
Proof. intros [[a| |] [b| |]] v [H1 H2]; cbn in *; try easy; apply Z.leb_le; lia. Qed.

Lemma contains_leq_zitv3 : forall i j v, leq_zitv i j -> in_zitv i v -> in_zitv j v.
Proof.
  intros i j v Hij Hm. pose proof (contains_nonempty _ _ Hm) as Hne.
  apply (all_is_geq_bot_zitv i j Hne) in Hij as [Hl Hh]. destruct Hm as [M1 M2].
  split; [ eapply leq_zinf_trans; [exact Hl | exact M1] | eapply leq_zinf_trans; [exact M2 | exact Hh] ].
Qed.

Lemma in_zitv3_sle3 : forall s t vx vy vz,
  leq_zitv3 s t -> in_zitv3 s vx vy vz -> in_zitv3 t vx vy vz.
Proof.
  intros s t vx vy vz Hst (Hx & Hy & Hz).
  assert (Ene : is_not_bot_zitv3 s = true) by
    (unfold is_not_bot_zitv3; rewrite (contains_nonempty _ _ Hx),(contains_nonempty _ _ Hy),(contains_nonempty _ _ Hz); reflexivity).
  apply (leq_zitv3_nobot_inv s t Ene) in Hst as (Hix & Hiy & Hiz).
  split; [ apply (contains_leq_zitv3 _ _ _ Hix Hx)
         | split; [ apply (contains_leq_zitv3 _ _ _ Hiy Hy) | apply (contains_leq_zitv3 _ _ _ Hiz Hz) ] ].
Qed.

Lemma closure_laws :
  forall (P : Z -> Z -> Z -> Prop) (f : zitv3 -> zitv3),
  (forall s vx vy vz, in_zitv3 s vx vy vz -> P vx vy vz -> in_zitv3 (f s) vx vy vz) ->
  (forall s, feasible P s -> forall t, preserve_solutions P s t -> leq_zitv3 (f s) t) ->
  (forall s, is_not_bot_zitv3 (f s) = true -> feasible P s) ->
  (forall s, leq_zitv3 (f s) s)
  /\ (forall s t, leq_zitv3 s t -> leq_zitv3 (f s) (f t))
  /\ (forall s, leq_zitv3 (f (f s)) (f s) /\ leq_zitv3 (f s) (f (f s))).
Proof.
  intros P f Hsound Hbest Hnef.
  assert (Hred : forall s, leq_zitv3 (f s) s).
  { intro s. destruct (is_not_bot_zitv3 (f s)) eqn:E; [ | apply bot_is_leq_all_zitv3; exact E ].
    apply Hbest; [ apply Hnef; exact E | ]. intros vx vy vz Hin _; exact Hin. }
  split; [ exact Hred | ]. split.
  - intros s t Hst. destruct (is_not_bot_zitv3 (f s)) eqn:E; [ | apply bot_is_leq_all_zitv3; exact E ].
    apply Hbest; [ apply Hnef; exact E | ].
    intros vx vy vz Hin HP.
    apply (Hsound t); [ apply (in_zitv3_sle3 s t _ _ _ Hst Hin) | exact HP ].
  - intro s. split; [ apply Hred | ].
    destruct (is_not_bot_zitv3 (f s)) eqn:E; [ | apply bot_is_leq_all_zitv3; exact E ].
    apply Hbest; [ apply Hnef; exact E | ].
    intros vx vy vz Hin HP.
    apply (Hsound (f s)); [ apply (Hsound s _ _ _ Hin HP) | exact HP ].
Qed.

(* ---- non-emptiness / bound extraction ---- *)
Lemma nonempty_bounds3 : forall i, is_not_bot_zitv i = true -> lb i <> Pinf /\ ub i <> Ninf.
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; split; discriminate.
Qed.

Lemma max_zinf_not_Pinf : forall a b, a <> Pinf -> b <> Pinf -> max_zinf a b <> Pinf.
Proof. intros [a| |] [b| |] Ha Hb; cbn; congruence. Qed.

Lemma min_zinf_not_Ninf : forall a b, a <> Ninf -> b <> Ninf -> min_zinf a b <> Ninf.
Proof. intros [a| |] [b| |] Ha Hb; cbn; congruence. Qed.
