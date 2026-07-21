(** * itv: consolidated interval + division machinery

    Self-contained merge of the [itv], [fdiv2] and [fdiv3] modules (finite
    interval infrastructure, the compressed finite floored-division
    propagator, and the infinity-aware division helpers).  Nothing here
    changed except that [fdiv3]'s qualified [fdiv2.cdiv]/[fdiv2.sol]
    references are now local.  Provided so that [div4] depends on a single
    module. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import Zinf.
Open Scope Z_scope.

(* ================================================================== *)
(** Interval over extended integers (Zinf) *)
(* ================================================================== *)

Record itv := Itv { lb : Zinf ; ub : Zinf }.

Definition mem3 (i : itv) (v : Z) : Prop :=
  leq_zinf (lb i) (Fin v) /\ leq_zinf (Fin v) (ub i).

(* non-emptiness: mirrors the C++ is_bot (l > u \/ l = +oo \/ u = -oo) *)
Definition nonempty3b (i : itv) : bool :=
  match lb i, ub i with
  | Pinf, _ => false
  | _, Ninf => false
  | Ninf, _ => true
  | _, Pinf => true
  | Fin a, Fin b => a <=? b
  end.

Record store3 := St3 { sx3 : itv ; sy3 : itv ; sz3 : itv }.

Definition in_store3 (s : store3) (vx vy vz : Z) : Prop :=
  mem3 (sx3 s) vx /\ mem3 (sy3 s) vy /\ mem3 (sz3 s) vz.

Definition ne_store3 (s : store3) : bool :=
  (nonempty3b (sx3 s) && nonempty3b (sy3 s) && nonempty3b (sz3 s))%bool.

Definition inter3 (i j : itv) : itv :=
  Itv (max_zinf (lb i) (lb j)) (min_zinf (ub i) (ub j)).

Definition ijoin3 (i j : itv) : itv :=
  Itv (min_zinf (lb i) (lb j)) (max_zinf (ub i) (ub j)).

Definition sjoin3 (s t : store3) : store3 :=
  St3 (ijoin3 (sx3 s) (sx3 t)) (ijoin3 (sy3 s) (sy3 t)) (ijoin3 (sz3 s) (sz3 t)).

Definition sqcupbot3 (s t : store3) : store3 :=
  if ne_store3 s
  then (if ne_store3 t then sjoin3 s t else s)
  else t.

(* interval order (containment) and store order — QUOTIENTED: every empty
   interval / failed store is identified with bottom and sits below all,
   matching the lattice \widetilde{I} and \mathbf{I} of the paper (the
   [isbot(a,b) \/ ...] / [isboti(d) \/ ...] disjunctions). *)
Definition ile3 (i j : itv) : Prop :=
  nonempty3b i = false \/ (leq_zinf (lb j) (lb i) /\ leq_zinf (ub i) (ub j)).
Definition sle3 (a b : store3) : Prop :=
  ne_store3 a = false \/
  (ile3 (sx3 a) (sx3 b) /\ ile3 (sy3 a) (sy3 b) /\ ile3 (sz3 a) (sz3 b)).



(* ---- intro / inversion helpers for the quotient order ---- *)
Lemma ile3_intro : forall i j, leq_zinf (lb j) (lb i) -> leq_zinf (ub i) (ub j) -> ile3 i j.
Proof. intros i j Hl Hh; right; split; assumption. Qed.

Lemma ile3_bot : forall i j, nonempty3b i = false -> ile3 i j.
Proof. intros i j H; left; exact H. Qed.

Lemma ile3_ne_inv : forall i j, nonempty3b i = true -> ile3 i j ->
  leq_zinf (lb j) (lb i) /\ leq_zinf (ub i) (ub j).
Proof. intros i j Hne [Hb | Hraw]; [ rewrite Hne in Hb; discriminate | exact Hraw ]. Qed.

(* a raw containment with a non-empty smaller side forces the larger non-empty *)
Lemma raw_ile_ne : forall i j, nonempty3b i = true ->
  leq_zinf (lb j) (lb i) -> leq_zinf (ub i) (ub j) -> nonempty3b j = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]]; cbn; intros Hne Hl Hh;
    try reflexivity; try discriminate; try (exfalso; exact Hl); try (exfalso; exact Hh);
    apply Z.leb_le in Hne; apply Z.leb_le; lia.
Qed.

Lemma sle3_intro : forall a b,
  ile3 (sx3 a) (sx3 b) -> ile3 (sy3 a) (sy3 b) -> ile3 (sz3 a) (sz3 b) -> sle3 a b.
Proof. intros a b Hx Hy Hz; right; split; [exact Hx | split; [exact Hy | exact Hz]]. Qed.

Lemma sle3_bot : forall a b, ne_store3 a = false -> sle3 a b.
Proof. intros a b H; left; exact H. Qed.

Lemma sle3_ne_inv : forall a b, ne_store3 a = true -> sle3 a b ->
  ile3 (sx3 a) (sx3 b) /\ ile3 (sy3 a) (sy3 b) /\ ile3 (sz3 a) (sz3 b).
Proof. intros a b Hne [Hb | Hraw]; [ rewrite Hne in Hb; discriminate | exact Hraw ]. Qed.

Lemma ne_store3_parts : forall s, ne_store3 s = true ->
  nonempty3b (sx3 s) = true /\ nonempty3b (sy3 s) = true /\ nonempty3b (sz3 s) = true.
Proof.
  intros s H. unfold ne_store3 in H.
  apply andb_true_iff in H as [H Hz]. apply andb_true_iff in H as [Hx Hy].
  split; [exact Hx | split; [exact Hy | exact Hz]].
Qed.

Lemma ile3_refl : forall i, ile3 i i.
Proof. intro i; apply ile3_intro; apply leq_zinf_refl. Qed.

Lemma ile3_trans : forall i j k, ile3 i j -> ile3 j k -> ile3 i k.
Proof.
  intros i j k H1 H2.
  destruct (nonempty3b i) eqn:Ei; [ | apply ile3_bot; exact Ei ].
  apply (ile3_ne_inv i j Ei) in H1 as [Hl1 Hh1].
  assert (Enj : nonempty3b j = true) by (apply (raw_ile_ne i j Ei Hl1 Hh1)).
  apply (ile3_ne_inv j k Enj) in H2 as [Hl2 Hh2].
  apply ile3_intro; eapply leq_zinf_trans; eassumption.
Qed.

Lemma inter3_ile3_l : forall i j, ile3 (inter3 i j) i.
Proof.
  intros i j; apply ile3_intro; unfold inter3; cbn [lb ub];
  [ apply leq_zinf_max_zinf_l | apply min_zinf_leq_zinf_l ].
Qed.

(* the NAIVE join is a LUB only when both inputs are non-empty (the quotient
   order collapses empties, so [ijoin3] may overshoot on an empty input) *)
Lemma ijoin3_ile3 : forall i j k,
  nonempty3b i = true -> nonempty3b j = true ->
  ile3 i k -> ile3 j k -> ile3 (ijoin3 i j) k.
Proof.
  intros i j k Ei Ej H1 H2.
  apply (ile3_ne_inv i k Ei) in H1 as [Hli Hhi].
  apply (ile3_ne_inv j k Ej) in H2 as [Hlj Hhj].
  apply ile3_intro; unfold ijoin3; cbn [lb ub].
  - apply leq_zinf_min_zinf_glb; assumption.
  - apply max_zinf_lub; assumption.
Qed.

Lemma sle3_trans : forall a b c, sle3 a b -> sle3 b c -> sle3 a c.
Proof.
  intros a b c H1 H2.
  destruct (ne_store3 a) eqn:Ea; [ | apply sle3_bot; exact Ea ].
  apply (sle3_ne_inv a b Ea) in H1 as (Hx1 & Hy1 & Hz1).
  apply ne_store3_parts in Ea as (Eax & Eay & Eaz).
  assert (Ebx : nonempty3b (sx3 b) = true).
  { apply (ile3_ne_inv _ _ Eax) in Hx1 as [Hl Hh]. apply (raw_ile_ne _ _ Eax Hl Hh). }
  assert (Eby : nonempty3b (sy3 b) = true).
  { apply (ile3_ne_inv _ _ Eay) in Hy1 as [Hl Hh]. apply (raw_ile_ne _ _ Eay Hl Hh). }
  assert (Ebz : nonempty3b (sz3 b) = true).
  { apply (ile3_ne_inv _ _ Eaz) in Hz1 as [Hl Hh]. apply (raw_ile_ne _ _ Eaz Hl Hh). }
  assert (Eb : ne_store3 b = true)
    by (unfold ne_store3; rewrite Ebx, Eby, Ebz; reflexivity).
  apply (sle3_ne_inv b c Eb) in H2 as (Hx2 & Hy2 & Hz2).
  apply sle3_intro; eapply ile3_trans; eassumption.
Qed.


Lemma sqcupbot3_ile : forall a b t, sle3 a t -> sle3 b t -> sle3 (sqcupbot3 a b) t.
Proof.
  intros a b t Ha Hb. unfold sqcupbot3.
  destruct (ne_store3 a) eqn:Ea; destruct (ne_store3 b) eqn:Eb; cbn iota; try assumption.
  apply ne_store3_parts in Ea as (Eax & Eay & Eaz).
  apply ne_store3_parts in Eb as (Ebx & Eby & Ebz).
  apply (sle3_ne_inv a t) in Ha; [ | unfold ne_store3; rewrite Eax,Eay,Eaz; reflexivity ].
  apply (sle3_ne_inv b t) in Hb; [ | unfold ne_store3; rewrite Ebx,Eby,Ebz; reflexivity ].
  destruct Ha as (Hax & Hay & Haz). destruct Hb as (Hbx & Hby & Hbz).
  apply sle3_intro; unfold sjoin3; cbn [sx3 sy3 sz3]; apply ijoin3_ile3; assumption.
Qed.


Lemma ne_inter3 : forall i j, nonempty3b (inter3 i j) = true -> nonempty3b i = true.
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

Definition contains3 (P : Z -> Z -> Z -> Prop) (s t : store3) : Prop :=
  forall vx vy vz, in_store3 s vx vy vz -> P vx vy vz -> in_store3 t vx vy vz.
Definition feasible3 (P : Z -> Z -> Z -> Prop) (s : store3) : Prop :=
  exists vx vy vz, in_store3 s vx vy vz /\ P vx vy vz.

Lemma mem3_nonempty : forall i v, mem3 i v -> nonempty3b i = true.
Proof. intros [[a| |] [b| |]] v [H1 H2]; cbn in *; try easy; apply Z.leb_le; lia. Qed.

Lemma mem3_ile3 : forall i j v, ile3 i j -> mem3 i v -> mem3 j v.
Proof.
  intros i j v Hij Hm. pose proof (mem3_nonempty _ _ Hm) as Hne.
  apply (ile3_ne_inv i j Hne) in Hij as [Hl Hh]. destruct Hm as [M1 M2].
  split; [ eapply leq_zinf_trans; [exact Hl | exact M1] | eapply leq_zinf_trans; [exact M2 | exact Hh] ].
Qed.

Lemma in_store3_sle3 : forall s t vx vy vz,
  sle3 s t -> in_store3 s vx vy vz -> in_store3 t vx vy vz.
Proof.
  intros s t vx vy vz Hst (Hx & Hy & Hz).
  assert (Ene : ne_store3 s = true) by
    (unfold ne_store3; rewrite (mem3_nonempty _ _ Hx),(mem3_nonempty _ _ Hy),(mem3_nonempty _ _ Hz); reflexivity).
  apply (sle3_ne_inv s t Ene) in Hst as (Hix & Hiy & Hiz).
  split; [ apply (mem3_ile3 _ _ _ Hix Hx)
         | split; [ apply (mem3_ile3 _ _ _ Hiy Hy) | apply (mem3_ile3 _ _ _ Hiz Hz) ] ].
Qed.

Lemma closure_laws :
  forall (P : Z -> Z -> Z -> Prop) (f : store3 -> store3),
  (forall s vx vy vz, in_store3 s vx vy vz -> P vx vy vz -> in_store3 (f s) vx vy vz) ->
  (forall s, feasible3 P s -> forall t, contains3 P s t -> sle3 (f s) t) ->
  (forall s, ne_store3 (f s) = true -> feasible3 P s) ->
  (forall s, sle3 (f s) s)
  /\ (forall s t, sle3 s t -> sle3 (f s) (f t))
  /\ (forall s, sle3 (f (f s)) (f s) /\ sle3 (f s) (f (f s))).
Proof.
  intros P f Hsound Hbest Hnef.
  assert (Hred : forall s, sle3 (f s) s).
  { intro s. destruct (ne_store3 (f s)) eqn:E; [ | apply sle3_bot; exact E ].
    apply Hbest; [ apply Hnef; exact E | ]. intros vx vy vz Hin _; exact Hin. }
  split; [ exact Hred | ]. split.
  - intros s t Hst. destruct (ne_store3 (f s)) eqn:E; [ | apply sle3_bot; exact E ].
    apply Hbest; [ apply Hnef; exact E | ].
    intros vx vy vz Hin HP.
    apply (Hsound t); [ apply (in_store3_sle3 s t _ _ _ Hst Hin) | exact HP ].
  - intro s. split; [ apply Hred | ].
    destruct (ne_store3 (f s)) eqn:E; [ | apply sle3_bot; exact E ].
    apply Hbest; [ apply Hnef; exact E | ].
    intros vx vy vz Hin HP.
    apply (Hsound (f s)); [ apply (Hsound s _ _ _ Hin HP) | exact HP ].
Qed.
