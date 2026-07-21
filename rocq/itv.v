(** * itv3: consolidated interval + division machinery

    Self-contained merge of the [itv], [fdiv2] and [fdiv3] modules (finite
    interval infrastructure, the compressed finite floored-division
    propagator, and the infinity-aware division helpers).  Nothing here
    changed except that [fdiv3]'s qualified [fdiv2.cdiv]/[fdiv2.sol]
    references are now local.  Provided so that [div4] depends on a single
    module. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import (*Lemmas*) inf.
Open Scope Z_scope.

(* ================================================================== *)
(** ** Part 1 : finite integer intervals  (was itv.v)                  *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(** ** Intervals and membership                                        *)
(* ------------------------------------------------------------------ *)

(** A (finite) interval is a pair of bounds; we work with finite bounds,
    which is what the top-level infinite-bound guard secures. *)
Record itv := Itv { lo : Z ; hi : Z }.

Definition mem (i : itv) (v : Z) : Prop := lo i <= v <= hi i.

Definition nonempty (i : itv) : Prop := lo i <= hi i.

Definition nonemptyb (i : itv) : bool := Z.leb (lo i) (hi i).

Lemma nonemptyb_true : forall i v, mem i v -> nonemptyb i = true.
Proof. intros i v Hm. unfold nonemptyb. apply Z.leb_le. unfold mem in Hm. lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** Meet (intersection) and join                                    *)
(* ------------------------------------------------------------------ *)

Definition inter (i j : itv) : itv := Itv (Z.max (lo i) (lo j)) (Z.min (hi i) (hi j)).
Lemma mem_inter : forall i j v, mem i v -> mem j v -> mem (inter i j) v.
Proof. intros i j v Hi Hj. unfold mem, inter in *; simpl in *. lia. Qed.

Definition ijoin (i j : itv) : itv :=
  Itv (Z.min (lo i) (lo j)) (Z.max (hi i) (hi j)).
Lemma in_store_ijoin_l : forall i j v, mem i v -> mem (ijoin i j) v.
Proof. intros i j v Hm. unfold mem, ijoin in *; simpl in *. lia. Qed.
Lemma in_store_ijoin_r : forall i j v, mem j v -> mem (ijoin i j) v.
Proof. intros i j v Hm. unfold mem, ijoin in *; simpl in *. lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** Stores: a box is a triple of intervals                          *)
(* ------------------------------------------------------------------ *)

Record store := St { sx : itv ; sy : itv ; sz : itv }.

Definition in_store (s : store) (vx vy vz : Z) : Prop :=
  mem (sx s) vx /\ mem (sy s) vy /\ mem (sz s) vz.

Definition ne_store (s : store) : bool :=
  (nonemptyb (sx s) && nonemptyb (sy s) && nonemptyb (sz s))%bool.

Lemma ne_store_true : forall s vx vy vz, in_store s vx vy vz -> ne_store s = true.
Proof.
  intros s vx vy vz (Hx & Hy & Hz); unfold ne_store.
  rewrite (nonemptyb_true _ _ Hx), (nonemptyb_true _ _ Hy), (nonemptyb_true _ _ Hz).
  reflexivity.
Qed.

Definition sjoin (s t : store) : store :=
  St (ijoin (sx s) (sx t)) (ijoin (sy s) (sy t)) (ijoin (sz s) (sz t)).

Definition sqcupbot (s t : store) : store :=
  if ne_store s
  then (if ne_store t then sjoin s t else s)
  else t.

Lemma sqcupbot_pres_l : forall s t vx vy vz,
  in_store s vx vy vz -> in_store (sqcupbot s t) vx vy vz.
Proof.
  intros s t vx vy vz Hs.
  unfold sqcupbot.
  rewrite (ne_store_true _ _ _ _ Hs).
  destruct (ne_store t) eqn:Et.
  - destruct Hs as (Hx & Hy & Hz).
    repeat split; simpl; apply in_store_ijoin_l; assumption.
  - exact Hs.
Qed.

Lemma sqcupbot_pres_r : forall s t vx vy vz,
  in_store t vx vy vz -> in_store (sqcupbot s t) vx vy vz.
Proof.
  intros s t vx vy vz Ht.
  unfold sqcupbot.
  rewrite (ne_store_true _ _ _ _ Ht).
  destruct (ne_store s) eqn:Es; simpl.
  - destruct Ht as (Hx & Hy & Hz).
    repeat split; simpl; apply in_store_ijoin_r; assumption.
  - exact Ht.
Qed.




(* ================================================================= *)
(** ** Order on intervals/stores                                  *)
(* ================================================================= *)

(* ---- order on intervals / stores ---- *)
Definition ile (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.   (* i included in j *)
Definition sle (a b : store) : Prop :=
  ile (sx a) (sx b) /\ ile (sy a) (sy b) /\ ile (sz a) (sz b).


Lemma ile_antisym : forall i j, ile i j -> ile j i -> i = j.
Proof. intros [il ih] [jl jh]; unfold ile; cbn [lo hi]; intros [??] [??]; f_equal; lia. Qed.
Lemma sle_antisym : forall a b, sle a b -> sle b a -> a = b.
Proof.
  intros [ax ay az] [bx byy bz]; unfold sle; cbn [sx sy sz];
  intros [H1 [H2 H3]] [H4 [H5 H6]]; f_equal; apply ile_antisym; assumption.
Qed.

Lemma ile_refl : forall i, ile i i.
Proof. intro i; unfold ile; lia. Qed.
Lemma ile_trans : forall i j k, ile i j -> ile j k -> ile i k.
Proof. unfold ile; intros i j k [??] [??]; lia. Qed.
Lemma inter_ile_l : forall i j, ile (inter i j) i.
Proof. intros i j; unfold ile, inter; cbn [lo hi]; lia. Qed.
Lemma ijoin_ile : forall i j k, ile i k -> ile j k -> ile (ijoin i j) k.
Proof. unfold ile, ijoin; cbn [lo hi]; intros i j k [??] [??]; lia. Qed.
Lemma sle_trans : forall a b c, sle a b -> sle b c -> sle a c.
Proof.
  unfold sle; intros a b c [Hx [Hy Hz]] [Hx' [Hy' Hz']];
  split; [|split]; eapply ile_trans; eassumption.
Qed.




Lemma mem_inter_l : forall i j v, mem (inter i j) v -> mem i v.
Proof.
  intros i j v; unfold mem, inter; cbn [lo hi]; intro H.
  pose proof (Z.le_max_l (lo i) (lo j)). pose proof (Z.le_min_l (hi i) (hi j)). lia.
Qed.

Lemma ne_store_bounds : forall p, ne_store p = true ->
  lo (sx p) <= hi (sx p) /\ lo (sy p) <= hi (sy p) /\ lo (sz p) <= hi (sz p).
Proof.
  intros p H. unfold ne_store, nonemptyb in H.
  destruct (lo (sx p) <=? hi (sx p)) eqn:Ax; cbn in H; try discriminate.
  destruct (lo (sy p) <=? hi (sy p)) eqn:Ay; cbn in H; try discriminate.
  destruct (lo (sz p) <=? hi (sz p)) eqn:Az; cbn in H; try discriminate.
  apply Z.leb_le in Ax. apply Z.leb_le in Ay. apply Z.leb_le in Az. auto.
Qed.

Lemma bounds_ne_store : forall p,
  lo (sx p) <= hi (sx p) -> lo (sy p) <= hi (sy p) -> lo (sz p) <= hi (sz p) ->
  ne_store p = true.
Proof.
  intros p Hx Hy Hz. unfold ne_store, nonemptyb.
  destruct (lo (sx p) <=? hi (sx p)) eqn:Ax; [|apply Z.leb_gt in Ax; lia].
  destruct (lo (sy p) <=? hi (sy p)) eqn:Ay; [|apply Z.leb_gt in Ay; lia].
  destruct (lo (sz p) <=? hi (sz p)) eqn:Az; [|apply Z.leb_gt in Az; lia].
  reflexivity.
Qed.





Lemma mem_of_ile : forall i j v, ile i j -> mem i v -> mem j v.
Proof. unfold ile, mem; intros i j v [??] [??]; lia. Qed.

Lemma in_store_sle : forall s t vx vy vz,
  sle s t -> in_store s vx vy vz -> in_store t vx vy vz.
Proof.
  unfold sle, in_store; intros s t vx vy vz (Hx & Hy & Hz) (Mx & My & Mz).
  split; [| split]; eapply mem_of_ile; eassumption.
Qed.




(* ================================================================== *)
(** ** Part 3 : infinity-aware division helpers  (was fdiv3.v)         *)
(* ================================================================== *)


(* ------------------------------------------------------------------ *)
(** ** Intervals and stores over Zinf; membership of INTEGERS          *)
(* ------------------------------------------------------------------ *)

Record itv3 := Itv3 { lo3 : Zinf ; hi3 : Zinf }.

Definition mem3 (i : itv3) (v : Z) : Prop :=
  zle (lo3 i) (Fin v) /\ zle (Fin v) (hi3 i).

(* non-emptiness: mirrors the C++ is_bot (l > u \/ l = +oo \/ u = -oo) *)
Definition nonempty3b (i : itv3) : bool :=
  match lo3 i, hi3 i with
  | Pinf, _ => false
  | _, Ninf => false
  | Ninf, _ => true
  | _, Pinf => true
  | Fin a, Fin b => a <=? b
  end.

Record store3 := St3 { sx3 : itv3 ; sy3 : itv3 ; sz3 : itv3 }.

Definition in_store3 (s : store3) (vx vy vz : Z) : Prop :=
  mem3 (sx3 s) vx /\ mem3 (sy3 s) vy /\ mem3 (sz3 s) vz.

Definition ne_store3 (s : store3) : bool :=
  (nonempty3b (sx3 s) && nonempty3b (sy3 s) && nonempty3b (sz3 s))%bool.

Definition inter3 (i j : itv3) : itv3 :=
  Itv3 (zmax (lo3 i) (lo3 j)) (zmin (hi3 i) (hi3 j)).

Definition ijoin3 (i j : itv3) : itv3 :=
  Itv3 (zmin (lo3 i) (lo3 j)) (zmax (hi3 i) (hi3 j)).

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
Definition ile3 (i j : itv3) : Prop :=
  nonempty3b i = false \/ (zle (lo3 j) (lo3 i) /\ zle (hi3 i) (hi3 j)).
Definition sle3 (a b : store3) : Prop :=
  ne_store3 a = false \/
  (ile3 (sx3 a) (sx3 b) /\ ile3 (sy3 a) (sy3 b) /\ ile3 (sz3 a) (sz3 b)).



(* ---- intro / inversion helpers for the quotient order ---- *)
Lemma ile3_intro : forall i j, zle (lo3 j) (lo3 i) -> zle (hi3 i) (hi3 j) -> ile3 i j.
Proof. intros i j Hl Hh; right; split; assumption. Qed.

Lemma ile3_bot : forall i j, nonempty3b i = false -> ile3 i j.
Proof. intros i j H; left; exact H. Qed.

Lemma ile3_ne_inv : forall i j, nonempty3b i = true -> ile3 i j ->
  zle (lo3 j) (lo3 i) /\ zle (hi3 i) (hi3 j).
Proof. intros i j Hne [Hb | Hraw]; [ rewrite Hne in Hb; discriminate | exact Hraw ]. Qed.

(* a raw containment with a non-empty smaller side forces the larger non-empty *)
Lemma raw_ile_ne : forall i j, nonempty3b i = true ->
  zle (lo3 j) (lo3 i) -> zle (hi3 i) (hi3 j) -> nonempty3b j = true.
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
Proof. intro i; apply ile3_intro; apply zle_refl. Qed.

Lemma ile3_trans : forall i j k, ile3 i j -> ile3 j k -> ile3 i k.
Proof.
  intros i j k H1 H2.
  destruct (nonempty3b i) eqn:Ei; [ | apply ile3_bot; exact Ei ].
  apply (ile3_ne_inv i j Ei) in H1 as [Hl1 Hh1].
  assert (Enj : nonempty3b j = true) by (apply (raw_ile_ne i j Ei Hl1 Hh1)).
  apply (ile3_ne_inv j k Enj) in H2 as [Hl2 Hh2].
  apply ile3_intro; eapply zle_trans; eassumption.
Qed.

Lemma inter3_ile3_l : forall i j, ile3 (inter3 i j) i.
Proof.
  intros i j; apply ile3_intro; unfold inter3; cbn [lo3 hi3];
  [ apply zle_zmax_l | apply zmin_zle_l ].
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
  apply ile3_intro; unfold ijoin3; cbn [lo3 hi3].
  - apply zle_zmin_glb; assumption.
  - apply zmax_lub; assumption.
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
  split; [ eapply zle_trans; [exact Hl | exact M1] | eapply zle_trans; [exact M2 | exact Hh] ].
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
