(** * store_lattice.v : the general store (X -> I)/~ is a COMPLETE LATTICE.

    Generalising [store3] (the fixed 3-variable store) to an arbitrary index
    type [V] of variables: a store is a total map [V -> itv3].  As in the
    paper's \mathbf{I} = (X -> \widetilde{I})/~_I, all FAILED stores (some
    variable empty) are identified with bottom; this is modelled by the order
    [sle] carrying the [~ ne_store] disjunct, so equality is up to [seq].

    We prove the store domain is a complete lattice (up to [seq]): every set
    of stores has a glb and a lub, obtained pointwise from the interval
    completeness of itv_lattice.v.  Assembling the pointwise witnesses into a
    store needs functional choice, so this file uses [ClassicalChoice]
    (= [classic] + [choice]); the interval and propagator files stay clean. *)

From Stdlib Require Import ZArith Lia ClassicalChoice.
From LalaInterval Require Import itv itv_lattice.
Open Scope Z_scope.

Section StoreLattice.
Context {V : Type}.

Definition store := V -> itv3.

(* concretization: an assignment [rho] is in [s] iff pointwise in range. *)
Definition in_store (s : store) (rho : V -> Z) : Prop := forall x, mem3 (s x) (rho x).

(* a store is non-failed iff every variable is non-empty. *)
Definition ne_store (s : store) : Prop := forall x, nonempty3b (s x) = true.

(* quotient store order: failed stores are bottom, else pointwise [ile3]. *)
Definition sle (a b : store) : Prop := ~ ne_store a \/ (forall x, ile3 (a x) (b x)).
Definition seq (a b : store) : Prop := sle a b /\ sle b a.

(* ---- intro / inversion for the quotient order ---- *)
Lemma sle_raw : forall a b, (forall x, ile3 (a x) (b x)) -> sle a b.
Proof. intros a b H; right; exact H. Qed.

Lemma sle_bot : forall a b, ~ ne_store a -> sle a b.
Proof. intros a b H; left; exact H. Qed.

Lemma sle_ne_inv : forall a b, ne_store a -> sle a b -> forall x, ile3 (a x) (b x).
Proof. intros a b Hne [Hb | Hraw]; [ contradiction | exact Hraw ]. Qed.

(* a raw containment with a non-failed smaller side forces the larger non-failed *)
Lemma ne_store_mono : forall a b, ne_store a -> (forall x, ile3 (a x) (b x)) -> ne_store b.
Proof.
  intros a b Ha Hle x.
  pose proof (Ha x) as Hax. pose proof (Hle x) as Hlex.
  apply (ile3_ne_inv (a x) (b x) Hax) in Hlex as [Hlo Hhi].
  exact (raw_ile_ne (a x) (b x) Hax Hlo Hhi).
Qed.

Lemma sle_refl : forall a, sle a a.
Proof. intro a; apply sle_raw; intro x; apply ile3_refl. Qed.

Lemma sle_trans : forall a b c, sle a b -> sle b c -> sle a c.
Proof.
  intros a b c H1 H2.
  destruct (classic (ne_store a)) as [Ha | Ha]; [ | apply sle_bot; exact Ha ].
  pose proof (sle_ne_inv a b Ha H1) as Hab.
  pose proof (ne_store_mono a b Ha Hab) as Hb.
  pose proof (sle_ne_inv b c Hb H2) as Hbc.
  apply sle_raw. intro x. eapply ile3_trans; [ apply Hab | apply Hbc ].
Qed.

Lemma seq_refl : forall a, seq a a. Proof. intro a; split; apply sle_refl. Qed.
Lemma seq_sym : forall a b, seq a b -> seq b a. Proof. intros a b [H1 H2]; split; assumption. Qed.
Lemma seq_trans : forall a b c, seq a b -> seq b c -> seq a c.
Proof. intros a b c [H1 H2] [H3 H4]; split; eapply sle_trans; eassumption. Qed.

(* ================================================================== *)
(** ** COMPLETENESS: every set of stores has a glb and a lub (up to ~)

    Lifted pointwise from the interval completeness of itv_lattice.v.
    The pointwise witnesses are assembled into a store with [choice]. *)
(* ================================================================== *)

Definition sub (S : store -> Prop) (u : store) : Prop := forall s, S s -> sle s u.
Definition slb (S : store -> Prop) (l : store) : Prop := forall s, S s -> sle l s.
Definition is_slub (S : store -> Prop) (m : store) : Prop :=
  sub S m /\ (forall u, sub S u -> sle m u).
Definition is_sglb (S : store -> Prop) (m : store) : Prop :=
  slb S m /\ (forall l, slb S l -> sle l m).

(* join = pointwise interval lub over the NON-FAILED members (failed stores
   are bottom and do not contribute); bottom if there is no non-failed one. *)
Theorem store_complete_lub : forall S, exists m, is_slub S m.
Proof.
  intro S.
  destruct (classic (exists s0, S s0 /\ ne_store s0)) as [Hne | Hallbot].
  - assert (Hpt : forall x, exists mx, is_ilub (fun i => exists s, S s /\ ne_store s /\ s x = i) mx)
      by (intro x; apply itv_complete_lub).
    apply choice in Hpt. destruct Hpt as [m Hm].
    exists m. split.
    + intros s Hs. destruct (classic (ne_store s)) as [Hnes | Hbots]; [ | apply sle_bot; exact Hbots ].
      apply sle_raw. intro x. destruct (Hm x) as [Hub _].
      apply Hub. exists s. split; [ exact Hs | split; [ exact Hnes | reflexivity ] ].
    + intros u Hu. apply sle_raw. intro x. destruct (Hm x) as [_ Hleast].
      apply Hleast. intros i [s [Hs [Hnes Hi]]]. subst i.
      apply (sle_ne_inv s u Hnes (Hu s Hs)).
  - exists (fun _ => ibot). split.
    + intros s Hs. apply sle_bot. intro Hns. apply Hallbot. exists s. split; [ exact Hs | exact Hns ].
    + intros u Hu. apply sle_raw. intro x. apply ile3_ibot.
Qed.

(* meet = pointwise interval glb over ALL members; bottom if any member is
   already failed (meet with bottom is bottom). *)
Theorem store_complete_glb : forall S, exists m, is_sglb S m.
Proof.
  intro S.
  destruct (classic (exists e, S e /\ ~ ne_store e)) as [[e [He Hee]] | Hallne].
  - exists (fun _ => ibot). split.
    + intros s Hs. apply sle_raw. intro x. apply ile3_ibot.
    + intros l Hl. apply sle_bot. intro Hnl.
      apply Hee. apply (ne_store_mono l e Hnl). apply (sle_ne_inv l e Hnl (Hl e He)).
  - assert (Hpt : forall x, exists mx, is_iglb (fun i => exists s, S s /\ s x = i) mx)
      by (intro x; apply itv_complete_glb).
    apply choice in Hpt. destruct Hpt as [m Hm].
    exists m. split.
    + intros s Hs. apply sle_raw. intro x. destruct (Hm x) as [Hlb _].
      apply Hlb. exists s. split; [ exact Hs | reflexivity ].
    + intros l Hl. destruct (classic (ne_store l)) as [Hnl | Hbl]; [ | apply sle_bot; exact Hbl ].
      apply sle_raw. intro x. destruct (Hm x) as [_ Hgreat].
      apply Hgreat. intros i [s [Hs Hi]]. subst i.
      apply (sle_ne_inv l s Hnl (Hl s Hs)).
Qed.

End StoreLattice.
