(** * itv_lattice.v : the interval domain of itv.v is a COMPLETE LATTICE.

    The order [ile3] is only a partial order UP TO the bottom equivalence
    [ieq] (all empty intervals are identified), so this is the quotient
    lattice \widetilde{I} of the paper.  We prove:
      - [ieq] is an equivalence and [ile3] a partial order modulo [ieq];
      - the algebraic correspondence of the binary meet/join with the order
        ([inter3] is the glb, [iqcup] the lub, absorption, etc.);
      - COMPLETENESS: every set of intervals has a glb and a lub (up to ~).

    Completeness rests on [Zinf] being a genuine complete lattice (its [zle]
    IS antisymmetric).  Constructing arbitrary suprema over Z needs a
    bounded-maximum argument, which is classical; hence this file (and only
    this file) uses [Classical].  itv.v and the propagator files stay
    axiom-free. *)

From Stdlib Require Import ZArith Lia Classical.
From LalaInterval Require Import inf itv.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** The bottom equivalence and the order modulo it                  *)
(* ------------------------------------------------------------------ *)

Definition ieq (i j : itv3) : Prop := ile3 i j /\ ile3 j i.

Lemma ieq_refl : forall i, ieq i i.
Proof. intro i; split; apply ile3_refl. Qed.

Lemma ieq_sym : forall i j, ieq i j -> ieq j i.
Proof. intros i j [H1 H2]; split; assumption. Qed.

Lemma ieq_trans : forall i j k, ieq i j -> ieq j k -> ieq i k.
Proof. intros i j k [H1 H2] [H3 H4]; split; eapply ile3_trans; eassumption. Qed.

(* antisymmetry of [ile3] holds exactly up to [ieq] (that IS [ieq]). *)
Lemma ile3_antisym_mod : forall i j, ile3 i j -> ile3 j i -> ieq i j.
Proof. intros i j H1 H2; split; assumption. Qed.

(* [Zinf]'s own order is a genuine (antisymmetric) partial order. *)
Lemma zinf_antisym : forall a b, zle a b -> zle b a -> a = b.
Proof. intros [x| |] [y| |] H1 H2; cbn in *; try contradiction; try reflexivity; f_equal; lia. Qed.

(* ================================================================== *)
(** ** Zinf is a COMPLETE lattice

    Every subset of [Zinf] has a supremum and an infimum.  This is the
    scalar core of interval completeness.  The supremum of an arbitrary
    integer set requires a bounded-maximum argument, which is classical. *)
(* ================================================================== *)

(* bounded maximum of a Z-predicate (classical: LEM at each candidate). *)
Lemma zmax_bounded_aux : forall (n:nat) (P:Z->Prop) (hi z0:Z),
  (forall z, P z -> z <= hi) -> P z0 -> hi - Z.of_nat n <= z0 ->
  exists m, P m /\ (forall z, P z -> z <= m).
Proof.
  induction n as [|k IH]; intros P hi z0 Hub Hz0 Hlo.
  - exists z0. split; [exact Hz0|]. intros z Hz. pose proof (Hub z Hz). pose proof (Hub z0 Hz0). simpl in Hlo. lia.
  - destruct (classic (exists z, P z /\ z0 < z)) as [[z1 [Hz1 Hlt]]|Hno].
    + apply (IH P hi z1 Hub Hz1). rewrite Nat2Z.inj_succ in Hlo. lia.
    + exists z0. split; [exact Hz0|]. intros z Hz.
      destruct (Z.le_gt_cases z z0) as [Hle|Hgt]; [exact Hle|].
      exfalso. apply Hno. exists z. split; [exact Hz|exact Hgt].
Qed.

Lemma zmax_bounded : forall (P:Z->Prop) (hi:Z),
  (exists z, P z) -> (forall z, P z -> z <= hi) ->
  exists m, P m /\ (forall z, P z -> z <= m).
Proof.
  intros P hi [z0 Hz0] Hub.
  apply (zmax_bounded_aux (Z.to_nat (hi - z0)) P hi z0 Hub Hz0).
  pose proof (Hub z0 Hz0). rewrite Z2Nat.id by lia. lia.
Qed.

Definition zub (S : Zinf -> Prop) (u : Zinf) : Prop := forall a, S a -> zle a u.
Definition zis_lub (S : Zinf -> Prop) (m : Zinf) : Prop :=
  zub S m /\ (forall u, zub S u -> zle m u).

Lemma zlub_exists : forall S, exists m, zis_lub S m.
Proof.
  intro S.
  destruct (classic (S Pinf)) as [HP|HnP].
  - exists Pinf. split.
    + intros a Ha. destruct a; cbn; exact I.
    + intros u Hu. exact (Hu Pinf HP).
  - destruct (classic (exists N:Z, forall a, S a -> zle a (Fin N))) as [[N HN]|Hunb].
    + destruct (classic (exists z:Z, S (Fin z))) as [Hfin|Hnofin].
      * assert (Hub : forall z, S (Fin z) -> z <= N).
        { intros z Hz. specialize (HN (Fin z) Hz). cbn in HN. exact HN. }
        destruct (zmax_bounded (fun z => S (Fin z)) N Hfin Hub) as [m0 [Hm0 Hmax]].
        exists (Fin m0). split.
        -- intros a Ha. destruct a as [z| |].
           ++ cbn. apply Hmax. exact Ha.
           ++ exfalso. apply HnP. exact Ha.
           ++ cbn. exact I.
        -- intros u Hu. exact (Hu (Fin m0) Hm0).
      * exists Ninf. split.
        -- intros a Ha. destruct a as [z| |].
           ++ exfalso. apply Hnofin. exists z. exact Ha.
           ++ exfalso. apply HnP. exact Ha.
           ++ cbn. exact I.
        -- intros u Hu. destruct u; cbn; exact I.
    + exists Pinf. split.
      * intros a Ha. destruct a; cbn; exact I.
      * intros u Hu. destruct u as [N| |].
        -- exfalso. apply Hunb. exists N. exact Hu.
        -- cbn. exact I.
        -- exfalso. apply Hunb. exists 0. intros a Ha. specialize (Hu a Ha).
           destruct a as [z| |]; cbn in Hu |- *; [ contradiction | contradiction | exact I ].
Qed.

(* infimum by the order-reversing bijection [ineg3]. *)
Definition ineg3 (a : Zinf) : Zinf :=
  match a with Fin v => Fin (- v) | Pinf => Ninf | Ninf => Pinf end.

Lemma ineg3_invol : forall a, ineg3 (ineg3 a) = a.
Proof. intros [v| |]; cbn; try reflexivity. f_equal; lia. Qed.

Lemma ineg3_le : forall a b, zle (ineg3 a) (ineg3 b) <-> zle b a.
Proof. intros [x| |] [y| |]; cbn; try tauto; lia. Qed.

Definition zlb (S : Zinf -> Prop) (l : Zinf) : Prop := forall a, S a -> zle l a.
Definition zis_glb (S : Zinf -> Prop) (m : Zinf) : Prop :=
  zlb S m /\ (forall l, zlb S l -> zle l m).

Lemma zglb_exists : forall S, exists m, zis_glb S m.
Proof.
  intro S. destruct (zlub_exists (fun a => S (ineg3 a))) as [M [Hub Hle]].
  exists (ineg3 M). split.
  - intros b Hb.
    assert (HS' : S (ineg3 (ineg3 b))) by (rewrite ineg3_invol; exact Hb).
    pose proof (Hub (ineg3 b) HS') as H.
    apply (proj2 (ineg3_le M (ineg3 b))) in H.
    rewrite ineg3_invol in H. exact H.
  - intros l Hl.
    assert (Hubl : zub (fun a => S (ineg3 a)) (ineg3 l)).
    { intros a Ha. pose proof (Hl (ineg3 a) Ha) as H.
      apply (proj2 (ineg3_le (ineg3 a) l)) in H. rewrite ineg3_invol in H. exact H. }
    pose proof (Hle (ineg3 l) Hubl) as H.
    apply (proj2 (ineg3_le (ineg3 l) M)) in H.
    rewrite ineg3_invol in H. exact H.
Qed.

(* ================================================================== *)
(** ** Binary meet / join and the algebraic correspondence (up to ~)   *)
(* ================================================================== *)

Lemma zle_zmax_r : forall a b, zle b (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.
Lemma zmin_zle_r : forall a b, zle (zmin a b) b.
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.

(* meet = [inter3] is the greatest lower bound *)
Lemma inter3_ile3_r : forall i j, ile3 (inter3 i j) j.
Proof.
  intros i j; apply ile3_intro; unfold inter3; cbn [lo3 hi3];
  [ apply zle_zmax_r | apply zmin_zle_r ].
Qed.

Lemma inter3_glb : forall i j c, ile3 c i -> ile3 c j -> ile3 c (inter3 i j).
Proof.
  intros i j c Hci Hcj. destruct (nonempty3b c) eqn:Ec; [ | apply ile3_bot; exact Ec ].
  apply (ile3_ne_inv c i Ec) in Hci as [Hli Hhi].
  apply (ile3_ne_inv c j Ec) in Hcj as [Hlj Hhj].
  apply ile3_intro; unfold inter3; cbn [lo3 hi3].
  - apply zmax_lub; assumption.
  - apply zle_zmin_glb; assumption.
Qed.

(* join = the bottom-aware hull [iqcup] is the least upper bound.  (The raw
   [ijoin3] of itv.v is a lub only when both inputs are non-empty.) *)
Definition iqcup (i j : itv3) : itv3 :=
  if nonempty3b i then (if nonempty3b j then ijoin3 i j else i) else j.

Lemma ile3_iqcup_l : forall i j, ile3 i (iqcup i j).
Proof.
  intros i j. unfold iqcup. destruct (nonempty3b i) eqn:Ei.
  - destruct (nonempty3b j) eqn:Ej.
    + apply ile3_intro; unfold ijoin3; cbn [lo3 hi3]; [ apply zmin_zle_l | apply zle_zmax_l ].
    + apply ile3_refl.
  - apply ile3_bot; exact Ei.
Qed.

Lemma ile3_iqcup_r : forall i j, ile3 j (iqcup i j).
Proof.
  intros i j. unfold iqcup. destruct (nonempty3b i) eqn:Ei.
  - destruct (nonempty3b j) eqn:Ej.
    + apply ile3_intro; unfold ijoin3; cbn [lo3 hi3]; [ apply zmin_zle_r | apply zle_zmax_r ].
    + apply ile3_bot; exact Ej.
  - apply ile3_refl.
Qed.

Lemma iqcup_lub : forall i j k, ile3 i k -> ile3 j k -> ile3 (iqcup i j) k.
Proof.
  intros i j k Hik Hjk. unfold iqcup. destruct (nonempty3b i) eqn:Ei.
  - destruct (nonempty3b j) eqn:Ej.
    + apply ijoin3_ile3; assumption.
    + exact Hik.
  - exact Hjk.
Qed.

(* the defining absorption laws: order = meet-fixed = join-fixed (up to ~) *)
Lemma ile3_meet : forall i j, ile3 i j <-> ieq (inter3 i j) i.
Proof.
  intros i j; split.
  - intro H. split; [ apply inter3_ile3_l | apply inter3_glb; [ apply ile3_refl | exact H ] ].
  - intros [_ H]. eapply ile3_trans; [ exact H | apply inter3_ile3_r ].
Qed.

Lemma ile3_join : forall i j, ile3 i j <-> ieq (iqcup i j) j.
Proof.
  intros i j; split.
  - intro H. split; [ apply iqcup_lub; [ exact H | apply ile3_refl ] | apply ile3_iqcup_r ].
  - intros [H _]. eapply ile3_trans; [ apply ile3_iqcup_l | exact H ].
Qed.

(* bounded: greatest element [itop] and least element [ibot]. *)
Definition itop : itv3 := Itv3 Ninf Pinf.
Definition ibot : itv3 := Itv3 Pinf Ninf.
Lemma zle_ninf_l : forall a, zle Ninf a. Proof. intros [x| |]; cbn; exact I. Qed.
Lemma zle_pinf_r : forall a, zle a Pinf. Proof. intros [x| |]; cbn; exact I. Qed.
Lemma ile3_itop : forall i, ile3 i itop.
Proof. intro i. apply ile3_intro; [ apply zle_ninf_l | apply zle_pinf_r ]. Qed.
Lemma ile3_ibot : forall i, ile3 ibot i.
Proof. intro i. apply ile3_bot. reflexivity. Qed.

Lemma ile3_bot_absorb : forall l e, ile3 l e -> nonempty3b e = false -> nonempty3b l = false.
Proof.
  intros l e H He. destruct (nonempty3b l) eqn:El; [ | reflexivity ].
  apply (ile3_ne_inv l e El) in H as [Hlo Hhi].
  pose proof (raw_ile_ne l e El Hlo Hhi) as Hne. rewrite Hne in He. discriminate.
Qed.

(* ================================================================== *)
(** ** COMPLETENESS: every set of intervals has a glb and a lub (up to ~)

    The interval domain [itv3] (modulo [ieq]) is a complete lattice:
    arbitrary meets (intersections) and joins (bottom-aware hulls) exist,
    inherited componentwise from the completeness of [Zinf]. *)
(* ================================================================== *)

Definition ile3_lb (S : itv3 -> Prop) (m : itv3) : Prop := forall i, S i -> ile3 m i.
Definition ile3_ub (S : itv3 -> Prop) (m : itv3) : Prop := forall i, S i -> ile3 i m.
Definition is_iglb (S : itv3 -> Prop) (m : itv3) : Prop :=
  ile3_lb S m /\ (forall l, ile3_lb S l -> ile3 l m).
Definition is_ilub (S : itv3 -> Prop) (m : itv3) : Prop :=
  ile3_ub S m /\ (forall u, ile3_ub S u -> ile3 m u).

Theorem itv_complete_glb : forall S, exists m, is_iglb S m.
Proof.
  intro S.
  destruct (classic (exists e, S e /\ nonempty3b e = false)) as [[e [He Hee]] | Hallne].
  - exists ibot. split.
    + intros i Hi. apply ile3_ibot.
    + intros l Hl. apply ile3_bot. exact (ile3_bot_absorb l e (Hl e He) Hee).
  - destruct (zlub_exists (fun a => exists i, S i /\ lo3 i = a)) as [ml [Hml_ub Hml_l]].
    destruct (zglb_exists (fun a => exists i, S i /\ hi3 i = a)) as [mh [Hmh_lb Hmh_g]].
    exists (Itv3 ml mh). split.
    + intros i Hi. apply ile3_intro; cbn [lo3 hi3].
      * apply Hml_ub. exists i. split; [ exact Hi | reflexivity ].
      * apply Hmh_lb. exists i. split; [ exact Hi | reflexivity ].
    + intros l Hl. destruct (nonempty3b l) eqn:El; [ | apply ile3_bot; exact El ].
      apply ile3_intro; cbn [lo3 hi3].
      * apply Hml_l. intros a [i [Hi Ha]]. subst a.
        exact (proj1 (ile3_ne_inv l i El (Hl i Hi))).
      * apply Hmh_g. intros a [i [Hi Ha]]. subst a.
        exact (proj2 (ile3_ne_inv l i El (Hl i Hi))).
Qed.

Theorem itv_complete_lub : forall S, exists m, is_ilub S m.
Proof.
  intro S.
  destruct (classic (exists i, S i /\ nonempty3b i = true)) as [Hne | Hallbot].
  - destruct (zglb_exists (fun a => exists i, S i /\ nonempty3b i = true /\ lo3 i = a)) as [ml [Hml_lb Hml_g]].
    destruct (zlub_exists (fun a => exists i, S i /\ nonempty3b i = true /\ hi3 i = a)) as [mh [Hmh_ub Hmh_l]].
    exists (Itv3 ml mh). split.
    + intros i Hi. destruct (nonempty3b i) eqn:Ei; [ | apply ile3_bot; exact Ei ].
      apply ile3_intro; cbn [lo3 hi3].
      * apply Hml_lb. exists i. split; [ exact Hi | split; [ exact Ei | reflexivity ] ].
      * apply Hmh_ub. exists i. split; [ exact Hi | split; [ exact Ei | reflexivity ] ].
    + intros u Hu. apply ile3_intro; cbn [lo3 hi3].
      * apply Hml_g. intros a [i [Hi [Ei Ha]]]. subst a.
        exact (proj1 (ile3_ne_inv i u Ei (Hu i Hi))).
      * apply Hmh_l. intros a [i [Hi [Ei Ha]]]. subst a.
        exact (proj2 (ile3_ne_inv i u Ei (Hu i Hi))).
  - exists ibot. split.
    + intros i Hi. apply ile3_bot. destruct (nonempty3b i) eqn:Ei; [ | reflexivity ].
      exfalso. apply Hallbot. exists i. split; [ exact Hi | exact Ei ].
    + intros u Hu. apply ile3_ibot.
Qed.
