(* ========================================================================= *)
(* Claim 9:                                                                  *)
(* "The lattice Ĩ = ⟨I/∼, ⊑, ⊔, ⊓⟩ views all empty intervals as equivalent   *)
(*  ... Further, it is a complete lattice."                                  *)
(*                                                                           *)
(* We prove that the paper's ⊔ and ⊓ are binary joins and meets of the       *)
(* quotient order ⊑, and that the quotient is a complete lattice: every      *)
(* subset has a least upper bound and a greatest lower bound.                *)
(*                                                                           *)
(* The suprema of arbitrary sets of extended integers are obtained           *)
(* classically (bounded sets of integers have maxima); this file provides    *)
(* zsup/zinf on P(Z∞) together with their characteristic properties, which   *)
(* are the workhorses of all later interval claims.                          *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical ClassicalEpsilon.
From Paper Require Import claim1 claim2 claim8.
Open Scope Z_scope.

(* ==================== Classical maxima of bounded sets ==================== *)

Lemma Z_bounded_max : forall (P : Z -> Prop),
  (exists z, P z) -> (exists b, forall z, P z -> z <= b) ->
  exists m, P m /\ forall z, P z -> z <= m.
Proof.
  intros P [z0 Hz0] [b Hb].
  assert (Main : forall (n : nat) (c : Z),
             (forall z, P z -> z <= c) ->
             (exists z, P z /\ c - Z.of_nat n <= z) ->
             exists m, P m /\ forall z, P z -> z <= m).
  { induction n as [|n IH]; intros c Hc [z [Hz Hge]].
    - exists z. split; [exact Hz|]. intros z' Hz'.
      simpl in Hge.
      pose proof (Hc z Hz). pose proof (Hc z' Hz'). lia.
    - destruct (classic (exists z', P z' /\ c - Z.of_nat n <= z')) as [He|He].
      + exact (IH c Hc He).
      + exists z. split; [exact Hz|]. intros z' Hz'.
        assert (Hlt : ~ (c - Z.of_nat n <= z')) by (intro; apply He; eauto).
        rewrite Nat2Z.inj_succ in Hge. lia. }
  apply (Main (Z.to_nat (b - z0)) b Hb).
  exists z0. split; [exact Hz0|].
  pose proof (Hb z0 Hz0). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma Z_bounded_min : forall (P : Z -> Prop),
  (exists z, P z) -> (exists b, forall z, P z -> b <= z) ->
  exists m, P m /\ forall z, P z -> m <= z.
Proof.
  intros P [z0 Hz0] [b Hb].
  destruct (Z_bounded_max (fun z => P (- z))) as [m [Hm Hmax]].
  - exists (- z0). rewrite Z.opp_involutive. exact Hz0.
  - exists (- b). intros z Hz. specialize (Hb _ Hz). lia.
  - exists (- m). split; [exact Hm|]. intros z Hz.
    specialize (Hmax (- z)). rewrite Z.opp_involutive in Hmax.
    specialize (Hmax Hz). lia.
Qed.

(* ==================== Suprema and infima on Z∞ ==================== *)

Definition zub (S : Zinf -> Prop) (b : Zinf) : Prop := forall x, S x -> zle x b.
Definition zlb (S : Zinf -> Prop) (b : Zinf) : Prop := forall x, S x -> zle b x.
Definition z_is_lub (S : Zinf -> Prop) (l : Zinf) : Prop :=
  zub S l /\ forall b, zub S b -> zle l b.
Definition z_is_glb (S : Zinf -> Prop) (g : Zinf) : Prop :=
  zlb S g /\ forall b, zlb S b -> zle b g.

Lemma z_lub_exists : forall S, exists l, z_is_lub S l.
Proof.
  intros S.
  destruct (classic (S PInf \/ forall M : Z, exists z, S (Fin z) /\ M <= z))
    as [HA|HA].
  - (* unbounded above (or contains +∞): lub = +∞ *)
    exists PInf. split.
    + intros x _. destruct x; simpl; exact I.
    + intros b Hb. destruct b as [|m|]; simpl.
      * (* b = -∞ impossible *)
        destruct HA as [HP|HU].
        -- exact (Hb PInf HP).
        -- destruct (HU 0) as [z [Hz _]]. exact (Hb (Fin z) Hz).
      * (* b = Fin m impossible *)
        destruct HA as [HP|HU].
        -- exact (Hb PInf HP).
        -- destruct (HU (m + 1)) as [z [Hz Hge]].
           specialize (Hb (Fin z) Hz). simpl in Hb. lia.
      * exact I.
  - (* bounded above and no +∞ *)
    apply not_or_and in HA. destruct HA as [HnP HnU].
    apply not_all_ex_not in HnU. destruct HnU as [M HM].
    assert (Hbound : forall z, S (Fin z) -> z <= M - 1).
    { intros z Hz. destruct (Z_le_gt_dec z (M - 1)); [assumption|].
      exfalso. apply HM. exists z. split; [assumption | lia]. }
    destruct (classic (exists z, S (Fin z))) as [Hne|Hne].
    + destruct (Z_bounded_max (fun z => S (Fin z)) Hne) as [m [Hm Hmax]].
      { exists (M - 1). exact Hbound. }
      exists (Fin m). split.
      * intros x Hx. destruct x as [|z|]; simpl.
        -- exact I.
        -- apply Hmax, Hx.
        -- contradiction.
      * intros b Hb. exact (Hb (Fin m) Hm).
    + (* S ⊆ {-∞} : lub = -∞ *)
      exists MInf. split.
      * intros x Hx. destruct x as [|z|]; simpl.
        -- exact I.
        -- exfalso. apply Hne. eauto.
        -- contradiction.
      * intros b Hb. destruct b; simpl; exact I.
Qed.

Definition zsup (S : Zinf -> Prop) : Zinf :=
  epsilon (inhabits MInf) (z_is_lub S).

Lemma zsup_spec : forall S, z_is_lub S (zsup S).
Proof.
  intros S. unfold zsup. apply epsilon_spec. apply z_lub_exists.
Qed.

Lemma zsup_ub : forall S x, S x -> zle x (zsup S).
Proof. intros S x Hx. destruct (zsup_spec S) as [Hub _]. apply Hub, Hx. Qed.

Lemma zsup_least : forall S b, zub S b -> zle (zsup S) b.
Proof. intros S b Hb. destruct (zsup_spec S) as [_ Hl]. apply Hl, Hb. Qed.

(* Negation on Z∞, giving glbs by duality. *)
Definition zneg (a : Zinf) : Zinf :=
  match a with MInf => PInf | Fin z => Fin (- z) | PInf => MInf end.

Lemma zneg_involutive : forall a, zneg (zneg a) = a.
Proof. intros [|z|]; simpl; try reflexivity. f_equal; lia. Qed.

Lemma zneg_antitone : forall a b, zle a b -> zle (zneg b) (zneg a).
Proof. intros [|x|] [|y|]; simpl; try tauto; lia. Qed.

Definition zinfS (S : Zinf -> Prop) : Zinf :=
  zneg (zsup (fun x => S (zneg x))).

Lemma zinfS_lb : forall S x, S x -> zle (zinfS S) x.
Proof.
  intros S x Hx. unfold zinfS.
  rewrite <- (zneg_involutive x).
  apply zneg_antitone, zsup_ub.
  rewrite zneg_involutive. exact Hx.
Qed.

Lemma zinfS_greatest : forall S b, zlb S b -> zle b (zinfS S).
Proof.
  intros S b Hb. unfold zinfS.
  rewrite <- (zneg_involutive b).
  apply zneg_antitone, zsup_least.
  intros x Hx. rewrite <- (zneg_involutive x).
  apply zneg_antitone, Hb, Hx.
Qed.

Lemma zinfS_spec : forall S, z_is_glb S (zinfS S).
Proof.
  intros S. split; [intros x Hx; apply zinfS_lb; exact Hx | apply zinfS_greatest].
Qed.

(* ---------- Discreteness and characterizations of zsup/zinf ---------- *)

Lemma zlt_fin_pred : forall x b, zlt x (Fin b) -> zle x (Fin (b - 1)).
Proof. intros [|z|] b; simpl; try tauto; lia. Qed.

Lemma fin_lt_succ : forall x b, zlt (Fin b) x -> zle (Fin (b + 1)) x.
Proof. intros [|z|] b; simpl; try tauto; lia. Qed.

(* Finite bound below a sup: some element is above it. *)
Lemma fin_le_zsup_inv : forall S b,
  zle (Fin b) (zsup S) -> exists x, S x /\ zle (Fin b) x.
Proof.
  intros S b Hle.
  destruct (classic (exists x, S x /\ zle (Fin b) x)) as [H|H]; [exact H|].
  exfalso.
  assert (Hub : zub S (Fin (b - 1))).
  { intros x Hx. apply zlt_fin_pred, znle_lt.
    intro Hc. apply H. eauto. }
  pose proof (zsup_least S _ Hub) as Hs.
  pose proof (zle_trans _ _ _ Hle Hs). simpl in *. lia.
Qed.

(* Sup equal to +∞: elements are unbounded. *)
Lemma zsup_pinf_inv : forall S,
  zle PInf (zsup S) -> forall M : Z, exists x, S x /\ zle (Fin M) x.
Proof.
  intros S Hle M.
  destruct (classic (exists x, S x /\ zle (Fin M) x)) as [H|H]; [exact H|].
  exfalso.
  assert (Hub : zub S (Fin (M - 1))).
  { intros x Hx. apply zlt_fin_pred, znle_lt.
    intro Hc. apply H. eauto. }
  pose proof (zsup_least S _ Hub) as Hs.
  pose proof (zle_trans _ _ _ Hle Hs). simpl in *. lia.
Qed.

Lemma zinfS_fin_inv : forall S b,
  zle (zinfS S) (Fin b) -> exists x, S x /\ zle x (Fin b).
Proof.
  intros S b Hle.
  destruct (classic (exists x, S x /\ zle x (Fin b))) as [H|H]; [exact H|].
  exfalso.
  assert (Hlb : zlb S (Fin (b + 1))).
  { intros x Hx. apply fin_lt_succ, znle_lt.
    intro Hc. apply H. eauto. }
  pose proof (zinfS_greatest S _ Hlb) as Hs.
  pose proof (zle_trans _ _ _ Hs Hle). simpl in *. lia.
Qed.

Lemma zinfS_minf_inv : forall S,
  zle (zinfS S) MInf -> forall M : Z, exists x, S x /\ zle x (Fin M).
Proof.
  intros S Hle M.
  destruct (classic (exists x, S x /\ zle x (Fin M))) as [H|H]; [exact H|].
  exfalso.
  assert (Hlb : zlb S (Fin (M + 1))).
  { intros x Hx. apply fin_lt_succ, znle_lt.
    intro Hc. apply H. eauto. }
  pose proof (zinfS_greatest S _ Hlb) as Hs.
  pose proof (zle_trans _ _ _ Hs Hle). simpl in *. lia.
Qed.

(* Sup/inf of the empty set. *)
Lemma zsup_empty : forall S, (forall x, ~ S x) -> zsup S = MInf.
Proof.
  intros S H. apply zle_antisym.
  - apply zsup_least. intros x Hx. destruct (H x Hx).
  - destruct (zsup S); simpl; exact I.
Qed.

Lemma zinfS_empty : forall S, (forall x, ~ S x) -> zinfS S = PInf.
Proof.
  intros S H. apply zle_antisym.
  - destruct (zinfS S); simpl; exact I.
  - apply zinfS_greatest. intros x Hx. destruct (H x Hx).
Qed.

(* ==================== The quotient interval lattice Ĩ ==================== *)

(* Empty ("bottom") intervals: ℓ > u ∨ ℓ = +∞ ∨ u = -∞. *)
Definition isbot (i : Itv) : Prop :=
  zlt (snd i) (fst i) \/ fst i = PInf \/ snd i = MInf.

Definition isbotb (i : Itv) : bool :=
  (negb (zleb (fst i) (snd i)))
  || (match fst i with PInf => true | _ => false end)
  || (match snd i with MInf => true | _ => false end).

Lemma isbotb_isbot : forall i, isbotb i = true <-> isbot i.
Proof.
  intros [l u]. unfold isbotb, isbot. simpl.
  rewrite !Bool.orb_true_iff, Bool.negb_true_iff.
  split.
  - intros [[H|H]|H].
    + left. apply znle_lt. intro Hc. apply zleb_le in Hc. congruence.
    + right; left. destruct l; simpl in H; congruence.
    + right; right. destruct u; simpl in H; congruence.
  - intros [H|[H|H]].
    + left; left. destruct (zleb l u) eqn:E; [|reflexivity].
      apply zleb_le in E. exfalso. exact (zlt_nle _ _ H E).
    + left; right. rewrite H. reflexivity.
    + right. rewrite H. reflexivity.
Qed.

Lemma isbotb_false : forall i, isbotb i = false <-> ~ isbot i.
Proof.
  intros i. split.
  - intros H Hb. apply isbotb_isbot in Hb. congruence.
  - intros H. destruct (isbotb i) eqn:E; [|reflexivity].
    apply isbotb_isbot in E. contradiction.
Qed.

(* Membership of an integer in an interval. *)
Definition imem (v : Z) (i : Itv) : Prop :=
  zle (fst i) (Fin v) /\ zle (Fin v) (snd i).

Lemma isbot_no_mem : forall i, isbot i -> forall v, ~ imem v i.
Proof.
  intros [l u] Hb v [H1 H2]. simpl in *.
  destruct Hb as [H|[H|H]]; simpl in *.
  - apply (zlt_nle _ _ H). eapply zle_trans; eauto.
  - subst. destruct u; simpl in *; tauto.
  - subst. destruct l; simpl in *; tauto.
Qed.

Lemma not_isbot_mem : forall i, ~ isbot i -> exists v, imem v i.
Proof.
  intros [l u] Hb. unfold isbot in Hb. simpl in Hb.
  apply not_or_and in Hb. destruct Hb as [Hlu Hb].
  apply not_or_and in Hb. destruct Hb as [Hl Hu].
  apply znlt_le in Hlu.
  destruct l as [|a|]; destruct u as [|b|]; simpl in *; try congruence.
  - (* l = -∞, u = Fin b *) exists b. split; simpl; [exact I | lia].
  - (* l = -∞, u = +∞ *) exists 0. split; simpl; exact I.
  - (* l = Fin a, u = Fin b *) exists a. split; simpl; lia.
  - (* l = Fin a, u = +∞ *) exists a. split; simpl; [lia | exact I].
Qed.

Lemma imem_not_isbot : forall i v, imem v i -> ~ isbot i.
Proof. intros i v Hm Hb. exact (isbot_no_mem i Hb v Hm). Qed.

(* The quotient equality ∼, order ⊑, join ⊔ and meet ⊓ of the paper. *)
Definition ieq (i j : Itv) : Prop := (isbot i /\ isbot j) \/ i = j.
Definition isle (i j : Itv) : Prop := isbot i \/ ile i j.
Definition isjoin (i j : Itv) : Itv :=
  if isbotb i then j else if isbotb j then i else ijoin i j.
Definition ismeet (i j : Itv) : Itv := imeet i j.

(* An interval below an empty interval is empty. *)
Lemma ile_isbot : forall i j, ile i j -> isbot j -> isbot i.
Proof.
  intros [a b] [c d] [H1 H2] Hb. unfold isbot in *. simpl in *.
  destruct Hb as [H|[H|H]].
  - left. eapply zle_lt_trans; [exact H2|]. eapply zlt_le_trans; eauto.
  - subst c. destruct a; simpl in H1; try contradiction.
    right; left; reflexivity.
  - subst d. destruct b; simpl in H2; try contradiction.
    right; right; reflexivity.
Qed.

Definition QItv_OSet : OSet.
Proof.
  refine (MkOSet Itv ieq isle _ _ _ _ _ _).
  - intros i. right. reflexivity.
  - intros i j [[H1 H2]|H]; [left; tauto | right; congruence].
  - intros i j k [[H1 H2]|H] [[H3 H4]|H'].
    + left; tauto.
    + left. split; [exact H1 | rewrite <- H'; exact H2].
    + left. split; [rewrite H; exact H3 | exact H4].
    + right; congruence.
  - intros i j [[H1 H2]|H]; [left; exact H1 | right; rewrite H; split; apply zle_refl].
  - intros i j k [H|H] [H'|H'].
    + left; exact H.
    + left; exact H.
    + left. exact (ile_isbot i j H H').
    + right. destruct H as [H1 H2]; destruct H' as [H3 H4].
      split; eapply zle_trans; eauto.
  - intros i j [H|H] [H'|H'].
    + left; tauto.
    + left. split; [exact H | exact (ile_isbot j i H' H)].
    + left. split; [exact (ile_isbot i j H H') | exact H'].
    + right. destruct i as [a b]; destruct j as [c d].
      destruct H as [H1 H2]; destruct H' as [H3 H4]. simpl in *.
      f_equal; apply zle_antisym; assumption.
Defined.

(* ---------- The binary join and meet of the paper ---------- *)

Theorem claim9_binary_lattice : is_lattice QItv_OSet isjoin ismeet.
Proof.
  repeat split.
  - (* x ⊑ x ⊔ y *)
    intros i j. simpl. unfold isjoin.
    destruct (isbotb i) eqn:Ei.
    + left. apply isbotb_isbot, Ei.
    + destruct (isbotb j) eqn:Ej.
      * right. split; apply zle_refl.
      * right. split; simpl; [apply zmin_le_l | apply zmax_ge_l].
  - (* y ⊑ x ⊔ y *)
    intros i j. simpl. unfold isjoin.
    destruct (isbotb i) eqn:Ei.
    + right. split; apply zle_refl.
    + destruct (isbotb j) eqn:Ej.
      * left. apply isbotb_isbot, Ej.
      * right. split; simpl; [apply zmin_le_r | apply zmax_ge_r].
  - (* least upper bound *)
    intros i j k Hi Hj. simpl in *. unfold isjoin.
    destruct (isbotb i) eqn:Ei; [exact Hj|].
    destruct (isbotb j) eqn:Ej; [exact Hi|].
    apply isbotb_false in Ei. apply isbotb_false in Ej.
    destruct Hi as [Hi|Hi]; [contradiction|].
    destruct Hj as [Hj|Hj]; [contradiction|].
    right. destruct Hi as [H1 H2]; destruct Hj as [H3 H4].
    split; simpl; [apply zmin_glb; assumption | apply zmax_lub; assumption].
  - (* x ⊓ y ⊑ x *)
    intros i j. simpl. unfold ismeet.
    right. split; simpl; [apply zmax_ge_l | apply zmin_le_l].
  - (* x ⊓ y ⊑ y *)
    intros i j. simpl. unfold ismeet.
    right. split; simpl; [apply zmax_ge_r | apply zmin_le_r].
  - (* greatest lower bound *)
    intros i j k Hi Hj. simpl in *. unfold ismeet.
    destruct Hi as [Hi|Hi]; [left; exact Hi|].
    destruct Hj as [Hj|Hj]; [left; exact Hj|].
    right. destruct Hi as [H1 H2]; destruct Hj as [H3 H4].
    split; simpl; [apply zmax_lub; assumption | apply zmin_glb; assumption].
Qed.

(* ---------- Completeness ---------- *)

(* Supremum of an arbitrary set of intervals: hull of the non-empty members. *)
Definition issup (S : Itv -> Prop) : Itv :=
  (zinfS (fun l => exists i, S i /\ ~ isbot i /\ fst i = l),
   zsup (fun u => exists i, S i /\ ~ isbot i /\ snd i = u)).

Definition QItv_CL : CompleteLattice.
Proof.
  refine (MkCL QItv_OSet issup _ _).
  - (* upper bound *)
    intros S i HiS. simpl.
    destruct (classic (isbot i)) as [Hb|Hb].
    + left; exact Hb.
    + right. split; simpl.
      * apply zinfS_lb. exists i; auto.
      * apply zsup_ub. exists i; auto.
  - (* least *)
    intros S k Hub. simpl in *.
    destruct (classic (exists i, S i /\ ~ isbot i)) as [Hne|Hne].
    + destruct Hne as [i0 [HS0 Hb0]].
      right. split; simpl.
      * (* fst k ≤ zinfS L *)
        apply zinfS_greatest. intros l [i [HiS [Hib Hfst]]]. subst l.
        destruct (Hub i HiS) as [Hb|[H1 H2]]; [contradiction | exact H1].
      * apply zsup_least. intros u [i [HiS [Hib Hsnd]]]. subst u.
        destruct (Hub i HiS) as [Hb|[H1 H2]]; [contradiction | exact H2].
    + (* all members are empty: the sup is an empty interval *)
      left. unfold isbot. simpl. right; left.
      apply zinfS_empty. intros l [i [HiS [Hib _]]].
      apply Hne. eauto.
Defined.

(* ======================= CLAIM 9 ======================= *)
Theorem claim9 : complete_lattice QItv_OSet.
Proof. exact (CompleteLattice_complete QItv_CL). Qed.
