(* ========================================================================= *)
(* Claim 16:                                                                 *)
(* "Addition and subtraction propagators are the best propagators."          *)
(*                                                                           *)
(* The addition propagator of the paper (Figure "def-propagators", box III): *)
(*   I[x = y + z]d =                                                         *)
(*     d(x) ← add(d(y), d(z))                                                *)
(*     d(y) ← sub(d(x), d(z))                                                *)
(*     d(z) ← sub(d(x), d(y))                                                *)
(*     return d                                                              *)
(*   I[x = y - z] = I[y = x + z]                                             *)
(* where d(v) ← E means d(v) := d(v) ⊓ E, returning d as soon as the         *)
(* updated interval is empty.                                                *)
(*                                                                           *)
(* We prove both are equal (up to the quotient ∼I) to the best interval      *)
(* propagator I[c] = αI ∘ S×[c] ∘ γI, i.e. sound and α-complete.             *)
(*                                                                           *)
(* The propagator is proved best for the constraint r = p + q for any        *)
(* pairwise-distinct triple of variables (r,p,q), which directly yields      *)
(* both the addition (x = y + z) and the subtraction (y = x + z) instances.  *)
(*                                                                           *)
(* This file also develops the Z∞ / interval arithmetic toolkit (Figures I   *)
(* and II of the paper) together with generic soundness/α-completeness       *)
(* helpers, reused by claims 17, 18, 20 and 21.                              *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical.
From Paper Require Import claim1 claim2 claim3 claim4 claim8 claim9 claim10
  claim11 claim12 claim15.
Open Scope Z_scope.

(* ==================== Arithmetic over Z∞ (Figure I) ==================== *)

Definition zadd (x y : Zinf) : Zinf :=
  match x, y with
  | MInf, _ => MInf
  | PInf, _ => PInf
  | Fin a, Fin b => Fin (a + b)
  | Fin _, MInf => MInf
  | Fin _, PInf => PInf
  end.

Definition zsub (x y : Zinf) : Zinf :=
  match x, y with
  | MInf, _ => MInf
  | PInf, _ => PInf
  | Fin a, Fin b => Fin (a - b)
  | Fin _, MInf => PInf
  | Fin _, PInf => MInf
  end.

Lemma zsub_as_zadd_zneg : forall a b, zsub a b = zadd a (zneg b).
Proof. intros [|x|] [|y|]; reflexivity. Qed.

(* ==================== Interval arithmetic (Figure II) ==================== *)

Definition ineg (i : Itv) : Itv := (zneg (snd i), zneg (fst i)).
Definition iadd (i j : Itv) : Itv :=
  (zadd (fst i) (fst j), zadd (snd i) (snd j)).
Definition isub (i j : Itv) : Itv :=
  (zsub (fst i) (snd j), zsub (snd i) (fst j)).

Lemma isub_as_iadd_ineg : forall i j, isub i j = iadd i (ineg j).
Proof.
  intros [a b] [c d]. unfold isub, iadd, ineg. simpl.
  rewrite !zsub_as_zadd_zneg. reflexivity.
Qed.

(* ---------- Membership lemmas ---------- *)

Lemma imem_imeet : forall v i j,
  imem v (imeet i j) <-> (imem v i /\ imem v j).
Proof.
  intros v i j. unfold imeet, imem. cbn [fst snd]. split.
  - intros [H1 H2]. repeat split.
    + eapply zle_trans; [apply zmax_ge_l | exact H1].
    + eapply zle_trans; [exact H2 | apply zmin_le_l].
    + eapply zle_trans; [apply zmax_ge_r | exact H1].
    + eapply zle_trans; [exact H2 | apply zmin_le_r].
  - intros [[H1 H2] [H3 H4]]. split.
    + apply zmax_lub; assumption.
    + apply zmin_glb; assumption.
Qed.

Lemma isbot_imeet_l : forall i j, isbot i -> isbot (imeet i j).
Proof.
  intros [a b] [c d] Hb. unfold isbot, imeet in *. cbn [fst snd] in *.
  destruct Hb as [H|[H|H]].
  - left. eapply zle_lt_trans; [apply zmin_le_l|].
    eapply zlt_le_trans; [exact H | apply zmax_ge_l].
  - subst. right; left.
    destruct (zmax_case PInf c) as [[E Hle]|[E _]]; [|exact E].
    destruct c; simpl in Hle; try contradiction. exact E.
  - subst. right; right.
    destruct (zmin_case MInf d) as [[E _]|[E Hle]]; [exact E|].
    destruct d; simpl in Hle; try contradiction. exact E.
Qed.

Lemma isbot_imeet_r : forall i j, isbot j -> isbot (imeet i j).
Proof.
  intros [a b] [c d] Hb. unfold isbot, imeet in *. cbn [fst snd] in *.
  destruct Hb as [H|[H|H]].
  - left. eapply zle_lt_trans; [apply zmin_le_r|].
    eapply zlt_le_trans; [exact H | apply zmax_ge_r].
  - subst. right; left.
    destruct (zmax_case a PInf) as [[E _]|[E Hle]]; [exact E|].
    destruct a; simpl in Hle; try contradiction. exact E.
  - subst. right; right.
    destruct (zmin_case b MInf) as [[E Hle]|[E _]]; [|exact E].
    destruct b; simpl in Hle; try contradiction. exact E.
Qed.

(* Unfolded characterization of non-empty intervals. *)
Lemma not_isbot_char : forall l u,
  ~ isbot (l, u) <-> (zle l u /\ l <> PInf /\ u <> MInf).
Proof.
  intros l u. unfold isbot. cbn [fst snd]. split.
  - intros H. apply not_or_and in H. destruct H as [H1 H].
    apply not_or_and in H. destruct H as [H2 H3].
    repeat split; try assumption. apply znlt_le. exact H1.
  - intros [H1 [H2 H3]] [H|[H|H]]; try contradiction.
    exact (zlt_nle _ _ H H1).
Qed.

Lemma imem_ineg : forall v i, imem v (ineg i) <-> imem (- v) i.
Proof.
  intros v [a b]. unfold ineg, imem. cbn [fst snd]. split.
  - intros [H1 H2]. split.
    + rewrite <- (zneg_involutive a).
      replace (Fin (- v)) with (zneg (Fin v)) by reflexivity.
      apply zneg_antitone. exact H2.
    + rewrite <- (zneg_involutive b).
      replace (Fin (- v)) with (zneg (Fin v)) by reflexivity.
      apply zneg_antitone. exact H1.
  - intros [H1 H2]. split.
    + replace (Fin v) with (zneg (Fin (- v))) by (simpl; f_equal; lia).
      apply zneg_antitone. exact H2.
    + replace (Fin v) with (zneg (Fin (- v))) by (simpl; f_equal; lia).
      apply zneg_antitone. exact H1.
Qed.

Lemma isbot_ineg : forall i, isbot (ineg i) <-> isbot i.
Proof.
  intros [a b]. unfold ineg, isbot. cbn [fst snd]. split.
  - intros [H|[H|H]].
    + left. destruct a as [|x|]; destruct b as [|y|]; simpl in *; try tauto; lia.
    + right; right. destruct b; simpl in H; congruence.
    + right; left. destruct a; simpl in H; congruence.
  - intros [H|[H|H]].
    + left. destruct a as [|x|]; destruct b as [|y|]; simpl in *; try tauto; lia.
    + subst. right; right. reflexivity.
    + subst. right; left. reflexivity.
Qed.

(* ---------- Soundness of interval addition/subtraction ---------- *)

Lemma zadd_le_lower : forall l l' (b c : Z),
  zle l (Fin b) -> zle l' (Fin c) -> zle (zadd l l') (Fin (b + c)).
Proof. intros [|x|] [|y|] b c; simpl; try tauto; lia. Qed.

Lemma zadd_ge_upper : forall u u' (b c : Z),
  zle (Fin b) u -> zle (Fin c) u' -> zle (Fin (b + c)) (zadd u u').
Proof. intros [|x|] [|y|] b c; simpl; try tauto; lia. Qed.

Lemma imem_iadd_intro : forall b c Y Z,
  imem b Y -> imem c Z -> imem (b + c) (iadd Y Z).
Proof.
  intros b c [yl yu] [zl zu] [H1 H2] [H3 H4]. cbn [fst snd] in *.
  split; cbn [iadd fst snd].
  - apply zadd_le_lower; assumption.
  - apply zadd_ge_upper; assumption.
Qed.

Lemma imem_isub_intro : forall b c Y Z,
  imem b Y -> imem c Z -> imem (b - c) (isub Y Z).
Proof.
  intros b c Y Z HY HZ. rewrite isub_as_iadd_ineg.
  replace (b - c) with (b + (- c)) by lia.
  apply imem_iadd_intro; [exact HY|].
  apply imem_ineg. rewrite Z.opp_involutive. exact HZ.
Qed.

(* ---------- Exactness (γ-decomposition) of interval addition ---------- *)

Lemma zadd_le_sub : forall a c (w : Z),
  zle (zadd a c) (Fin w) -> zle a (zsub (Fin w) c).
Proof. intros [|x|] [|y|] w; simpl; try tauto; lia. Qed.

Lemma sub_le_of_le_zadd : forall b d (w : Z),
  zle (Fin w) (zadd b d) -> zle (zsub (Fin w) d) b.
Proof. intros [|x|] [|y|] w; simpl; try tauto; lia. Qed.

Lemma zsub_fin_antitone : forall (w : Z) c c',
  zle c c' -> zle (zsub (Fin w) c') (zsub (Fin w) c).
Proof. intros w [|x|] [|y|]; simpl; try tauto; lia. Qed.

Lemma zsub_fin_le : forall (w b : Z) u,
  zle (zsub (Fin w) u) (Fin b) -> zle (Fin (w - b)) u.
Proof. intros w b [|y|]; simpl; try tauto; lia. Qed.

Lemma zsub_fin_ge : forall (w b : Z) l,
  zle (Fin b) (zsub (Fin w) l) -> zle l (Fin (w - b)).
Proof. intros w b [|y|]; simpl; try tauto; lia. Qed.

Lemma zmax_pinf : forall a b, zmax a b = PInf -> a = PInf \/ b = PInf.
Proof.
  intros a b H. destruct (zmax_case a b) as [[E _]|[E _]]; rewrite E in H; auto.
Qed.

Lemma zmin_minf : forall a b, zmin a b = MInf -> a = MInf \/ b = MInf.
Proof.
  intros a b H. destruct (zmin_case a b) as [[E _]|[E _]]; rewrite E in H; auto.
Qed.

Lemma zsub_fin_pinf : forall (w : Z) c, zsub (Fin w) c = PInf -> c = MInf.
Proof. intros w [|y|]; simpl; congruence. Qed.

Lemma zsub_fin_minf : forall (w : Z) c, zsub (Fin w) c = MInf -> c = PInf.
Proof. intros w [|y|]; simpl; congruence. Qed.

(* Decomposition of a member of an interval sum. *)
Lemma imem_iadd_elim : forall (w : Z) Y Z,
  ~ isbot Y -> ~ isbot Z -> imem w (iadd Y Z) ->
  exists b c, imem b Y /\ imem c Z /\ w = b + c.
Proof.
  intros w [yl yu] [zl zu] HY HZ [Hlo Hhi]. cbn [iadd fst snd] in Hlo, Hhi.
  apply not_isbot_char in HY. destruct HY as [Hy1 [Hy2 Hy3]].
  apply not_isbot_char in HZ. destruct HZ as [Hz1 [Hz2 Hz3]].
  (* B := [yl,yu] ⊓ [w - zu, w - zl] is a non-empty interval *)
  set (B := imeet (yl, yu) (zsub (Fin w) zu, zsub (Fin w) zl)).
  assert (HB : ~ isbot B).
  { unfold B, imeet. cbn [fst snd]. apply not_isbot_char. repeat split.
    - apply zmax_lub; apply zmin_glb.
      + exact Hy1.
      + apply zadd_le_sub. exact Hlo.
      + apply sub_le_of_le_zadd. exact Hhi.
      + apply zsub_fin_antitone. exact Hz1.
    - intros Hp. apply zmax_pinf in Hp. destruct Hp as [Hp|Hp].
      + exact (Hy2 Hp).
      + exact (Hz3 (zsub_fin_pinf _ _ Hp)).
    - intros Hm. apply zmin_minf in Hm. destruct Hm as [Hm|Hm].
      + exact (Hy3 Hm).
      + exact (Hz2 (zsub_fin_minf _ _ Hm)). }
  destruct (not_isbot_mem B HB) as [b Hb].
  unfold B in Hb. apply imem_imeet in Hb. destruct Hb as [HbY [Hb1 Hb2]].
  cbn [fst snd] in Hb1, Hb2.
  exists b, (w - b). repeat split.
  - destruct HbY as [H1 H2]; exact H1.
  - destruct HbY as [H1 H2]; exact H2.
  - apply zsub_fin_ge. exact Hb2.
  - apply zsub_fin_le. exact Hb1.
  - lia.
Qed.

Lemma imem_isub_elim : forall (w : Z) Y Z,
  ~ isbot Y -> ~ isbot Z -> imem w (isub Y Z) ->
  exists b c, imem b Y /\ imem c Z /\ w = b - c.
Proof.
  intros w Y Z HY HZ Hm. rewrite isub_as_iadd_ineg in Hm.
  destruct (imem_iadd_elim w Y (ineg Z)) as [b [c [Hb [Hc Heq]]]];
    [exact HY | | exact Hm |].
  - intro Hb. apply HZ. apply isbot_ineg. exact Hb.
  - exists b, (- c). split; [exact Hb|]. split; [|lia].
    apply imem_ineg in Hc. exact Hc.
Qed.

(* ---------- Clamped members ---------- *)

Lemma zmax_minf_r : forall a, zmax a MInf = a.
Proof. intros [|x|]; reflexivity. Qed.

Lemma zmin_pinf_r : forall a, zmin a PInf = a.
Proof. intros [|x|]; reflexivity. Qed.

(* A non-empty interval whose lower bound is at most M has a member ≤ M. *)
Lemma mem_below : forall i (M : Z),
  ~ isbot i -> zle (fst i) (Fin M) ->
  exists v, imem v i /\ (v <= M)%Z.
Proof.
  intros [l u] M Hnb Hle. cbn [fst snd] in Hle.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  assert (Hj : ~ isbot (imeet (l, u) (MInf, Fin M))).
  { unfold imeet. cbn [fst snd]. rewrite zmax_minf_r. apply not_isbot_char.
    repeat split.
    - apply zmin_glb; assumption.
    - exact H2.
    - intros Hm. apply zmin_minf in Hm.
      destruct Hm as [Hm|Hm]; [exact (H3 Hm) | discriminate Hm]. }
  destruct (not_isbot_mem _ Hj) as [v Hv].
  apply imem_imeet in Hv. destruct Hv as [Hvi [_ HvM]].
  simpl in HvM. exists v. split; [exact Hvi | exact HvM].
Qed.

Lemma mem_above : forall i (M : Z),
  ~ isbot i -> zle (Fin M) (snd i) ->
  exists v, imem v i /\ (M <= v)%Z.
Proof.
  intros [l u] M Hnb Hle. cbn [fst snd] in Hle.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  assert (Hj : ~ isbot (imeet (l, u) (Fin M, PInf))).
  { unfold imeet. cbn [fst snd]. rewrite zmin_pinf_r. apply not_isbot_char.
    repeat split.
    - apply zmax_lub; assumption.
    - intros Hp. apply zmax_pinf in Hp.
      destruct Hp as [Hp|Hp]; [exact (H2 Hp) | discriminate Hp].
    - exact H3. }
  destruct (not_isbot_mem _ Hj) as [v Hv].
  apply imem_imeet in Hv. destruct Hv as [Hvi [HvM _]].
  simpl in HvM. exists v. split; [exact Hvi | exact HvM].
Qed.

(* ---------- Witness-based bounds on hulls ---------- *)

Lemma zinf_le_of_wit : forall (V : Z -> Prop) (l : Zinf),
  (forall M : Z, zle l (Fin M) -> exists v, V v /\ (v <= M)%Z) ->
  zle (zinfS (finset V)) l.
Proof.
  intros V l H. destruct l as [|b|].
  - destruct (zinfS (finset V)) eqn:E; simpl; try exact I.
    + exfalso. destruct (H (z - 1)) as [v [Hv Hle]]; [exact I|].
      assert (Hlb : zle (zinfS (finset V)) (Fin v)).
      { apply zinfS_lb. exists v. auto. }
      rewrite E in Hlb. simpl in Hlb. lia.
    + exfalso. destruct (H 0) as [v [Hv _]]; [exact I|].
      assert (Hlb : zle (zinfS (finset V)) (Fin v)).
      { apply zinfS_lb. exists v. auto. }
      rewrite E in Hlb. simpl in Hlb. exact Hlb.
  - destruct (H b) as [v [Hv Hle]]; [apply zle_refl|].
    assert (Hlb : zle (zinfS (finset V)) (Fin v)).
    { apply zinfS_lb. exists v. auto. }
    eapply zle_trans; [exact Hlb | simpl; lia].
  - destruct (zinfS (finset V)); simpl; exact I.
Qed.

Lemma zsup_ge_of_wit : forall (V : Z -> Prop) (u : Zinf),
  (forall M : Z, zle (Fin M) u -> exists v, V v /\ (M <= v)%Z) ->
  zle u (zsup (finset V)).
Proof.
  intros V u H. destruct u as [|b|].
  - destruct (zsup (finset V)); simpl; exact I.
  - destruct (H b) as [v [Hv Hle]]; [apply zle_refl|].
    assert (Hub : zle (Fin v) (zsup (finset V))).
    { apply zsup_ub. exists v. auto. }
    eapply zle_trans; [|exact Hub]. simpl. lia.
  - destruct (zsup (finset V)) eqn:E; simpl; try exact I.
    + exfalso. destruct (H 0) as [v [Hv _]]; [exact I|].
      assert (Hub : zle (Fin v) (zsup (finset V))).
      { apply zsup_ub. exists v. auto. }
      rewrite E in Hub. simpl in Hub. exact Hub.
    + exfalso. destruct (H (z + 1)) as [v [Hv Hle]]; [exact I|].
      assert (Hub : zle (Fin v) (zsup (finset V))).
      { apply zsup_ub. exists v. auto. }
      rewrite E in Hub. simpl in Hub. lia.
Qed.

(* ---------- Generic soundness / α-completeness helpers ---------- *)

Section GenericHelpers.
  Context {X : Type}.

  (* A propagator that preserves every solution of the box is sound. *)
  Lemma sols_preserved_sound :
    forall (c : constraint X) (e : istore X) (d : istore X),
      (forall asn, csem c (ibox d) asn -> forall w, imem (asn w) (e w)) ->
      leI X (bestI c d) e.
  Proof.
    intros c e d Hpres.
    destruct (classic (exists asn, csem c (ibox d) asn)) as [[asn0 Hs0]|Hno].
    - right. intros w. right.
      unfold bestI, ihull, alphai. split; cbn [fst snd].
      + apply zinfS_greatest. intros v' [v [[asn [Hs Hv]] Heq]].
        subst v' v. destruct (Hpres asn Hs w) as [H1 _]. exact H1.
      + apply zsup_least. intros v' [v [[asn [Hs Hv]] Heq]].
        subst v' v. destruct (Hpres asn Hs w) as [_ H2]. exact H2.
    - left. apply no_sol_bestI_bot. intros asn Hs. apply Hno. eauto.
  Qed.

  (* An interval is below the best propagation of variable w as soon as all
     its "clamped" bounds are witnessed by solutions in the box. *)
  Lemma isle_bestI_of_wit :
    forall (c : constraint X) (d : istore X) (i : Itv) (w : X),
      (forall M : Z, zle (fst i) (Fin M) ->
         exists asn, csem c (ibox d) asn /\ (asn w <= M)%Z) ->
      (forall M : Z, zle (Fin M) (snd i) ->
         exists asn, csem c (ibox d) asn /\ (M <= asn w)%Z) ->
      isle i (bestI c d w).
  Proof.
    intros c d i w Hlo Hhi. right.
    unfold bestI, ihull, alphai. split; cbn [fst snd].
    - apply zinf_le_of_wit. intros M HM.
      destruct (Hlo M HM) as [asn [Hs Hle]].
      exists (asn w). split; [|exact Hle]. exists asn. auto.
    - apply zsup_ge_of_wit. intros M HM.
      destruct (Hhi M HM) as [asn [Hs Hle]].
      exists (asn w). split; [|exact Hle]. exists asn. auto.
  Qed.

End GenericHelpers.

(* ==================== Stores over the three variables ==================== *)

(* Store update. *)
Definition vupd (d : istore V3) (w : V3) (i : Itv) : istore V3 :=
  fun w' => if V3_eq_dec w' w then i else d w'.

Lemma vupd_same : forall d w i, vupd d w i w = i.
Proof.
  intros d w i. unfold vupd. destruct (V3_eq_dec w w); congruence.
Qed.

Lemma vupd_other : forall d w i w', w' <> w -> vupd d w i w' = d w'.
Proof.
  intros d w i w' H. unfold vupd. destruct (V3_eq_dec w' w); congruence.
Qed.

(* Coverage of V3 by three pairwise distinct variables. *)
Lemma V3_cover : forall (r p q : V3),
  r <> p -> r <> q -> p <> q ->
  forall w : V3, w = r \/ w = p \/ w = q.
Proof.
  intros r p q Hrp Hrq Hpq w.
  destruct r, p, q; try congruence; destruct w;
    ((left; congruence) || (right; left; congruence)
     || (right; right; congruence)).
Qed.

(* Assignment over V3 defined by the values of r, p, q. *)
Definition asn_rpq (r p q : V3) (a b c : Z) : Asn V3 :=
  fun w => if V3_eq_dec w r then a
           else if V3_eq_dec w p then b else c.

Lemma asn_rpq_r : forall r p q a b c, asn_rpq r p q a b c r = a.
Proof.
  intros. unfold asn_rpq. destruct (V3_eq_dec r r); congruence.
Qed.

Lemma asn_rpq_p : forall r p q a b c, r <> p -> asn_rpq r p q a b c p = b.
Proof.
  intros. unfold asn_rpq.
  destruct (V3_eq_dec p r); [congruence|].
  destruct (V3_eq_dec p p); congruence.
Qed.

Lemma asn_rpq_q : forall r p q a b c, r <> q -> p <> q -> asn_rpq r p q a b c q = c.
Proof.
  intros. unfold asn_rpq.
  destruct (V3_eq_dec q r); [congruence|].
  destruct (V3_eq_dec q p); congruence.
Qed.

(* ==================== The addition propagator ==================== *)

Section AddPropagator.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  (* The constraint r = p + q. *)
  Definition c_add : constraint V3 := MkC r p q OAdd.

  (* The three successive interval refinements of Figure III.  The paper's
     "d(v) ← E" updates d(v) to d(v) ⊓ E and returns early when the result
     is empty; computing the three refinements first and dispatching on
     emptiness afterwards yields exactly the same returned store. *)
  Definition addR (d : istore V3) : Itv := imeet (d r) (iadd (d p) (d q)).
  Definition addP (d : istore V3) : Itv := imeet (d p) (isub (addR d) (d q)).
  Definition addQ (d : istore V3) : Itv := imeet (d q) (isub (addR d) (addP d)).

  Definition prop_add (d : istore V3) : istore V3 :=
    if isbotb (addR d) then vupd d r (addR d)
    else if isbotb (addP d) then vupd (vupd d r (addR d)) p (addP d)
    else vupd (vupd (vupd d r (addR d)) p (addP d)) q (addQ d).

  (* Solutions of r = p + q inside the box are preserved by every step. *)
  Lemma prop_add_preserves :
    forall d asn, csem c_add (ibox d) asn ->
      forall w, imem (asn w) (prop_add d w).
  Proof.
    intros d asn [Hbox Hrel] w.
    unfold rel, c_add in Hrel. cbn [op_rel cop cx cy cz] in Hrel.
    assert (HmR : imem (asn r) (addR d)).
    { unfold addR. apply imem_imeet. split; [apply Hbox|].
      rewrite Hrel. apply imem_iadd_intro; apply Hbox. }
    assert (HmP : imem (asn p) (addP d)).
    { unfold addP. apply imem_imeet. split; [apply Hbox|].
      replace (asn p) with (asn r - asn q) by lia.
      apply imem_isub_intro; [exact HmR | apply Hbox]. }
    assert (HmQ : imem (asn q) (addQ d)).
    { unfold addQ. apply imem_imeet. split; [apply Hbox|].
      replace (asn q) with (asn r - asn p) by lia.
      apply imem_isub_intro; [exact HmR | exact HmP]. }
    unfold prop_add.
    destruct (isbotb (addR d)) eqn:ER.
    { exfalso. apply isbotb_isbot in ER. exact (imem_not_isbot _ _ HmR ER). }
    destruct (isbotb (addP d)) eqn:EP.
    { exfalso. apply isbotb_isbot in EP. exact (imem_not_isbot _ _ HmP EP). }
    destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
    - rewrite (vupd_other _ q _ r) by congruence.
      rewrite (vupd_other _ p _ r) by congruence.
      rewrite vupd_same. exact HmR.
    - rewrite (vupd_other _ q _ p) by congruence.
      rewrite vupd_same. exact HmP.
    - rewrite vupd_same. exact HmQ.
  Qed.

  (* Soundness. *)
  Lemma prop_add_sound : forall d, leI V3 (bestI c_add d) (prop_add d).
  Proof.
    intros d. apply sols_preserved_sound. apply prop_add_preserves.
  Qed.

  (* α-completeness. *)
  Lemma prop_add_complete : forall d, leI V3 (prop_add d) (bestI c_add d).
  Proof.
    intros d. unfold prop_add.
    destruct (isbotb (addR d)) eqn:ER.
    { (* early return: the output is failed *)
      apply isbotb_isbot in ER. left. exists r. rewrite vupd_same. exact ER. }
    apply isbotb_false in ER.
    destruct (isbotb (addP d)) eqn:EP.
    { apply isbotb_isbot in EP. left. exists p. rewrite vupd_same. exact EP. }
    apply isbotb_false in EP.
    destruct (classic (isbot (addQ d))) as [EQ|EQ].
    { left. exists q. rewrite vupd_same. exact EQ. }
    (* main case: R, P, Q are all non-empty *)
    assert (Hdp : ~ isbot (d p)).
    { intro Hb. apply EP. apply isbot_imeet_l. exact Hb. }
    assert (Hdq : ~ isbot (d q)).
    { intro Hb. apply EQ. apply isbot_imeet_l. exact Hb. }
    (* a member of R decomposes into a solution of the box *)
    assert (Hdec : forall a, imem a (addR d) ->
              exists asn, csem c_add (ibox d) asn /\ asn r = a).
    { intros a Ha. unfold addR in Ha.
      apply imem_imeet in Ha. destruct Ha as [Har Hadd].
      destruct (imem_iadd_elim a (d p) (d q) Hdp Hdq Hadd)
        as [b [c [Hb [Hc Heq]]]].
      exists (asn_rpq r p q a b c). split; [split|].
      - intros w. destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
        + rewrite asn_rpq_r. exact Har.
        + rewrite asn_rpq_p by exact Hrp. exact Hb.
        + rewrite asn_rpq_q by assumption. exact Hc.
      - unfold rel, c_add. cbn [op_rel cop cx cy cz].
        rewrite asn_rpq_r, asn_rpq_p, asn_rpq_q by assumption. exact Heq.
      - apply asn_rpq_r. }
    (* a member of P decomposes as well *)
    assert (HdecP : forall b, imem b (addP d) ->
              exists asn, csem c_add (ibox d) asn /\ asn p = b).
    { intros b Hb. unfold addP in Hb.
      apply imem_imeet in Hb. destruct Hb as [Hbp Hsub].
      destruct (imem_isub_elim b (addR d) (d q) ER Hdq Hsub)
        as [a [c [Ha [Hc Heq]]]].
      unfold addR in Ha. apply imem_imeet in Ha. destruct Ha as [Har _].
      exists (asn_rpq r p q a b c). split; [split|].
      - intros w. destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
        + rewrite asn_rpq_r. exact Har.
        + rewrite asn_rpq_p by exact Hrp. exact Hbp.
        + rewrite asn_rpq_q by assumption. exact Hc.
      - unfold rel, c_add. cbn [op_rel cop cx cy cz].
        rewrite asn_rpq_r, asn_rpq_p, asn_rpq_q by assumption. lia.
      - apply asn_rpq_p. exact Hrp. }
    (* a member of Q decomposes as well *)
    assert (HdecQ : forall c, imem c (addQ d) ->
              exists asn, csem c_add (ibox d) asn /\ asn q = c).
    { intros c Hc. unfold addQ in Hc.
      apply imem_imeet in Hc. destruct Hc as [Hcq Hsub].
      destruct (imem_isub_elim c (addR d) (addP d) ER EP Hsub)
        as [a [b [Ha [Hb Heq]]]].
      unfold addR in Ha. apply imem_imeet in Ha. destruct Ha as [Har _].
      unfold addP in Hb. apply imem_imeet in Hb. destruct Hb as [Hbp _].
      exists (asn_rpq r p q a b c). split; [split|].
      - intros w. destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
        + rewrite asn_rpq_r. exact Har.
        + rewrite asn_rpq_p by exact Hrp. exact Hbp.
        + rewrite asn_rpq_q by assumption. exact Hcq.
      - unfold rel, c_add. cbn [op_rel cop cx cy cz].
        rewrite asn_rpq_r, asn_rpq_p, asn_rpq_q by assumption. lia.
      - apply asn_rpq_q; assumption. }
    right. intros w.
    destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
    - rewrite (vupd_other _ q _ r) by congruence.
      rewrite (vupd_other _ p _ r) by congruence.
      rewrite vupd_same.
      apply isle_bestI_of_wit.
      + intros M HM. destruct (mem_below (addR d) M ER HM) as [a [Ha HaM]].
        destruct (Hdec a Ha) as [asn [Hs Heq]].
        exists asn. split; [exact Hs | lia].
      + intros M HM. destruct (mem_above (addR d) M ER HM) as [a [Ha HaM]].
        destruct (Hdec a Ha) as [asn [Hs Heq]].
        exists asn. split; [exact Hs | lia].
    - rewrite (vupd_other _ q _ p) by congruence.
      rewrite vupd_same.
      apply isle_bestI_of_wit.
      + intros M HM. destruct (mem_below (addP d) M EP HM) as [b [Hb HbM]].
        destruct (HdecP b Hb) as [asn [Hs Heq]].
        exists asn. split; [exact Hs | lia].
      + intros M HM. destruct (mem_above (addP d) M EP HM) as [b [Hb HbM]].
        destruct (HdecP b Hb) as [asn [Hs Heq]].
        exists asn. split; [exact Hs | lia].
    - rewrite vupd_same.
      apply isle_bestI_of_wit.
      + intros M HM. destruct (mem_below (addQ d) M EQ HM) as [c [Hc HcM]].
        destruct (HdecQ c Hc) as [asn [Hs Heq]].
        exists asn. split; [exact Hs | lia].
      + intros M HM. destruct (mem_above (addQ d) M EQ HM) as [c [Hc HcM]].
        destruct (HdecQ c Hc) as [asn [Hs Heq]].
        exists asn. split; [exact Hs | lia].
  Qed.

  (* The addition propagator is the best propagator for r = p + q. *)
  Theorem prop_add_best : forall d, eqI V3 (prop_add d) (bestI c_add d).
  Proof.
    intros d.
    apply (ole_antisym (o := I_OSet V3)); [apply prop_add_complete | apply prop_add_sound].
  Qed.

End AddPropagator.

(* ==================== CLAIM 16 ==================== *)

(* The addition propagator I[x = y + z] is the best propagator. *)
Theorem claim16_add : forall d,
  eqI V3 (prop_add Vx Vy Vz d) (bestI (MkC Vx Vy Vz OAdd) d).
Proof.
  apply prop_add_best; congruence.
Qed.

(* Best propagators only depend on the solution set of the constraint. *)
Lemma bestI_rel_ext : forall (X : Type) (c c' : constraint X) (d : istore X),
  (forall asn, rel c asn <-> rel c' asn) ->
  forall w, bestI c d w = bestI c' d w.
Proof.
  intros X c c' d Hiff w.
  unfold bestI, ihull, alphai.
  assert (Hset : forall v,
    (exists asn, csem c (ibox d) asn /\ asn w = v)
    <-> (exists asn, csem c' (ibox d) asn /\ asn w = v)).
  { intros v. split; intros [asn [[Hb Hr] Hv]]; exists asn;
      (split; [split; [exact Hb | apply Hiff; exact Hr] | exact Hv]). }
  f_equal.
  - apply zle_antisym; apply zinfS_greatest; intros x [v [Hv Heq]]; subst;
      apply zinfS_lb; exists v; split; try reflexivity; apply Hset; exact Hv.
  - apply zle_antisym; apply zsup_least; intros x [v [Hv Heq]]; subst;
      apply zsup_ub; exists v; split; try reflexivity; apply Hset; exact Hv.
Qed.

(* The subtraction propagator I[x = y - z] = I[y = x + z] is the best
   propagator for x = y - z. *)
Theorem claim16_sub : forall d,
  eqI V3 (prop_add Vy Vx Vz d) (bestI (MkC Vx Vy Vz OSub) d).
Proof.
  intros d.
  assert (Hbest := prop_add_best Vy Vx Vz ltac:(congruence) ltac:(congruence)
                     ltac:(congruence) d).
  assert (Hext : forall w, bestI (c_add Vy Vx Vz) d w
                           = bestI (MkC Vx Vy Vz OSub) d w).
  { apply bestI_rel_ext. intros asn. unfold rel, c_add. simpl. lia. }
  destruct Hbest as [[H1 H2]|H].
  - left. split; [exact H1|].
    destruct H2 as [w Hw]. exists w. rewrite <- Hext. exact Hw.
  - right. intros w. rewrite <- Hext. apply H.
Qed.

(* Combined statement of claim 16. *)
Theorem claim16 : forall d,
  eqI V3 (prop_add Vx Vy Vz d) (bestI (MkC Vx Vy Vz OAdd) d) /\
  eqI V3 (prop_add Vy Vx Vz d) (bestI (MkC Vx Vy Vz OSub) d).
Proof.
  intros d. split; [apply claim16_add | apply claim16_sub].
Qed.
