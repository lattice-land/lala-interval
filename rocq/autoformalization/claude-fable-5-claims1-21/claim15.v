(* ========================================================================= *)
(* Claim 15:                                                                 *)
(* "A sound and reductive propagator p_c ∈ I → I enforces bounds(Z)          *)
(*  consistency on a constraint c iff for all x ∈ X and v ∈ {l,u} for        *)
(*  [l,u] = p_c(d)(x), there exists asn ∈ rel(c) such that asn(x) = v ∧      *)
(*  ∀y ∈ X, asn(y) ∈ p_c(d)(y).  A propagator p_c enforces bounds(Z) iff     *)
(*  p_c = I[c] (on bounded intervals as bounds(Z) consistency is not         *)
(*  defined for infinite intervals)."                                        *)
(*                                                                           *)
(* Here I[c] = αI ∘ S×[c] ∘ γI is the best interval propagator, i.e. the     *)
(* interval hull of the solutions of c inside the box γI(d).  This file      *)
(* introduces ibox/ihull/bestI, reused by claims 16-21.                      *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical.
From Paper Require Import claim1 claim2 claim3 claim8 claim9 claim10 claim11 claim12 claim13.
Open Scope Z_scope.

(* Basic monotonicity of interval membership. *)
Lemma imem_ile : forall v i j, imem v i -> ile i j -> imem v j.
Proof.
  intros v i j [H1 H2] [H3 H4]. split.
  - eapply zle_trans; [exact H3 | exact H1].
  - eapply zle_trans; [exact H2 | exact H4].
Qed.

(* ---------- The best interval propagator ---------- *)

Section BestInterval.
  Context {X : Type}.

  (* γ = γ× ∘ γI : the box of assignments contained in the store d. *)
  Definition ibox (d : istore X) : powerset (Asn X) :=
    fun asn => forall x, imem (asn x) (d x).

  (* α = αI ∘ α× : the interval hull of a set of assignments. *)
  Definition ihull (P : powerset (Asn X)) : istore X :=
    fun x => alphai (fun v => exists asn, P asn /\ asn x = v).

  (* The best interval propagator I[c] = αI ∘ α× ∘ S[c] ∘ γ× ∘ γI. *)
  Definition bestI (c : constraint X) (d : istore X) : istore X :=
    ihull (csem c (ibox d)).

  (* bestI is literally the best propagator of the composite Galois
     connection P(Asn) ⇄ D ⇄ I of claims 3 and 12. *)
  Lemma bestI_is_composite_best :
    forall (c : constraint X) (d : istore X) (x : X),
      bestI c d x
      = galpha (GC_compose (GC_Cartesian X) (GC_Store X))
          (csem c (ggamma (GC_compose (GC_Cartesian X) (GC_Store X)) d)) x.
  Proof. reflexivity. Qed.

  (* Every solution inside the box lies inside the best propagation. *)
  Lemma sol_in_bestI : forall c d asn,
    csem c (ibox d) asn -> forall x, imem (asn x) (bestI c d x).
  Proof.
    intros c d asn Hs x. unfold bestI, ihull, alphai. split; cbn [fst snd].
    - apply zinfS_lb. exists (asn x). split; [|reflexivity].
      exists asn. auto.
    - apply zsup_ub. exists (asn x). split; [|reflexivity].
      exists asn. auto.
  Qed.

  (* The best propagation is contained in the input box (pointwise). *)
  Lemma bestI_ile_d : forall c d x, ile (bestI c d x) (d x).
  Proof.
    intros c d x. unfold bestI, ihull, alphai. split; cbn [fst snd].
    - apply zinfS_greatest. intros w [v [[asn [[Hbox _] Hrel]] Hv]].
      subst w v. destruct (Hbox x) as [H1 _]. exact H1.
    - apply zsup_least. intros w [v [[asn [[Hbox _] Hrel]] Hv]].
      subst w v. destruct (Hbox x) as [_ H2]. exact H2.
  Qed.

  Lemma bestI_reductive : forall c d, leI X (bestI c d) d.
  Proof. intros c d. right. intros x. right. apply bestI_ile_d. Qed.

  (* Failed best propagation means no solution in the box, and conversely. *)
  Lemma bestI_bot_no_sol : forall c d,
    isbotI X (bestI c d) -> forall asn, ~ csem c (ibox d) asn.
  Proof.
    intros c d [x Hx] asn Hs.
    exact (imem_not_isbot _ _ (sol_in_bestI c d asn Hs x) Hx).
  Qed.

  Lemma no_sol_bestI_bot : forall c d,
    (forall asn, ~ csem c (ibox d) asn) -> isbotI X (bestI c d).
  Proof.
    intros c d Hno. exists (cx c). unfold bestI, ihull.
    apply alphai_bot_of_empty. intros v [asn [Hs _]].
    exact (Hno asn Hs).
  Qed.

  (* ---------- Propagator properties over I ---------- *)

  Definition soundI (c : constraint X) (p : istore X -> istore X) : Prop :=
    forall d, leI X (bestI c d) (p d).
  Definition completeI (c : constraint X) (p : istore X -> istore X) : Prop :=
    forall d, leI X (p d) (bestI c d).
  Definition reductiveI (p : istore X -> istore X) : Prop :=
    forall d, leI X (p d) d.

  (* All interval bounds of the store are finite. *)
  Definition boundedI (d : istore X) : Prop :=
    forall x, exists a b : Z, d x = (Fin a, Fin b).

  (* The paper's definition of bounds(Z) consistency at d: unless the
     propagator failed, every bound of every variable is attained by a
     solution of c lying inside the propagated box. *)
  Definition boundsZ_consistent
    (c : constraint X) (p : istore X -> istore X) (d : istore X) : Prop :=
    ~ isbotI X (p d) ->
    forall x : X, exists lo hi : Z,
      p d x = (Fin lo, Fin hi) /\
      (exists asn, rel c asn /\ asn x = lo /\ forall y, imem (asn y) (p d y)) /\
      (exists asn, rel c asn /\ asn x = hi /\ forall y, imem (asn y) (p d y)).

  (* ======================= CLAIM 15 ======================= *)
  Theorem claim15 :
    forall (c : constraint X) (p : istore X -> istore X),
      soundI c p -> reductiveI p ->
      forall d, boundedI d ->
        (boundsZ_consistent c p d <-> eqI X (p d) (bestI c d)).
  Proof.
    intros c p Hsound Hred d Hbd. split.
    - (* bounds(Z) at d  ⟹  p d = I[c] d *)
      intros Hb.
      destruct (classic (isbotI X (p d))) as [Hbot|Hbot].
      + (* p failed: by soundness the best is failed too *)
        left. split; [exact Hbot|].
        destruct (Hsound d) as [Hb'|Hle]; [exact Hb'|].
        destruct Hbot as [x Hx]. exists x.
        exact (isle_isbot _ _ (Hle x) Hx).
      + (* p did not fail *)
        specialize (Hb Hbot).
        assert (Hnb : forall y, ~ isbot (p d y)).
        { intros y Hy. apply Hbot. exists y. exact Hy. }
        assert (Hred' : forall y, isle (p d y) (d y)).
        { destruct (Hred d) as [Hbb|Hle]; [contradiction | exact Hle]. }
        assert (Hile : forall y, ile (p d y) (d y)).
        { intros y. destruct (Hred' y) as [Hbb|Hle];
            [exfalso; exact (Hnb y Hbb) | exact Hle]. }
        (* the witnessing solutions live in the box of d *)
        assert (Hsol : forall asn, (forall y, imem (asn y) (p d y)) ->
                        rel c asn -> csem c (ibox d) asn).
        { intros asn Hin Hr. split; [|exact Hr].
          intros y. eapply imem_ile; [apply Hin | apply Hile]. }
        right. intros x.
        destruct (Hb x) as
          (lo & hi & Hpx & (alo & Hrlo & Hxlo & Hblo) & (ahi & Hrhi & Hxhi & Hbhi)).
        apply isle_antisym.
        * (* p d x ⊑ best: both bounds are values of solutions in the box *)
          right. rewrite Hpx. unfold bestI, ihull, alphai. split; cbn [fst snd].
          -- apply zinfS_lb. exists lo. split; [|reflexivity].
             exists alo. split; [apply Hsol; assumption | exact Hxlo].
          -- apply zsup_ub. exists hi. split; [|reflexivity].
             exists ahi. split; [apply Hsol; assumption | exact Hxhi].
        * (* best ⊑ p d x : soundness *)
          destruct (Hsound d) as [Hbb|Hle]; [|apply Hle].
          exfalso.
          exact (bestI_bot_no_sol c d Hbb alo (Hsol alo Hblo Hrlo)).
    - (* p d = I[c] d  ⟹  bounds(Z) at d *)
      intros Heq Hnbot x.
      assert (Hnb : forall y, ~ isbot (p d y)).
      { intros y Hy. apply Hnbot. exists y. exact Hy. }
      assert (Hpt : forall y, p d y = bestI c d y).
      { destruct Heq as [[H1 _]|H]; [contradiction|].
        intros y. destruct (H y) as [[Hb1 _]|He]; [|exact He].
        exfalso. exact (Hnb y Hb1). }
      (* finite bounds of p d x *)
      assert (Hile : ile (p d x) (d x)).
      { destruct (Hred d) as [Hbb|Hle]; [contradiction|].
        destruct (Hle x) as [Hbb|Hle']; [exfalso; exact (Hnb x Hbb) | exact Hle']. }
      destruct (Hbd x) as (a & b & Hdx).
      destruct (p d x) as [l u] eqn:Hpx.
      destruct Hile as [H1 H2]. rewrite Hdx in H1, H2. simpl in H1, H2.
      assert (Hnbx : ~ isbot (l, u)) by (rewrite <- Hpx; apply Hnb).
      unfold isbot in Hnbx. simpl in Hnbx.
      apply not_or_and in Hnbx. destruct Hnbx as [Hlu Hnbx].
      apply not_or_and in Hnbx. destruct Hnbx as [Hlp Hum].
      destruct l as [|lo|]; [destruct u; simpl in H1; contradiction | | congruence].
      destruct u as [|hi|]; [congruence | | simpl in H2; contradiction].
      exists lo, hi. split; [reflexivity|].
      (* attainment of both bounds from the hull *)
      assert (Hbx : bestI c d x = (Fin lo, Fin hi)) by (rewrite <- Hpt; exact Hpx).
      unfold bestI, ihull, alphai in Hbx.
      injection Hbx as Hinf Hsup.
      split.
      + (* lower bound *)
        destruct (zinfS_fin_inv
                    (finset (fun v => exists asn, csem c (ibox d) asn /\ asn x = v)) lo)
          as [w [Hw Hwle]].
        { rewrite Hinf. apply zle_refl. }
        destruct Hw as [v [[asn [Hs Hax]] ->]].
        assert (Hlb : zle (zinfS (finset
                 (fun v0 : Z => exists asn0, csem c (ibox d) asn0 /\ asn0 x = v0)))
                 (Fin v)).
        { apply zinfS_lb. exists v. split; [|reflexivity]. exists asn. auto. }
        rewrite Hinf in Hlb. simpl in Hlb, Hwle.
        assert (Hveq : v = lo) by lia. rewrite Hveq in Hax.
        exists asn. destruct Hs as [Hbox Hrel].
        split; [exact Hrel|]. split; [exact Hax|].
        intros y. rewrite Hpt. apply sol_in_bestI. split; assumption.
      + (* upper bound *)
        destruct (fin_le_zsup_inv
                    (finset (fun v => exists asn, csem c (ibox d) asn /\ asn x = v)) hi)
          as [w [Hw Hwle]].
        { rewrite Hsup. apply zle_refl. }
        destruct Hw as [v [[asn [Hs Hax]] ->]].
        assert (Hub : zle (Fin v)
                 (zsup (finset
                    (fun v0 : Z => exists asn0, csem c (ibox d) asn0 /\ asn0 x = v0)))).
        { apply zsup_ub. exists v. split; [|reflexivity]. exists asn. auto. }
        rewrite Hsup in Hub. simpl in Hub, Hwle.
        assert (Hveq : v = hi) by lia. rewrite Hveq in Hax.
        exists asn. destruct Hs as [Hbox Hrel].
        split; [exact Hrel|]. split; [exact Hax|].
        intros y. rewrite Hpt. apply sol_in_bestI. split; assumption.
  Qed.

End BestInterval.
