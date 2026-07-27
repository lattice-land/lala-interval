(* ========================================================================= *)
(* Claim 7:                                                                  *)
(* "As long as the propagators are executed fairly, their greatest mutual   *)
(*  fixpoint is the same for every order of execution."                      *)
(*                                                                           *)
(* Setting: a complete lattice A, a family (f_i)_{i∈Idx} of monotone and     *)
(* reductive propagators, and a starting point d.  An execution order is a   *)
(* sequence s : nat → Idx; the corresponding chaotic iteration is            *)
(*    x_0 = d,   x_{n+1} = f_{s(n)}(x_n).                                    *)
(* The sequence is fair when every propagator index occurs infinitely often. *)
(*                                                                           *)
(* We prove: whenever a fair iteration stabilizes (the descending chain      *)
(* becomes constant, e.g. after termination of propagation), its limit is    *)
(* the greatest common fixpoint of all the f_i below d — independently of    *)
(* the order of execution.  In particular any two fair stabilizing           *)
(* executions have equal (oeq) limits.                                       *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia List PeanoNat.
From Paper Require Import claim1 claim2 claim3 claim5.

Section FairIteration.
  Context (L : CompleteLattice).
  Notation A := (cl_os L).
  Context (Idx : Type) (fs : Idx -> oc A -> oc A).
  Hypothesis fs_mono : forall i, monotoneO A (fs i).
  Hypothesis fs_red : forall i, reductiveO A (fs i).
  Context (d : oc A).

  (* Monotone functions respect the setoid equality. *)
  Lemma fs_proper : forall i x y, oeq x y -> oeq (fs i x) (fs i y).
  Proof.
    intros i x y He. apply ole_antisym; apply fs_mono, ole_refl;
      [exact He | apply oeq_sym, He].
  Qed.

  (* Common post-fixpoints below d, and the greatest mutual fixpoint ν. *)
  Definition postfix (y : oc A) : Prop :=
    ole y d /\ forall i, ole y (fs i y).

  Definition nu : oc A := csup postfix.

  Lemma nu_le_d : ole nu d.
  Proof. apply csup_least. intros y [Hy _]. exact Hy. Qed.

  Lemma nu_post : forall i, ole nu (fs i nu).
  Proof.
    intros i. apply csup_least. intros y [Hyd Hyf].
    eapply ole_trans; [apply Hyf|]. apply fs_mono. apply csup_ub. split; assumption.
  Qed.

  (* ν is a common fixpoint of all the propagators. *)
  Lemma nu_fix : forall i, oeq (fs i nu) nu.
  Proof.
    intros i. apply ole_antisym; [apply fs_red | apply nu_post].
  Qed.

  (* ν is the greatest common fixpoint below d. *)
  Lemma nu_greatest : forall y,
    ole y d -> (forall i, oeq (fs i y) y) -> ole y nu.
  Proof.
    intros y Hyd Hfix. apply csup_ub. split; [exact Hyd|].
    intros i. apply ole_refl, oeq_sym, Hfix.
  Qed.

  (* Chaotic iteration along an execution order s. *)
  Fixpoint iter (s : nat -> Idx) (n : nat) : oc A :=
    match n with
    | O => d
    | S m => fs (s m) (iter s m)
    end.

  Definition fair (s : nat -> Idx) : Prop :=
    forall i N, exists n, (N <= n)%nat /\ s n = i.

  Lemma iter_le_d : forall s n, ole (iter s n) d.
  Proof.
    intros s n. induction n as [|m IH]; simpl.
    - apply ole_refl'.
    - eapply ole_trans; [apply fs_red | exact IH].
  Qed.

  Lemma iter_above_nu : forall s n, ole nu (iter s n).
  Proof.
    intros s n. induction n as [|m IH]; simpl.
    - apply nu_le_d.
    - eapply ole_trans; [apply nu_post | apply fs_mono, IH].
  Qed.

  (* Any fair iteration that stabilizes, stabilizes exactly at ν. *)
  Theorem fair_iteration_limit :
    forall (s : nat -> Idx) (N : nat),
      fair s ->
      (forall m, (N <= m)%nat -> oeq (iter s m) (iter s N)) ->
      oeq (iter s N) nu.
  Proof.
    intros s N Hfair Hstab.
    apply ole_antisym.
    - (* iter s N ≤ ν: iter s N is a common fixpoint below d *)
      apply nu_greatest; [apply iter_le_d|].
      intros i.
      destruct (Hfair i N) as [n [Hn Hsn]].
      (* f_i (iter N) ≡ f_i (iter n) = iter (n+1) ≡ iter N *)
      eapply oeq_trans.
      + apply fs_proper. apply oeq_sym, Hstab, Hn.
      + rewrite <- Hsn.
        change (fs (s n) (iter s n)) with (iter s (S n)).
        apply Hstab. lia.
    - apply iter_above_nu.
  Qed.

  (* ======================= CLAIM 7 ======================= *)
  (* Order independence: any two fair stabilizing executions reach the same
     greatest mutual fixpoint. *)
  Theorem claim7 :
    forall (s s' : nat -> Idx) (N N' : nat),
      fair s -> fair s' ->
      (forall m, (N <= m)%nat -> oeq (iter s m) (iter s N)) ->
      (forall m, (N' <= m)%nat -> oeq (iter s' m) (iter s' N')) ->
      oeq (iter s N) (iter s' N').
  Proof.
    intros s s' N N' Hf Hf' Hs Hs'.
    eapply oeq_trans.
    - apply (fair_iteration_limit s N Hf Hs).
    - apply oeq_sym, (fair_iteration_limit s' N' Hf' Hs').
  Qed.

End FairIteration.
