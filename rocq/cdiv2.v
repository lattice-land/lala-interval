(** * cdiv2: the ceiling-division propagator, by reduction to floor division

    The C++ implements the ceiling propagator through the identity
        ceil(y/z) = -floor(-y/z)
    ([cdiv_num]/[cdiv_den] in zinterval.hpp delegate to the fdiv versions on
    negated intervals).  We verify exactly that reduction: the ceiling
    propagator is (negate x,y) o floor-propagator o (negate x,y), and ALL the
    properties proved for [fdiv2.propagator] transfer through the bijection:
      - soundness              : [cdiv_soundness]
      - reductivity            : [cdiv_reductive]
      - optimality             : [cdiv_best]
      - monotonicity           : [cdiv_monotone]
      - idempotence            : [cdiv_idempotence]
      - completeness/singleton : [cdiv_singleton_complete] *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv2.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Ceiling solutions and the negation equivalence                  *)
(* ------------------------------------------------------------------ *)

Definition csol (x y z : Z) : Prop := z <> 0 /\ x = cdiv y z.

(* the code-level equivalence with floor division *)
Lemma csol_sol : forall x y z, csol x y z <-> sol (-x) (-y) z.
Proof.
  unfold csol, sol, cdiv. intros x y z.
  split; intros [Hz He]; split; auto; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Negation of the x and y components                              *)
(* ------------------------------------------------------------------ *)

Definition negi (i : itv) : itv := Itv (- hi i) (- lo i).
Definition negs (s : store) : store := St (negi (sx s)) (negi (sy s)) (sz s).

Definition cpropagator (s : store) : store := negs (propagator (negs s)).

Lemma negi_invol : forall i, negi (negi i) = i.
Proof. intros [l u]; unfold negi; cbn; f_equal; lia. Qed.

Lemma negs_invol : forall s, negs (negs s) = s.
Proof.
  intros [ix iy iz]; unfold negs; cbn [sx sy sz]; rewrite !negi_invol; reflexivity.
Qed.

Lemma mem_negi : forall i v, mem (negi i) v <-> mem i (- v).
Proof. intros [l u] v; unfold mem, negi; cbn; lia. Qed.

Lemma in_store_negs : forall s vx vy vz,
  in_store (negs s) vx vy vz <-> in_store s (- vx) (- vy) vz.
Proof.
  intros s vx vy vz; unfold in_store, negs; cbn [sx sy sz].
  rewrite !mem_negi. tauto.
Qed.

Lemma ile_negi : forall i j, ile (negi i) (negi j) <-> ile i j.
Proof. intros [li ui] [lj uj]; unfold ile, negi; cbn; lia. Qed.

Lemma sle_negs : forall a b, sle (negs a) (negs b) <-> sle a b.
Proof.
  intros a b; unfold sle, negs; cbn [sx sy sz].
  rewrite !ile_negi. tauto.
Qed.

(* ceiling-side notions, mirrored through the bijection *)
Definition contains_csols (s t : store) : Prop :=
  forall vx vy vz, in_store s vx vy vz -> csol vx vy vz -> in_store t vx vy vz.
Definition cfeasible (s : store) : Prop :=
  exists vx vy vz, in_store s vx vy vz /\ csol vx vy vz.

Lemma cfeasible_feasible : forall s, cfeasible s <-> feasible (negs s).
Proof.
  intro s; split.
  - intros (vx & vy & vz & Hin & Hc).
    exists (- vx), (- vy), vz. split.
    + apply in_store_negs. rewrite !Z.opp_involutive. exact Hin.
    + apply csol_sol. exact Hc.
  - intros (vx & vy & vz & Hin & Hs).
    exists (- vx), (- vy), vz. split.
    + apply in_store_negs in Hin. exact Hin.
    + apply csol_sol. rewrite !Z.opp_involutive. unfold csol, sol, cdiv in *.
      destruct Hs; split; auto; lia.
Qed.

Lemma contains_csols_sols : forall s t,
  contains_csols s t <-> contains_sols (negs s) (negs t).
Proof.
  intros s t; split.
  - intros H vx vy vz Hin Hs.
    apply in_store_negs in Hin.
    apply in_store_negs.
    apply H; [exact Hin|].
    apply csol_sol. rewrite !Z.opp_involutive. exact Hs.
  - intros H vx vy vz Hin Hc.
    assert (Hin' : in_store (negs s) (- vx) (- vy) vz).
    { apply in_store_negs. rewrite !Z.opp_involutive. exact Hin. }
    apply csol_sol in Hc.
    pose proof (H _ _ _ Hin' Hc) as Ht.
    apply in_store_negs in Ht.
    rewrite negs_invol in Ht. exact Ht.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The transferred properties                                      *)
(* ------------------------------------------------------------------ *)

Theorem cdiv_soundness : forall s vx vy vz,
  in_store s vx vy vz -> csol vx vy vz ->
  in_store (cpropagator s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hc.
  unfold cpropagator.
  assert (Hin' : in_store (negs s) (- vx) (- vy) vz).
  { apply in_store_negs. rewrite !Z.opp_involutive. exact Hin. }
  apply csol_sol in Hc.
  pose proof (fdiv_soundness _ _ _ _ Hin' Hc) as Hp.
  apply in_store_negs in Hp. exact Hp.
Qed.

Theorem cdiv_reductive : forall s, sle (cpropagator s) s.
Proof.
  intro s. unfold cpropagator.
  rewrite <- (negs_invol s) at 2.
  apply sle_negs. apply fdiv_reductive.
Qed.

Theorem cdiv_best : forall s,
  cfeasible s -> forall t, contains_csols s t -> sle (cpropagator s) t.
Proof.
  intros s Hf t Hc.
  unfold cpropagator.
  rewrite <- (negs_invol t).
  apply sle_negs.
  apply fdiv_best.
  - apply cfeasible_feasible. exact Hf.
  - apply contains_csols_sols. exact Hc.
Qed.

Theorem cdiv_monotone : forall s t,
  cfeasible s -> sle s t -> sle (cpropagator s) (cpropagator t).
Proof.
  intros s t Hf Hle.
  unfold cpropagator. apply sle_negs.
  apply fdiv_monotone.
  - apply cfeasible_feasible. exact Hf.
  - apply sle_negs. exact Hle.
Qed.

Theorem cdiv_idempotence : forall s,
  cfeasible s -> cpropagator (cpropagator s) = cpropagator s.
Proof.
  intros s Hf.
  unfold cpropagator.
  rewrite negs_invol.
  rewrite (fdiv_idempotence (negs s)); [reflexivity|].
  apply cfeasible_feasible. exact Hf.
Qed.

(* non-emptiness commutes with the negation *)
Lemma ne_negs : forall s, ne_store (negs s) = ne_store s.
Proof.
  intros [[lx ux] [ly uy] [lz uz]]; unfold ne_store, negs, negi, nonemptyb; cbn.
  destruct (- ux <=? - lx) eqn:E1; destruct (lx <=? ux) eqn:E2;
  destruct (- uy <=? - ly) eqn:E3; destruct (ly <=? uy) eqn:E4; cbn;
  try reflexivity;
  try (apply Z.leb_le in E1 || apply Z.leb_gt in E1);
  try (apply Z.leb_le in E2 || apply Z.leb_gt in E2);
  try (apply Z.leb_le in E3 || apply Z.leb_gt in E3);
  try (apply Z.leb_le in E4 || apply Z.leb_gt in E4);
  lia.
Qed.

Theorem cdiv_singleton_complete : forall s vx vy vz,
  sx s = Itv vx vx -> sy s = Itv vy vy -> sz s = Itv vz vz ->
  ne_store (cpropagator s) = true ->
  csol vx vy vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold cpropagator in Hne. rewrite ne_negs in Hne.
  assert (Hs : sol (- vx) (- vy) vz).
  { apply (fdiv_singleton_complete (negs s) (- vx) (- vy) vz); auto.
    - unfold negs; cbn. rewrite Hx. unfold negi; cbn. reflexivity.
    - unfold negs; cbn. rewrite Hy. unfold negi; cbn. reflexivity. }
  apply csol_sol. exact Hs.
Qed.
