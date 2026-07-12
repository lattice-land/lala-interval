From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Definition ileD (i j : itv) : Prop := lo j <= lo i /\ hi i <= hi j.
Definition CxD (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).

(* A witness solution attaining a NEGATIVE quotient z0 with x-value x0. *)
Lemma attain_neg : forall (ix iy : itv) z0 x0,
  z0 < 0 ->
  lo ix <= x0 <= hi ix ->
  lo iy <= hi iy ->
  lo iy <= z0 * x0 ->
  z0 * (x0 + 1) + 1 <= hi iy ->
  exists x y, mem ix x /\ mem iy y /\ sol x y z0.
Proof.
  intros ix iy z0 x0 Hz0 Hxin Hne Hub Hlb.
  exists x0, (Z.min (hi iy) (z0 * x0)).
  unfold mem, sol.
  split; [exact Hxin|].
  split.
  - split.
    + apply Z.min_glb; lia.
    + apply Z.le_min_l.
  - split; [lia|].
    destruct (Z.min_spec (hi iy) (z0 * x0)) as [[Hlt E]|[Hge E]]; rewrite E.
    + (* y = hi iy, and hi iy < z0*x0 *)
      assert (x0 <= hi iy / z0) by (apply fdiv_lb_neg; [lia|lia]).
      assert (hi iy / z0 < x0 + 1) by (apply fdiv_lt_neg; [lia|lia]).
      lia.
    + (* y = z0*x0 *)
      rewrite Z.mul_comm. rewrite Z.div_mul; [reflexivity|lia].
Qed.

(* The trivial witness x=0,y=0 attains any nonzero z0 when 0 is in both boxes. *)
Lemma attain_zero : forall (ix iy : itv) z0,
  z0 <> 0 -> lo ix <= 0 <= hi ix -> lo iy <= 0 <= hi iy ->
  exists x y, mem ix x /\ mem iy y /\ sol x y z0.
Proof.
  intros ix iy z0 Hz0 Hx Hy. exists 0, 0. unfold mem, sol.
  rewrite Z.div_0_l by lia. repeat split; lia.
Qed.

(* Clamped witness: z0 achievable as soon as [a,b] overlaps the achievable
   x-window [d/z0, c/z0] at divisor z0 (for z0 < 0). *)
Lemma attain_neg2 : forall (ix iy : itv) z0,
  z0 < 0 -> lo ix <= hi ix -> lo iy <= hi iy ->
  lo ix <= Z.div (lo iy) z0 ->
  Z.div (hi iy) z0 <= hi ix ->
  exists x y, mem ix x /\ mem iy y /\ sol x y z0.
Proof.
  intros ix iy z0 Hz Hix Hiy HA HB.
  set (c := lo iy) in *. set (d := hi iy) in *.
  assert (Hcd_div : Z.div d z0 <= Z.div c z0) by (apply div_le_mono_num_neg; lia).
  pose proof (div_bracket_neg c z0 Hz) as [Bc1 Bc2].
  pose proof (div_bracket_neg d z0 Hz) as [Bd1 Bd2].
  apply (attain_neg ix iy z0 (Z.max (lo ix) (Z.div d z0))).
  - exact Hz.
  - split; [apply Z.le_max_l| apply Z.max_lub; [exact Hix|exact HB]].
  - exact Hiy.
  - assert (Hx0c : Z.max (lo ix) (Z.div d z0) <= Z.div c z0)
      by (apply Z.max_lub; [exact HA| exact Hcd_div]).
    nia.
  - assert (Hx0d : Z.div d z0 <= Z.max (lo ix) (Z.div d z0)) by apply Z.le_max_r.
    nia.
Qed.

(* Multiplicative form of the two overlap conditions. *)
Lemma attain_neg3 : forall (ix iy : itv) z0,
  z0 < 0 -> lo ix <= hi ix -> lo iy <= hi iy ->
  lo iy <= z0 * lo ix ->
  z0 * (hi ix + 1) < hi iy ->
  exists x y, mem ix x /\ mem iy y /\ sol x y z0.
Proof.
  intros ix iy z0 Hz Hix Hiy HA HB.
  apply attain_neg2; try assumption.
  - apply fdiv_lb_neg; [lia| exact HA].
  - assert (hi iy / z0 < hi ix + 1) by (apply fdiv_lt_neg; [lia| exact HB]). lia.
Qed.

Lemma fden_opt_neg : forall ix iy iz,
  hi iz < 0 ->
  lo ix <= hi ix ->
  lo iy <= hi iy ->
  ileD ix (CxD iy iz) ->
  lo (fden ix iy iz) <= hi (fden ix iy iz) ->
  (exists x y, mem ix x /\ mem iy y /\ sol x y (lo (fden ix iy iz)))
  /\ (exists x y, mem ix x /\ mem iy y /\ sol x y (hi (fden ix iy iz))).
Proof.
Admitted.
