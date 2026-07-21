(** * zmod.v : soundness of the truncated-modulus propagator [ztmod].

    Truncated modulus [x = y % z] (C99 `%`, round-toward-zero) is [Z.rem].
    The propagator narrows the store with the modulus-specific bounds
      - z <> 0
      - sign(x) = sign(y),  |x| <= |y|,  |x| <= |z| - 1
    and (in the C++ implementation) additionally ternarizes against truncated
    division via the identity  y = (y quot z) * z + x  to reuse the already
    verified division / product / sum contractors.  Here we prove the direct
    narrowing SOUND (never drops a modulus solution) and record the
    ternarization identity that justifies the composed part. *)

From Stdlib Require Import ZArith Lia.
From LalaInterval Require Import Zinf itv zadd zmul.
Open Scope Z_scope.

(* truncated-modulus solution relation: x = y rem z with z <> 0. *)
Definition tmsol (vx vy vz : Z) : Prop := vz <> 0 /\ vx = Z.rem vy vz.

(* ------------------------------------------------------------------ *)
(** ** Arithmetic core: sign and magnitude of the truncated remainder  *)
(* ------------------------------------------------------------------ *)

(* |x| <= |y| in the same-sign directions (with sign from [Z.rem_nonneg]/
   [Z.rem_nonpos] and magnitude from [Z.rem_bound_abs]). *)
Lemma rem_le_dividend : forall vy vz, vz <> 0 -> 0 <= vy -> Z.rem vy vz <= vy.
Proof.
  intros vy vz Hz Hy.
  pose proof (Z.rem_bound_abs vy vz Hz) as Hb.
  pose proof (Z.rem_nonneg vy vz Hz Hy) as Hn.
  assert (Z.abs (Z.rem vy vz) = Z.rem vy vz) by (apply Z.abs_eq; exact Hn).
  destruct (Z.lt_ge_cases (Z.abs vy) (Z.abs vz)) as [Hlt|Hge].
  - rewrite (proj2 (Z.rem_small_iff vy vz Hz) Hlt). lia.
  - assert (Z.abs vy = vy) by (apply Z.abs_eq; exact Hy). lia.
Qed.

Lemma rem_ge_dividend : forall vy vz, vz <> 0 -> vy <= 0 -> vy <= Z.rem vy vz.
Proof.
  intros vy vz Hz Hy.
  pose proof (Z.rem_bound_abs vy vz Hz) as Hb.
  pose proof (Z.rem_nonpos vy vz Hz Hy) as Hn.
  assert (Z.abs (Z.rem vy vz) = - Z.rem vy vz) by (apply Z.abs_neq; exact Hn).
  destruct (Z.lt_ge_cases (Z.abs vy) (Z.abs vz)) as [Hlt|Hge].
  - rewrite (proj2 (Z.rem_small_iff vy vz Hz) Hlt). lia.
  - assert (Z.abs vy = - vy) by (apply Z.abs_neq; exact Hy). lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The remainder envelope on the interval domain                    *)
(* ------------------------------------------------------------------ *)

(* Upper bound on |v| for any v in an interval, over Zinf (infinity-aware). *)
Definition zabs_ub (i : itv) : Zinf := max_zinf (isneg_zinf3 (lb i)) (ub i).

Lemma zabs_ub_sound : forall i v, mem3 i v -> leq_zinf (Fin (Z.abs v)) (zabs_ub i).
Proof.
  intros i v [Hlo Hhi]. unfold zabs_ub.
  assert (E : Fin (Z.abs v) = max_zinf (isneg_zinf3 (Fin v)) (Fin v)) by (cbn; f_equal; lia).
  rewrite E. apply max_zinf_mono; [ apply isneg_zinf3_anti; exact Hlo | exact Hhi ].
Qed.

(* The remainder envelope for [x] given [y] and [z]:
     lower = max( min(lo y, 0),  -(|z|_max - 1) )     upper = min( max(hi y, 0),  |z|_max - 1 )
   combining the sign bound (x has y's sign, |x| <= |y|) with the magnitude
   bound (|x| <= |z| - 1). *)
Definition tmod_env (sy sz : itv) : itv :=
  Itv (max_zinf (min_zinf (lb sy) (Fin 0)) (iadd3 (isneg_zinf3 (zabs_ub sz)) (Fin 1)))
       (min_zinf (max_zinf (ub sy) (Fin 0)) (isub3 (zabs_ub sz) (Fin 1))).

Lemma mem3_tmod_env : forall sy sz vy vz,
  vz <> 0 -> mem3 sy vy -> mem3 sz vz -> mem3 (tmod_env sy sz) (Z.rem vy vz).
Proof.
  intros sy sz vy vz Hz [Hylo Hyhi] Hsz.
  pose proof (zabs_ub_sound sz vz Hsz) as Hzabs.
  pose proof (Z.rem_bound_abs vy vz Hz) as Hra.
  assert (Hmagu : leq_zinf (Fin (Z.rem vy vz)) (isub3 (zabs_ub sz) (Fin 1))).
  { apply (leq_zinf_trans _ (Fin (Z.abs vz - 1))).
    - cbn; lia.
    - assert (E : Fin (Z.abs vz - 1) = isub3 (Fin (Z.abs vz)) (Fin 1)) by (cbn; f_equal; lia).
      rewrite E. apply isub3_mono; [ exact Hzabs | apply leq_zinf_refl ]. }
  assert (Hmagl : leq_zinf (iadd3 (isneg_zinf3 (zabs_ub sz)) (Fin 1)) (Fin (Z.rem vy vz))).
  { apply (leq_zinf_trans _ (Fin (- Z.abs vz + 1))).
    - assert (E : Fin (- Z.abs vz + 1) = iadd3 (isneg_zinf3 (Fin (Z.abs vz))) (Fin 1)) by (cbn; f_equal; lia).
      rewrite E. apply iadd3_mono; [ apply isneg_zinf3_anti; exact Hzabs | apply leq_zinf_refl ].
    - cbn; lia. }
  split.
  - unfold tmod_env; cbn [lb]. apply max_zinf_lub; [ | exact Hmagl ].
    destruct (Z.le_gt_cases vy 0) as [Hy|Hy].
    + apply (leq_zinf_trans _ (lb sy)); [ apply leq_zinf_min_zinf_l | ].
      apply (leq_zinf_trans _ (Fin vy)); [ exact Hylo | ].
      cbn. pose proof (rem_ge_dividend vy vz Hz Hy). lia.
    + apply (leq_zinf_trans _ (Fin 0)); [ apply min_zinf_leq_zinf_r | ].
      cbn. pose proof (Z.rem_nonneg vy vz Hz ltac:(lia)). lia.
  - unfold tmod_env; cbn [ub]. apply leq_zinf_min_zinf_glb; [ | exact Hmagu ].
    destruct (Z.le_gt_cases 0 vy) as [Hy|Hy].
    + apply (leq_zinf_trans _ (ub sy)); [ | apply leq_zinf_max_zinf_l ].
      apply (leq_zinf_trans _ (Fin vy)); [ | exact Hyhi ].
      cbn. pose proof (rem_le_dividend vy vz Hz Hy). lia.
    + apply (leq_zinf_trans _ (Fin 0)); [ | apply leq_zinf_max_zinf_r ].
      cbn. pose proof (Z.rem_nonpos vy vz Hz ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The propagator and its soundness                                 *)
(* ------------------------------------------------------------------ *)

(* Direct modulus narrowing: clip x to the remainder envelope and force z <> 0
   (via [neqz3], shaving a 0-bound). y is untouched by the direct step. *)
Definition ztmod (s : store3) : store3 :=
  St3 (inter3 (sx3 s) (tmod_env (sy3 s) (sz3 s))) (sy3 s) (neqz3 (sz3 s)).

Theorem ztmod_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> tmsol vx vy vz -> in_store3 (ztmod s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) [Hnz Heq]. subst vx.
  unfold ztmod, in_store3; cbn [sx3 sy3 sz3].
  split; [ | split ].
  - apply mem3_inter; [ exact Hx | apply mem3_tmod_env; assumption ].
  - exact Hy.
  - apply neqz3_sound; [ exact Hz | exact Hnz ].
Qed.

(* The identity behind the C++ ternarization: introducing q = tdiv(y,z),
   x = y rem z is equivalent to  y = q*z + x.  This is why composing the
   already-verified division / product / sum contractors is sound. *)
Lemma tmsol_ternary : forall vx vy vz, vz <> 0 ->
  (vx = Z.rem vy vz <-> vy = Z.quot vy vz * vz + vx).
Proof.
  intros vx vy vz Hz. pose proof (Z.quot_rem vy vz Hz) as Hqr.
  split; intro H; nia.
Qed.
