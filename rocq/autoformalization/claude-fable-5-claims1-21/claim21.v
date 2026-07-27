(* ========================================================================= *)
(* Claim 21:                                                                 *)
(* The simplified truncated-division propagator (appendix figure             *)
(* "simplified-tdiv") is the best interval propagator of x = tdiv(y,z).      *)
(*                                                                           *)
(*   I[x = tdiv⁺(y,z)]: the core propagator enforcing x = tdiv(y,z) ∧ z ≥ 1  *)
(*     tden⁺([xl,xu],[yl,yu]) refines z starting from [1,∞]:                 *)
(*       if xl > 0 then z ← [−∞, ⌊yu/xl⌋] else z ← [⌈(yu−1)/(xl−1)⌉, ∞]      *)
(*       if xu > −1 then z ← [⌈(yl+1)/(xu+1)⌉, ∞] else z ← [−∞, ⌊yl/xu⌋]     *)
(*     tnum⁺([xl,xu],[zl,zu]) refines y by the corner hull of the truncation *)
(*       windows, tdiv⁺fwd([yl,yu],[zl,zu]) refines x by the corner hull of  *)
(*       the truncated division.                                             *)
(*   I[x = tdiv(y,z)] = I[x = tdiv⁺(y,z)] ⊔̈ (zneg_xz ∘ I[x=tdiv⁺] ∘ zneg_xz) *)
(*                                                                           *)
(* The whole development rests on the window characterization of truncated   *)
(* division by a positive divisor:                                           *)
(*   for z ≥ 1,  x = tdiv(y,z)  ⟺  WloZ x z ≤ y ≤ WhiZ x z                  *)
(* where WloZ x z = if x > 0 then x·z else (x−1)·z+1 and                     *)
(*       WhiZ x z = if x < 0 then x·z else (x+1)·z−1,                        *)
(* and windows of consecutive x are adjacent: WhiZ x z + 1 = WloZ (x+1) z.   *)
(* The proof mirrors the fdiv⁺ development of claim 20 step by step.         *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical FunctionalExtensionality
  PropExtensionality.
From Paper Require Import claim1 claim2 claim3 claim4 claim8 claim9 claim10
  claim11 claim12 claim15 claim16 claim20.
Open Scope Z_scope.

(* ==================== Small Z∞ helpers ==================== *)

Lemma zle_fin : forall a b : Z, a <= b -> zle (Fin a) (Fin b).
Proof. intros a b H. exact H. Qed.

Lemma zcdiv_fin : forall a b : Z, zcdiv (Fin a) (Fin b) = Fin (cdivZ a b).
Proof. reflexivity. Qed.

Lemma zltb_0_fin : forall a : Z, zltb (Fin 0) (Fin a) = (0 <? a).
Proof. intros a. unfold zltb. simpl. rewrite Z.ltb_antisym. reflexivity. Qed.

Lemma zltb_fin_0 : forall b : Z, zltb (Fin b) (Fin 0) = (b <? 0).
Proof. intros b. unfold zltb. simpl. rewrite Z.ltb_antisym. reflexivity. Qed.

Lemma zadd1_mono2 : forall a b, zle a b -> zle (zadd a (Fin 1)) (zadd b (Fin 1)).
Proof. intros [|x|] [|y|] H; simpl in *; try tauto; lia. Qed.

Lemma zmin_zadd1_le : forall A B,
  zle (zmin (zadd A (Fin 1)) (zadd B (Fin 1))) (zadd (zmin A B) (Fin 1)).
Proof.
  intros A B. destruct (zmin_case A B) as [[E _]|[E _]]; rewrite E.
  - apply zmin_le_l.
  - apply zmin_le_r.
Qed.

(* ==================== The truncation window on Z ==================== *)

Definition WloZ (x z : Z) : Z := if 0 <? x then x * z else (x - 1) * z + 1.
Definition WhiZ (x z : Z) : Z := if x <? 0 then x * z else (x + 1) * z - 1.

Ltac zbool :=
  repeat match goal with
         | E : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in E
         | E : (_ <? _)%Z = false |- _ => apply Z.ltb_ge in E
         end.

Lemma WloZ_le_WhiZ : forall x z, 1 <= z -> WloZ x z <= WhiZ x z.
Proof.
  intros x z Hz. unfold WloZ, WhiZ.
  destruct (0 <? x) eqn:E1; destruct (x <? 0) eqn:E2; zbool; nia.
Qed.

Lemma WloZ_mono_x : forall x x' z, 1 <= z -> x <= x' -> WloZ x z <= WloZ x' z.
Proof.
  intros x x' z Hz Hx. unfold WloZ.
  destruct (0 <? x) eqn:E1; destruct (0 <? x') eqn:E2; zbool; nia.
Qed.

Lemma WhiZ_mono_x : forall x x' z, 1 <= z -> x <= x' -> WhiZ x z <= WhiZ x' z.
Proof.
  intros x x' z Hz Hx. unfold WhiZ.
  destruct (x <? 0) eqn:E1; destruct (x' <? 0) eqn:E2; zbool; nia.
Qed.

(* Adjacency of consecutive windows. *)
Lemma WhiZ_adj : forall x z, WhiZ x z + 1 = WloZ (x + 1) z.
Proof.
  intros x z. unfold WhiZ, WloZ.
  destruct (x <? 0) eqn:E1; destruct (0 <? x + 1) eqn:E2; zbool; nia.
Qed.

(* The window characterization of truncated division. *)
Lemma tdivZ_win_refl : forall y z, 1 <= z ->
  WloZ (tdivZ y z) z <= y <= WhiZ (tdivZ y z) z.
Proof.
  intros y z Hz.
  destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
  - rewrite tdiv_q1 by lia.
    pose proof (fdivZ_char_refl y z Hz) as [G1 G2].
    assert (Hq : 0 <= fdivZ y z) by (apply fdivZ_lb; lia).
    unfold WloZ, WhiZ.
    destruct (0 <? fdivZ y z) eqn:E1; destruct (fdivZ y z <? 0) eqn:E2;
      zbool; split; nia.
  - rewrite tdiv_q3 by lia.
    assert (G1 : y <= z * cdivZ y z)
      by (apply (proj1 (cdivZ_le y z (cdivZ y z) Hz)); lia).
    assert (G2 : z * cdivZ y z <= y + z - 1)
      by (apply (proj1 (cdivZ_ge y z (cdivZ y z) Hz)); lia).
    assert (Hq : cdivZ y z <= 0) by (apply cdivZ_le; lia).
    unfold WloZ, WhiZ.
    destruct (0 <? cdivZ y z) eqn:E1; destruct (cdivZ y z <? 0) eqn:E2;
      zbool; split; nia.
Qed.

Lemma tdivZ_win_le : forall y z M, 1 <= z -> (tdivZ y z <= M <-> y <= WhiZ M z).
Proof.
  intros y z M Hz. split.
  - intros H.
    pose proof (tdivZ_win_refl y z Hz) as [_ G2].
    pose proof (WhiZ_mono_x (tdivZ y z) M z Hz H). lia.
  - intros H.
    destruct (Z_le_gt_dec (tdivZ y z) M) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    pose proof (tdivZ_win_refl y z Hz) as [G1 _].
    pose proof (WhiZ_adj M z) as Ha.
    pose proof (WloZ_mono_x (M + 1) (tdivZ y z) z Hz ltac:(lia)). lia.
Qed.

Lemma tdivZ_win_ge : forall y z M, 1 <= z -> (M <= tdivZ y z <-> WloZ M z <= y).
Proof.
  intros y z M Hz. split.
  - intros H.
    pose proof (tdivZ_win_refl y z Hz) as [G1 _].
    pose proof (WloZ_mono_x M (tdivZ y z) z Hz H). lia.
  - intros H.
    destruct (Z_le_gt_dec M (tdivZ y z)) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    pose proof (tdivZ_win_refl y z Hz) as [_ G2].
    pose proof (WhiZ_adj (tdivZ y z) z) as Ha.
    pose proof (WloZ_mono_x (tdivZ y z + 1) M z Hz ltac:(lia)). lia.
Qed.

(* Monotonicity of truncated division in the numerator. *)
Lemma tdivZ_mono_num : forall y y' z, 1 <= z -> y <= y' -> tdivZ y z <= tdivZ y' z.
Proof.
  intros y y' z Hz Hy.
  apply tdivZ_win_le; [exact Hz|].
  pose proof (tdivZ_win_refl y' z Hz) as [_ G2]. lia.
Qed.

(* Sign of the quotient, and monotonicity in the divisor. *)
Lemma tdivZ_nonneg : forall y z, 0 <= y -> 1 <= z -> 0 <= tdivZ y z.
Proof. intros y z Hy Hz. rewrite tdiv_q1 by lia. apply fdivZ_lb; lia. Qed.

Lemma tdivZ_nonpos : forall y z, y <= 0 -> 1 <= z -> tdivZ y z <= 0.
Proof. intros y z Hy Hz. rewrite tdiv_q3 by lia. apply cdivZ_le; lia. Qed.

Lemma tdivZ_antitone_div : forall y u v,
  0 <= y -> 0 < u <= v -> tdivZ y v <= tdivZ y u.
Proof.
  intros y u v Hy Huv.
  rewrite (tdiv_q1 y u), (tdiv_q1 y v) by lia.
  apply fdivZ_antitone_div; lia.
Qed.

Lemma tdivZ_monotone_div : forall y u v,
  y <= 0 -> 0 < u <= v -> tdivZ y u <= tdivZ y v.
Proof.
  intros y u v Hy Huv.
  rewrite (tdiv_q3 y u), (tdiv_q3 y v) by lia.
  rewrite !cdivZ_as_fdiv.
  pose proof (fdivZ_antitone_div (- y) u v ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma tdivZ_zero_num : forall z, z <> 0 -> tdivZ 0 z = 0.
Proof.
  intros z Hz. unfold tdivZ, fdivZ, cdivZ.
  rewrite Z.opp_0.
  destruct (0 <=? 0 * z); rewrite Z.div_0_l by lia; lia.
Qed.

(* Truncated division is odd in the divisor. *)
Lemma tdivZ_opp_den : forall y z, z <> 0 -> tdivZ y (- z) = - tdivZ y z.
Proof.
  intros y z Hz.
  destruct (Z.eq_dec y 0) as [->|Hy].
  - rewrite !tdivZ_zero_num by lia. reflexivity.
  - unfold tdivZ.
    destruct (Z.leb_spec 0 (y * z)) as [H1|H1];
      destruct (Z.leb_spec 0 (y * - z)) as [H2|H2]; try nia.
    + (* y·z > 0, so y·(−z) < 0: cdiv on the left, fdiv on the right *)
      rewrite (cdivZ_opp y (- z)) by lia.
      rewrite Z.opp_involutive. reflexivity.
    + (* y·z < 0: fdiv on the left, cdiv on the right *)
      rewrite (cdivZ_opp y z) by lia. lia.
Qed.

(* ==================== The truncation window on Z∞ ==================== *)

Definition wloE (xl w : Zinf) : Zinf :=
  if zltb (Fin 0) xl then zmul xl w
  else zadd (zmul (zsub xl (Fin 1)) w) (Fin 1).

Definition whiE (xu w : Zinf) : Zinf :=
  if zltb xu (Fin 0) then zmul xu w
  else zsub (zmul (zadd xu (Fin 1)) w) (Fin 1).

(* Normal forms. *)
Lemma wloE_fin : forall a z : Z, wloE (Fin a) (Fin z) = Fin (WloZ a z).
Proof.
  intros a z. unfold wloE, WloZ. rewrite zltb_0_fin.
  destruct (0 <? a); reflexivity.
Qed.

Lemma whiE_fin : forall b z : Z, whiE (Fin b) (Fin z) = Fin (WhiZ b z).
Proof.
  intros b z. unfold whiE, WhiZ. rewrite zltb_fin_0.
  destruct (b <? 0); reflexivity.
Qed.

Lemma wloE_minf : forall z : Z, 1 <= z -> wloE MInf (Fin z) = MInf.
Proof.
  intros z Hz. unfold wloE.
  change (zltb (Fin 0) MInf) with false.
  cbn [zsub]. rewrite zmul_minf_pos by lia. reflexivity.
Qed.

Lemma wloE_pinf : forall z : Z, 1 <= z -> wloE PInf (Fin z) = PInf.
Proof.
  intros z Hz. unfold wloE.
  change (zltb (Fin 0) PInf) with true.
  apply zmul_pinf_pos. exact Hz.
Qed.

Lemma whiE_minf : forall z : Z, 1 <= z -> whiE MInf (Fin z) = MInf.
Proof.
  intros z Hz. unfold whiE.
  change (zltb MInf (Fin 0)) with true.
  apply zmul_minf_pos. exact Hz.
Qed.

Lemma whiE_pinf : forall z : Z, 1 <= z -> whiE PInf (Fin z) = PInf.
Proof.
  intros z Hz. unfold whiE.
  change (zltb PInf (Fin 0)) with false.
  cbn [zadd]. rewrite zmul_pinf_pos by lia. reflexivity.
Qed.

Lemma wloE_pinf_inv : forall l (z : Z),
  1 <= z -> wloE l (Fin z) = PInf -> l = PInf.
Proof.
  intros [|a|] z Hz H.
  - rewrite wloE_minf in H by lia. discriminate.
  - rewrite wloE_fin in H. discriminate.
  - reflexivity.
Qed.

Lemma whiE_minf_inv : forall u (z : Z),
  1 <= z -> whiE u (Fin z) = MInf -> u = MInf.
Proof.
  intros [|b|] z Hz H.
  - reflexivity.
  - rewrite whiE_fin in H. discriminate.
  - rewrite whiE_pinf in H by lia. discriminate.
Qed.

(* Monotonicity of the window bounds in the x argument. *)
Lemma wloE_mono_x_fin : forall l (x z : Z),
  zle l (Fin x) -> 1 <= z -> zle (wloE l (Fin z)) (Fin (WloZ x z)).
Proof.
  intros [|a|] x z H Hz.
  - rewrite wloE_minf by lia. apply zle_minf.
  - rewrite wloE_fin. apply zle_fin. apply WloZ_mono_x; [exact Hz | exact H].
  - simpl in H. contradiction.
Qed.

Lemma whiE_mono_x_fin : forall u (x z : Z),
  zle (Fin x) u -> 1 <= z -> zle (Fin (WhiZ x z)) (whiE u (Fin z)).
Proof.
  intros [|b|] x z H Hz.
  - simpl in H. contradiction.
  - rewrite whiE_fin. apply zle_fin. apply WhiZ_mono_x; [exact Hz | exact H].
  - rewrite whiE_pinf by lia. apply zle_pinf.
Qed.

(* Non-emptiness of the window at Z∞ level. *)
Lemma wloE_le_whiE : forall c c' (z : Z),
  zle c c' -> 1 <= z -> zle (wloE c (Fin z)) (whiE c' (Fin z)).
Proof.
  intros [|a|] [|b|] z H Hz; simpl in H; try contradiction.
  - rewrite wloE_minf by lia. apply zle_minf.
  - rewrite wloE_minf by lia. apply zle_minf.
  - rewrite wloE_minf by lia. apply zle_minf.
  - rewrite wloE_fin, whiE_fin. apply zle_fin.
    pose proof (WloZ_mono_x a b z Hz H).
    pose proof (WloZ_le_WhiZ b z Hz). lia.
  - rewrite whiE_pinf by lia. apply zle_pinf.
  - rewrite whiE_pinf by lia. apply zle_pinf.
Qed.

(* Corner bounds: the window bound at any z inside [zl,zu] lies between the
   values at the two corners. *)
Lemma wloE_corner_lb : forall c zl zu (z : Z),
  1 <= z -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (zmin (wloE c zl) (wloE c zu)) (wloE c (Fin z)).
Proof.
  intros c zl zu z Hz H1 H2. unfold wloE.
  destruct (zltb (Fin 0) c).
  - apply zmul_corner_lb; assumption.
  - eapply zle_trans; [apply zmin_zadd1_le|].
    apply zadd1_mono2.
    apply zmul_corner_lb; assumption.
Qed.

Lemma whiE_corner_ub : forall c zl zu (z : Z),
  1 <= z -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (whiE c (Fin z)) (zmax (whiE c zl) (whiE c zu)).
Proof.
  intros c zl zu z Hz H1 H2. unfold whiE.
  destruct (zltb c (Fin 0)).
  - apply zmul_corner_ub; assumption.
  - eapply zle_trans; [|apply zsub1_le_zmax].
    apply zsub1_mono.
    apply zmul_corner_ub; assumption.
Qed.

(* Bridging window bounds and truncated division. *)
Lemma wloE_le_tdiv : forall l (y z : Z),
  1 <= z -> zle (wloE l (Fin z)) (Fin y) -> zle l (Fin (tdivZ y z)).
Proof.
  intros [|a|] y z Hz H.
  - exact I.
  - rewrite wloE_fin in H. simpl in H. apply zle_fin.
    apply tdivZ_win_ge; [exact Hz | exact H].
  - rewrite wloE_pinf in H by lia. simpl in H. contradiction.
Qed.

Lemma tdiv_le_whiE : forall u (y z : Z),
  1 <= z -> zle (Fin y) (whiE u (Fin z)) -> zle (Fin (tdivZ y z)) u.
Proof.
  intros [|b|] y z Hz H.
  - rewrite whiE_minf in H by lia. simpl in H. contradiction.
  - rewrite whiE_fin in H. simpl in H. apply zle_fin.
    apply tdivZ_win_le; [exact Hz | exact H].
  - exact I.
Qed.

(* ==================== Truncated division on Z∞ ==================== *)

(* On an infinite divisor the truncation of |y/z| < 1 is 0 for any y. *)
Definition ztdiv (x y : Zinf) : Zinf :=
  match y with
  | PInf => Fin 0
  | MInf => Fin 0
  | Fin b => match x with
             | Fin a => Fin (tdivZ a b)
             | MInf => if 0 <? b then MInf else PInf
             | PInf => if 0 <? b then PInf else MInf
             end
  end.

Lemma ztdiv_minf_pos : forall z : Z, 1 <= z -> ztdiv MInf (Fin z) = MInf.
Proof.
  intros z Hz. simpl. destruct (0 <? z) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E. lia.
Qed.

Lemma ztdiv_pinf_pos : forall z : Z, 1 <= z -> ztdiv PInf (Fin z) = PInf.
Proof.
  intros z Hz. simpl. destruct (0 <? z) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E. lia.
Qed.

(* Monotonicity of Z∞ truncated division in the numerator. *)
Lemma ztdiv_mono_y : forall w w' v,
  zle (Fin 1) v -> zle w w' -> zle (ztdiv w v) (ztdiv w' v).
Proof.
  intros w w' [|c|] Hv H; simpl in Hv; [contradiction| |].
  - destruct w as [|a|]; destruct w' as [|b|]; simpl in H; try contradiction.
    + rewrite ztdiv_minf_pos by lia. apply zle_minf.
    + rewrite ztdiv_minf_pos by lia. apply zle_minf.
    + rewrite ztdiv_minf_pos by lia. apply zle_minf.
    + cbn [ztdiv]. apply zle_fin. apply tdivZ_mono_num; lia.
    + rewrite ztdiv_pinf_pos by lia. apply zle_pinf.
    + rewrite ztdiv_pinf_pos by lia. apply zle_pinf.
  - cbn [ztdiv]. apply zle_fin. lia.
Qed.

(* Corner bounds for Z∞ truncated division of a finite numerator by a
   positive interval of divisors. *)
Lemma ztdiv_corner_lb : forall (y : Z) zl zu (z : Z),
  1 <= z -> zle (Fin 1) zl -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (zmin (ztdiv (Fin y) zl) (ztdiv (Fin y) zu)) (Fin (tdivZ y z)).
Proof.
  intros y [|l|] [|u|] z Hz H0 H1 H2; simpl in H0, H1, H2; try contradiction.
  - (* zl = Fin l, zu = Fin u *)
    destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [apply zmin_le_r|]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_antitone_div; lia.
    + eapply zle_trans; [apply zmin_le_l|]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_monotone_div; lia.
  - (* zl = Fin l, zu = +inf *)
    destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [apply zmin_le_r|]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_nonneg; lia.
    + eapply zle_trans; [apply zmin_le_l|]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_monotone_div; lia.
Qed.

Lemma ztdiv_corner_ub : forall (y : Z) zl zu (z : Z),
  1 <= z -> zle (Fin 1) zl -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (Fin (tdivZ y z)) (zmax (ztdiv (Fin y) zl) (ztdiv (Fin y) zu)).
Proof.
  intros y [|l|] [|u|] z Hz H0 H1 H2; simpl in H0, H1, H2; try contradiction.
  - destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [|apply zmax_ge_l]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_antitone_div; lia.
    + eapply zle_trans; [|apply zmax_ge_r]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_monotone_div; lia.
  - destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [|apply zmax_ge_l]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_antitone_div; lia.
    + eapply zle_trans; [|apply zmax_ge_r]. cbn [ztdiv]. apply zle_fin.
      apply tdivZ_nonpos; lia.
Qed.

(* ==================== The tdiv⁺ propagator (appendix figure) ============= *)

(* First phase of tden⁺: enforce Wlo(xl,z) ≤ yu on z ∈ [1,∞]. *)
Definition tdenP1 (xl yu : Zinf) : Itv :=
  if zltb (Fin 0) xl then imeet (Fin 1, PInf) (MInf, zfdiv yu xl)
  else imeet (Fin 1, PInf) (zcdiv (zsub yu (Fin 1)) (zsub xl (Fin 1)), PInf).

(* Second phase of tden⁺: enforce yl ≤ Whi(xu,z). *)
Definition tdenP2 (xu yl : Zinf) (z1 : Itv) : Itv :=
  if zltb (Fin (-1)) xu
    then imeet z1 (zcdiv (zadd yl (Fin 1)) (zadd xu (Fin 1)), PInf)
  else imeet z1 (MInf, zfdiv yl xu).

Definition tdenP (Xi Yi : Itv) : Itv :=
  tdenP2 (snd Xi) (fst Yi) (tdenP1 (fst Xi) (snd Yi)).

(* tnum⁺: hull of the truncation windows over z in Zi. *)
Definition tnumP (Xi Zi : Itv) : Itv :=
  (zmin (wloE (fst Xi) (fst Zi)) (wloE (fst Xi) (snd Zi)),
   zmax (whiE (snd Xi) (fst Zi)) (whiE (snd Xi) (snd Zi))).

(* Forward tdiv⁺: hull of the four corner divisions. *)
Definition tfwdP (Yi Zi : Itv) : Itv :=
  (zmin (zmin (ztdiv (fst Yi) (fst Zi)) (ztdiv (fst Yi) (snd Zi)))
        (zmin (ztdiv (snd Yi) (fst Zi)) (ztdiv (snd Yi) (snd Zi))),
   zmax (zmax (ztdiv (fst Yi) (fst Zi)) (ztdiv (fst Yi) (snd Zi)))
        (zmax (ztdiv (snd Yi) (fst Zi)) (ztdiv (snd Yi) (snd Zi)))).

(* ---------- Membership characterization of tden⁺ ---------- *)

Lemma tdenP1_mem : forall xl yu (z : Z),
  xl <> PInf -> yu <> MInf ->
  (imem z (tdenP1 xl yu) <-> (1 <= z /\ zle (wloE xl (Fin z)) yu)).
Proof.
  intros xl yu z HX HY. unfold tdenP1.
  destruct xl as [|a|]; [| |congruence].
  - (* xl = -inf: no constraint beyond z >= 1 *)
    change (zltb (Fin 0) MInf) with false.
    rewrite imem_imeet, !imem_pair. split.
    + intros [[H1 _] _]. simpl in H1. split; [lia|].
      rewrite wloE_minf by lia. apply zle_minf.
    + intros [Hz _]. split; [split|split].
      * apply zle_fin. lia.
      * apply zle_pinf.
      * cbn [zsub]. apply zcdiv_minf_le. exact Hz.
      * apply zle_pinf.
  - (* xl = Fin a *)
    destruct (Z_lt_le_dec 0 a) as [Ha|Ha].
    + (* a > 0 *)
      assert (E1 : zltb (Fin 0) (Fin a) = true) by (apply zltb_lt; simpl; lia).
      rewrite E1.
      assert (Ewl : wloE (Fin a) (Fin z) = Fin (a * z))
        by (unfold wloE; rewrite E1; reflexivity).
      rewrite Ewl.
      rewrite imem_imeet, !imem_pair. split.
      * intros [[H1 _] [_ H4]]. simpl in H1. split; [lia|].
        destruct yu as [|b|]; [congruence| |].
        -- simpl in H4. apply fdivZ_lb in H4; [|lia].
           apply zle_fin. nia.
        -- apply zle_pinf.
      * intros [Hz HC]. split; [split|split].
        -- apply zle_fin. lia.
        -- apply zle_pinf.
        -- apply zle_minf.
        -- destruct yu as [|b|]; [congruence| |].
           ++ simpl in HC. simpl. apply fdivZ_lb; [lia|]. nia.
           ++ rewrite zfdiv_pinf_pos by lia. exact I.
    + (* a <= 0 *)
      assert (E1 : zltb (Fin 0) (Fin a) = false) by (apply zltb_false; simpl; lia).
      rewrite E1.
      assert (Ewl : wloE (Fin a) (Fin z) = Fin ((a - 1) * z + 1)).
      { unfold wloE. rewrite E1. reflexivity. }
      rewrite Ewl.
      rewrite imem_imeet, !imem_pair. split.
      * intros [[H1 _] [H3 _]]. simpl in H1. split; [lia|].
        destruct yu as [|b|]; [congruence| |].
        -- apply zle_fin.
           pose proof (proj1 (cdivZ_le_neg (b - 1) (a - 1) z ltac:(lia)) H3).
           lia.
        -- apply zle_pinf.
      * intros [Hz HC]. split; [split|split].
        -- apply zle_fin. lia.
        -- apply zle_pinf.
        -- destruct yu as [|b|]; [congruence| |].
           ++ simpl in HC.
              exact (proj2 (cdivZ_le_neg (b - 1) (a - 1) z ltac:(lia)) ltac:(lia)).
           ++ cbn [zsub]. unfold zcdiv. simpl.
              destruct (0 <? a - 1) eqn:E3; [apply Z.ltb_lt in E3; lia|].
              simpl. exact I.
        -- apply zle_pinf.
Qed.

Lemma tdenP2_z1 : forall xu yl z1 (z : Z),
  imem z (tdenP2 xu yl z1) -> imem z z1.
Proof.
  intros xu yl z1 z H. unfold tdenP2 in H.
  destruct (zltb (Fin (-1)) xu); apply imem_imeet in H; tauto.
Qed.

Lemma tdenP2_mem : forall xu yl z1 (z : Z),
  xu <> MInf -> yl <> PInf -> 1 <= z ->
  (imem z (tdenP2 xu yl z1) <-> (imem z z1 /\ zle yl (whiE xu (Fin z)))).
Proof.
  intros xu yl z1 z HX HY Hz. unfold tdenP2.
  destruct xu as [|b|]; [congruence| |].
  - (* xu = Fin b *)
    destruct (Z_lt_le_dec (-1) b) as [Hb|Hb].
    + (* b > -1 *)
      assert (E1 : zltb (Fin (-1)) (Fin b) = true) by (apply zltb_lt; simpl; lia).
      rewrite E1.
      assert (Ewh : whiE (Fin b) (Fin z) = Fin ((b + 1) * z - 1)).
      { unfold whiE.
        assert (Eb : zltb (Fin b) (Fin 0) = false) by (apply zltb_false; simpl; lia).
        rewrite Eb. reflexivity. }
      rewrite Ewh.
      rewrite imem_imeet, imem_pair.
      destruct yl as [|c|]; [| | congruence].
      * (* yl = -inf *)
        split.
        -- intros [H1 _]. split; [exact H1 | apply zle_minf].
        -- intros [H1 _]. split; [exact H1|]. split; [|apply zle_pinf].
           unfold zcdiv. cbn [zadd zneg].
           rewrite zfdiv_pinf_pos by lia. simpl. exact I.
      * (* yl = Fin c *)
        split.
        -- intros [H1 [H3 _]]. split; [exact H1|].
           apply zle_fin.
           pose proof (proj1 (cdivZ_le (c + 1) (b + 1) z ltac:(lia)) H3). lia.
        -- intros [H1 HC]. split; [exact H1|]. split; [|apply zle_pinf].
           simpl in HC.
           exact (proj2 (cdivZ_le (c + 1) (b + 1) z ltac:(lia)) ltac:(lia)).
    + (* b <= -1 *)
      assert (E1 : zltb (Fin (-1)) (Fin b) = false)
        by (apply zltb_false; simpl; lia).
      rewrite E1.
      assert (Ewh : whiE (Fin b) (Fin z) = Fin (b * z)).
      { unfold whiE.
        assert (Eb : zltb (Fin b) (Fin 0) = true) by (apply zltb_lt; simpl; lia).
        rewrite Eb. reflexivity. }
      rewrite Ewh.
      rewrite imem_imeet, imem_pair.
      destruct yl as [|c|]; [| | congruence].
      * split.
        -- intros [H1 _]. split; [exact H1 | apply zle_minf].
        -- intros [H1 _]. split; [exact H1|]. split; [apply zle_minf|].
           simpl.
           destruct (0 <? b) eqn:E3; [apply Z.ltb_lt in E3; lia|].
           simpl. exact I.
      * split.
        -- intros [H1 [_ H4]]. split; [exact H1|].
           apply zle_fin.
           exact (proj1 (fdivZ_le_neg c b z ltac:(lia)) H4).
        -- intros [H1 HC]. split; [exact H1|]. split; [apply zle_minf|].
           simpl in HC.
           exact (proj2 (fdivZ_le_neg c b z ltac:(lia)) HC).
  - (* xu = +inf *)
    change (zltb (Fin (-1)) PInf) with true.
    rewrite whiE_pinf by lia.
    rewrite imem_imeet, imem_pair.
    split.
    + intros [H1 _]. split; [exact H1 | apply zle_pinf].
    + intros [H1 _]. split; [exact H1|]. split; [|apply zle_pinf].
      cbn [zadd]. apply zcdiv_pinf_le. exact Hz.
Qed.

(* The complete membership characterization of tden⁺:
   z belongs iff z ≥ 1, Wlo(xl,z) ≤ yu and yl ≤ Whi(xu,z). *)
Lemma tdenP_mem : forall Xi Yi (z : Z),
  ~ isbot Xi -> ~ isbot Yi ->
  (imem z (tdenP Xi Yi) <->
   (1 <= z /\
    zle (wloE (fst Xi) (Fin z)) (snd Yi) /\
    zle (fst Yi) (whiE (snd Xi) (Fin z)))).
Proof.
  intros [xl xu] [yl yu] z HX HY.
  apply not_isbot_char in HX. destruct HX as [HX1 [HX2 HX3]].
  apply not_isbot_char in HY. destruct HY as [HY1 [HY2 HY3]].
  unfold tdenP. cbn [fst snd].
  split.
  - intros H.
    pose proof (tdenP2_z1 _ _ _ _ H) as Hz1.
    apply tdenP1_mem in Hz1; [|exact HX2|exact HY3].
    destruct Hz1 as [Hz HC1].
    apply tdenP2_mem in H; [|exact HX3|exact HY2|exact Hz].
    destruct H as [_ HC2]. auto.
  - intros [Hz [HC1 HC2]].
    apply tdenP2_mem; [exact HX3|exact HY2|exact Hz|].
    split; [|exact HC2].
    apply tdenP1_mem; [exact HX2|exact HY3|]. auto.
Qed.

(* Lower bound 1 on the tden⁺ output. *)
Lemma tdenP1_lb1 : forall xl yu, zle (Fin 1) (fst (tdenP1 xl yu)).
Proof.
  intros xl yu. unfold tdenP1.
  destruct (zltb (Fin 0) xl); cbn [imeet fst]; apply zmax_ge_l.
Qed.

Lemma tdenP_lb1 : forall Xi Yi, zle (Fin 1) (fst (tdenP Xi Yi)).
Proof.
  intros Xi Yi. unfold tdenP, tdenP2.
  destruct (zltb (Fin (-1)) (snd Xi)); cbn [imeet fst];
    (eapply zle_trans; [apply tdenP1_lb1 | apply zmax_ge_l]).
Qed.

(* ==================== The tdiv⁺ propagator over V3 ==================== *)

Section TdivPropagator.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  (* The relation of the constraint x = tdiv⁺(y,z): z ≥ 1 ∧ x = tdiv(y,z). *)
  Definition Rtdp (a : Asn V3) : Prop := 1 <= a q /\ a r = tdivZ (a p) (a q).

  (* The three successive refinements of the appendix figure. *)
  Definition tdvZ (d : istore V3) : Itv := imeet (d q) (tdenP (d r) (d p)).
  Definition tdvY (d : istore V3) : Itv := imeet (d p) (tnumP (d r) (tdvZ d)).
  Definition tdvX (d : istore V3) : Itv := imeet (d r) (tfwdP (tdvY d) (tdvZ d)).

  Definition prop_tdivp (d : istore V3) : istore V3 :=
    if isbotb (tdvZ d) then vupd d q (tdvZ d)
    else if isbotb (tdvY d) then vupd (vupd d q (tdvZ d)) p (tdvY d)
    else vupd (vupd (vupd d q (tdvZ d)) p (tdvY d)) r (tdvX d).

  Lemma tdvZ_lb1 : forall d, zle (Fin 1) (fst (tdvZ d)).
  Proof.
    intros d. unfold tdvZ. cbn [imeet fst].
    eapply zle_trans; [apply tdenP_lb1 | apply zmax_ge_r].
  Qed.

  (* --------- Solutions are preserved by the three refinements --------- *)

  Lemma sol_mem_tdvZ : forall d asn,
    ibox d asn -> Rtdp asn -> imem (asn q) (tdvZ d).
  Proof.
    intros d asn Hbox [Hq Hr].
    pose proof (tdivZ_win_refl (asn p) (asn q) Hq) as [Hc1 Hc2].
    apply imem_imeet. split; [apply Hbox|].
    apply tdenP_mem.
    - exact (imem_not_isbot _ _ (Hbox r)).
    - exact (imem_not_isbot _ _ (Hbox p)).
    - split; [exact Hq|]. split.
      + (* Wlo(xl, z) ≤ yu *)
        eapply zle_trans.
        * apply (wloE_mono_x_fin (fst (d r)) (asn r) (asn q));
            [apply (Hbox r) | exact Hq].
        * eapply zle_trans; [|apply (Hbox p)].
          apply zle_fin. rewrite Hr. exact Hc1.
      + (* yl ≤ Whi(xu, z) *)
        eapply zle_trans; [apply (Hbox p)|].
        eapply zle_trans;
          [| apply (whiE_mono_x_fin (snd (d r)) (asn r) (asn q));
             [apply (Hbox r) | exact Hq]].
        apply zle_fin. rewrite Hr. exact Hc2.
  Qed.

  Lemma sol_mem_tdvY : forall d asn,
    ibox d asn -> Rtdp asn -> imem (asn p) (tdvY d).
  Proof.
    intros d asn Hbox HR.
    pose proof (sol_mem_tdvZ d asn Hbox HR) as [HZ1 HZ2].
    destruct HR as [Hq Hr].
    pose proof (tdivZ_win_refl (asn p) (asn q) Hq) as [Hc1 Hc2].
    apply imem_imeet. split; [apply Hbox|].
    unfold tnumP. apply imem_pair. split.
    - (* lower corner ≤ y *)
      eapply zle_trans.
      + apply (wloE_corner_lb (fst (d r)) (fst (tdvZ d)) (snd (tdvZ d)) (asn q));
          [exact Hq | exact HZ1 | exact HZ2].
      + eapply zle_trans.
        * apply (wloE_mono_x_fin (fst (d r)) (asn r) (asn q));
            [apply (Hbox r) | exact Hq].
        * apply zle_fin. rewrite Hr. exact Hc1.
    - (* y ≤ upper corner *)
      eapply zle_trans;
        [| apply (whiE_corner_ub (snd (d r)) (fst (tdvZ d)) (snd (tdvZ d)) (asn q));
           [exact Hq | exact HZ1 | exact HZ2]].
      eapply zle_trans;
        [| apply (whiE_mono_x_fin (snd (d r)) (asn r) (asn q));
           [apply (Hbox r) | exact Hq]].
      apply zle_fin. rewrite Hr. exact Hc2.
  Qed.

  Lemma sol_mem_tdvX : forall d asn,
    ibox d asn -> Rtdp asn -> imem (asn r) (tdvX d).
  Proof.
    intros d asn Hbox HR.
    pose proof (sol_mem_tdvZ d asn Hbox HR) as [HZ1 HZ2].
    pose proof (sol_mem_tdvY d asn Hbox HR) as [HY1 HY2].
    pose proof (tdvZ_lb1 d) as HZlb.
    destruct HR as [Hq Hr].
    apply imem_imeet. split; [apply Hbox|].
    unfold tfwdP. apply imem_pair. split.
    - (* min4 ≤ tdiv(y,z) *)
      rewrite Hr.
      eapply zle_trans;
        [| apply (ztdiv_corner_lb (asn p) (fst (tdvZ d)) (snd (tdvZ d)) (asn q));
           [exact Hq | exact HZlb | exact HZ1 | exact HZ2]].
      apply zmin_glb.
      + eapply zle_trans; [apply zmin_le_l|].
        eapply zle_trans; [apply zmin_le_l|].
        apply ztdiv_mono_y; [exact HZlb | exact HY1].
      + eapply zle_trans; [apply zmin_le_l|].
        eapply zle_trans; [apply zmin_le_r|].
        apply ztdiv_mono_y; [|exact HY1].
        eapply zle_trans; [exact HZlb|].
        eapply zle_trans; [exact HZ1 | exact HZ2].
    - (* tdiv(y,z) ≤ max4 *)
      rewrite Hr.
      eapply zle_trans;
        [apply (ztdiv_corner_ub (asn p) (fst (tdvZ d)) (snd (tdvZ d)) (asn q));
         [exact Hq | exact HZlb | exact HZ1 | exact HZ2] |].
      apply zmax_lub.
      + eapply zle_trans; [|apply zmax_ge_r].
        eapply zle_trans; [|apply zmax_ge_l].
        apply ztdiv_mono_y; [exact HZlb | exact HY2].
      + eapply zle_trans; [|apply zmax_ge_r].
        eapply zle_trans; [|apply zmax_ge_r].
        apply ztdiv_mono_y; [|exact HY2].
        eapply zle_trans; [exact HZlb|].
        eapply zle_trans; [exact HZ1 | exact HZ2].
  Qed.

  (* Soundness of the tdiv⁺ propagator. *)
  Lemma prop_tdivp_preserves : forall d asn,
    ibox d asn -> Rtdp asn -> forall w, imem (asn w) (prop_tdivp d w).
  Proof.
    intros d asn Hbox HR w.
    pose proof (sol_mem_tdvZ d asn Hbox HR) as HmZ.
    pose proof (sol_mem_tdvY d asn Hbox HR) as HmY.
    pose proof (sol_mem_tdvX d asn Hbox HR) as HmX.
    unfold prop_tdivp.
    destruct (isbotb (tdvZ d)) eqn:EZ.
    { exfalso. apply isbotb_isbot in EZ. exact (imem_not_isbot _ _ HmZ EZ). }
    destruct (isbotb (tdvY d)) eqn:EY.
    { exfalso. apply isbotb_isbot in EY. exact (imem_not_isbot _ _ HmY EY). }
    destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
    - rewrite vupd_same. exact HmX.
    - rewrite (vupd_other _ r _ p) by congruence.
      rewrite vupd_same. exact HmY.
    - rewrite (vupd_other _ r _ q) by congruence.
      rewrite (vupd_other _ p _ q) by congruence.
      rewrite vupd_same. exact HmZ.
  Qed.

  Lemma prop_tdivp_sound : forall d, leI V3 (bestR Rtdp d) (prop_tdivp d).
  Proof.
    intros d. apply (sols_preserved_sound_R Rtdp r).
    intros asn Hb HR. apply prop_tdivp_preserves; assumption.
  Qed.

End TdivPropagator.

(* ==================== α-completeness helpers for tdiv⁺ ==================== *)

Section TdivComplete.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  (* The y-window of a given denominator z: y must lie in
     [Wlo(xl,z), Whi(xu,z)] ∩ (d p). *)
  Definition Twin (d : istore V3) (z : Z) : Itv :=
    imeet (d p) (wloE (fst (d r)) (Fin z), whiE (snd (d r)) (Fin z)).

  Lemma Twin_nonbot : forall d (z : Z),
    ~ isbot (d r) -> ~ isbot (d p) -> 1 <= z ->
    zle (wloE (fst (d r)) (Fin z)) (snd (d p)) ->
    zle (fst (d p)) (whiE (snd (d r)) (Fin z)) ->
    ~ isbot (Twin d z).
  Proof.
    intros d z HdR HdP Hz HC1 HC2.
    destruct (d r) as [xl xu] eqn:ER. destruct (d p) as [yl yu] eqn:EP.
    apply not_isbot_char in HdR. destruct HdR as [HR1 [HR2 HR3]].
    apply not_isbot_char in HdP. destruct HdP as [HP1 [HP2 HP3]].
    cbn [fst snd] in *.
    unfold Twin. rewrite ER, EP. unfold imeet. cbn [fst snd].
    apply not_isbot_char. repeat split.
    - apply zmax_lub; apply zmin_glb.
      + exact HP1.
      + exact HC2.
      + exact HC1.
      + apply wloE_le_whiE; [exact HR1 | exact Hz].
    - intros Hc. apply zmax_pinf in Hc. destruct Hc as [Hc|Hc].
      + exact (HP2 Hc).
      + exact (HR2 (wloE_pinf_inv xl z Hz Hc)).
    - intros Hc. apply zmin_minf in Hc. destruct Hc as [Hc|Hc].
      + exact (HP3 Hc).
      + exact (HR3 (whiE_minf_inv xu z Hz Hc)).
  Qed.

  (* Any y in the window of a member z of d(q) yields a solution. *)
  Lemma sol_of_wy : forall d (z y : Z),
    1 <= z -> imem z (d q) -> imem y (Twin d z) ->
    exists asn, ibox d asn /\ Rtdp r p q asn /\ asn p = y /\ asn q = z.
  Proof.
    intros d z y Hz Hqz Hy.
    apply imem_imeet in Hy. destruct Hy as [Hyp Hy].
    apply imem_pair in Hy. destruct Hy as [Hy1 Hy2].
    exists (asn_rpq r p q (tdivZ y z) y z).
    assert (Br : imem (tdivZ y z) (d r)).
    { split.
      - apply (wloE_le_tdiv (fst (d r)) y z Hz Hy1).
      - apply (tdiv_le_whiE (snd (d r)) y z Hz Hy2). }
    split; [|split; [|split]].
    - intros w. destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
      + rewrite asn_rpq_r. exact Br.
      + rewrite asn_rpq_p by exact Hrp. exact Hyp.
      + rewrite asn_rpq_q by assumption. exact Hqz.
    - unfold Rtdp. rewrite asn_rpq_r, asn_rpq_p, asn_rpq_q by assumption.
      split; [exact Hz | reflexivity].
    - apply asn_rpq_p. exact Hrp.
    - apply asn_rpq_q; assumption.
  Qed.

  (* Every member of the refined denominator interval yields a solution. *)
  Lemma sol_of_z : forall d (z : Z),
    ~ isbot (d r) -> ~ isbot (d p) ->
    imem z (tdvZ r p q d) ->
    exists asn, ibox d asn /\ Rtdp r p q asn /\ asn q = z.
  Proof.
    intros d z HdR HdP Hm.
    apply imem_imeet in Hm. destruct Hm as [Hq Hden].
    apply tdenP_mem in Hden; [|exact HdR|exact HdP].
    destruct Hden as [Hz [HC1 HC2]].
    destruct (not_isbot_mem (Twin d z) (Twin_nonbot d z HdR HdP Hz HC1 HC2))
      as [y Hy].
    destruct (sol_of_wy d z y Hz Hq Hy) as [asn [Hb [HR [_ Hqz]]]].
    exists asn. auto.
  Qed.

  (* A member z of the refined denominator whose window is further clamped
     also yields a solution. *)
  Lemma sol_of_z_clamped : forall d (z : Z) (cl cu : Zinf),
    ~ isbot (d r) -> ~ isbot (d p) ->
    imem z (tdvZ r p q d) ->
    zle cl (snd (Twin d z)) -> zle (fst (Twin d z)) cu ->
    zle cl cu -> cl <> PInf -> cu <> MInf ->
    exists asn y, ibox d asn /\ Rtdp r p q asn /\ asn q = z /\ asn p = y /\
                  zle cl (Fin y) /\ zle (Fin y) cu.
  Proof.
    intros d z cl cu HdR HdP Hm Hcl Hcu Hclu HclP HcuM.
    apply imem_imeet in Hm. destruct Hm as [Hq Hden].
    apply tdenP_mem in Hden; [|exact HdR|exact HdP].
    destruct Hden as [Hz [HC1 HC2]].
    pose proof (Twin_nonbot d z HdR HdP Hz HC1 HC2) as HW.
    destruct (Twin d z) as [wl wu] eqn:EW.
    cbn [fst snd] in Hcl, Hcu.
    apply not_isbot_char in HW. destruct HW as [HW1 [HW2 HW3]].
    assert (HWc : ~ isbot (imeet (wl, wu) (cl, cu))).
    { unfold imeet. cbn [fst snd]. apply not_isbot_char. repeat split.
      - apply zmax_lub; apply zmin_glb; assumption.
      - intros Hc. apply zmax_pinf in Hc. tauto.
      - intros Hc. apply zmin_minf in Hc. tauto. }
    destruct (not_isbot_mem _ HWc) as [y Hy].
    apply imem_imeet in Hy. destruct Hy as [HyW Hyc].
    apply imem_pair in Hyc. destruct Hyc as [Hyc1 Hyc2].
    destruct (sol_of_wy d z y Hz Hq) as [asn [Hb [HR [Hp' Hq']]]].
    { rewrite EW. exact HyW. }
    exists asn, y.
    split; [exact Hb|]. split; [exact HR|]. split; [exact Hq'|].
    split; [exact Hp'|]. split; [exact Hyc1 | exact Hyc2].
  Qed.

End TdivComplete.

(* ---------- Choice of a good denominator for each bound obligation ------- *)

(* For the lower bound of the numerator: a member z with Wlo(xl,z) ≤ M. *)
Lemma zstar_wlo_lo : forall (xl : Zinf) (Zi : Itv) (M : Z),
  xl <> PInf -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (zmin (wloE xl (fst Zi)) (wloE xl (snd Zi))) (Fin M) ->
  exists z, imem z Zi /\ 1 <= z /\ zle (wloE xl (Fin z)) (Fin M).
Proof.
  intros xl [zl zu] M HxlP Hnb Hlb1 Hmin.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  cbn [fst snd] in *.
  destruct zl as [|l|]; [simpl in Hlb1; contradiction | | congruence].
  simpl in Hlb1.
  assert (Hmeml : imem l (Fin l, zu)).
  { split; [simpl; lia | exact H1]. }
  destruct xl as [|a|]; [| | congruence].
  - (* xl = -inf *)
    exists l. split; [exact Hmeml|]. split; [lia|].
    rewrite wloE_minf by lia. apply zle_minf.
  - (* xl = Fin a *)
    destruct (Z_lt_le_dec 0 a) as [Ha|Ha].
    + (* a > 0: monotone in z *)
      assert (Ea : zltb (Fin 0) (Fin a) = true) by (apply zltb_lt; simpl; lia).
      assert (Ewl : forall w, wloE (Fin a) w = zmul (Fin a) w)
        by (intros w; unfold wloE; rewrite Ea; reflexivity).
      rewrite !Ewl in Hmin.
      destruct (zmin_case (zmul (Fin a) (Fin l)) (zmul (Fin a) zu))
        as [[E _]|[E _]]; rewrite E in Hmin.
      * exists l. split; [exact Hmeml|]. split; [lia|].
        rewrite Ewl. exact Hmin.
      * destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia|]. rewrite Ewl. exact Hmin.
        -- rewrite zmul_fin_pinf_pos in Hmin by lia. simpl in Hmin. contradiction.
    + (* a <= 0: the slope a-1 is negative *)
      assert (Ea : zltb (Fin 0) (Fin a) = false) by (apply zltb_false; simpl; lia).
      assert (Ewl : forall w, wloE (Fin a) w = zadd (zmul (Fin (a - 1)) w) (Fin 1))
        by (intros w; unfold wloE; rewrite Ea; reflexivity).
      rewrite !Ewl in Hmin.
      destruct (zmin_case (zadd (zmul (Fin (a - 1)) (Fin l)) (Fin 1))
                          (zadd (zmul (Fin (a - 1)) zu) (Fin 1)))
        as [[E _]|[E _]]; rewrite E in Hmin.
      * exists l. split; [exact Hmeml|]. split; [lia|].
        rewrite Ewl. exact Hmin.
      * destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia|]. rewrite Ewl. exact Hmin.
        -- (* zu = +inf *)
           exists (Z.max l (cdivZ (M - 1) (a - 1))). split.
           { split; simpl; [lia | exact I]. }
           split; [lia|].
           pose proof (proj1 (cdivZ_le_neg (M - 1) (a - 1)
                        (Z.max l (cdivZ (M - 1) (a - 1))) ltac:(lia))
                        ltac:(lia)) as Hcc.
           rewrite Ewl. apply zle_fin. lia.
Qed.

(* For the upper bound of the numerator: a member z with M ≤ Whi(xu,z). *)
Lemma zstar_whi_hi : forall (xu : Zinf) (Zi : Itv) (M : Z),
  xu <> MInf -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (Fin M) (zmax (whiE xu (fst Zi)) (whiE xu (snd Zi))) ->
  exists z, imem z Zi /\ 1 <= z /\ zle (Fin M) (whiE xu (Fin z)).
Proof.
  intros xu [zl zu] M HxuM Hnb Hlb1 Hmax.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  cbn [fst snd] in *.
  destruct zl as [|l|]; [simpl in Hlb1; contradiction | | congruence].
  simpl in Hlb1.
  assert (Hmeml : imem l (Fin l, zu)).
  { split; [simpl; lia | exact H1]. }
  destruct xu as [|b|]; [congruence| |].
  - (* xu = Fin b *)
    destruct (Z_lt_le_dec b 0) as [Hb|Hb].
    + (* b < 0: whiE is multiplication by b *)
      assert (Eb : zltb (Fin b) (Fin 0) = true) by (apply zltb_lt; simpl; lia).
      assert (Ewh : forall w, whiE (Fin b) w = zmul (Fin b) w)
        by (intros w; unfold whiE; rewrite Eb; reflexivity).
      rewrite !Ewh in Hmax.
      destruct (zmax_case (zmul (Fin b) (Fin l)) (zmul (Fin b) zu))
        as [[E _]|[E _]]; rewrite E in Hmax.
      * (* max at zu *)
        destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia|]. rewrite Ewh. exact Hmax.
        -- rewrite zmul_fin_pinf_neg in Hmax by lia. simpl in Hmax. contradiction.
      * exists l. split; [exact Hmeml|]. split; [lia|].
        rewrite Ewh. exact Hmax.
    + (* b >= 0: the slope b+1 is positive *)
      assert (Eb : zltb (Fin b) (Fin 0) = false) by (apply zltb_false; simpl; lia).
      assert (Ewh : forall w, whiE (Fin b) w = zsub (zmul (Fin (b + 1)) w) (Fin 1))
        by (intros w; unfold whiE; rewrite Eb; reflexivity).
      rewrite !Ewh in Hmax.
      destruct (zmax_case (zsub (zmul (Fin (b + 1)) (Fin l)) (Fin 1))
                          (zsub (zmul (Fin (b + 1)) zu) (Fin 1)))
        as [[E _]|[E _]]; rewrite E in Hmax.
      * (* max at zu *)
        destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia|]. rewrite Ewh. exact Hmax.
        -- (* zu = +inf *)
           exists (Z.max l (cdivZ (M + 1) (b + 1))). split.
           { split; simpl; [lia | exact I]. }
           split; [lia|].
           pose proof (proj1 (cdivZ_le (M + 1) (b + 1)
                        (Z.max l (cdivZ (M + 1) (b + 1))) ltac:(lia))
                        ltac:(lia)) as Hcc.
           rewrite Ewh. apply zle_fin. lia.
      * exists l. split; [exact Hmeml|]. split; [lia|].
        rewrite Ewh. exact Hmax.
  - (* xu = +inf *)
    exists l. split; [exact Hmeml|]. split; [lia|].
    rewrite whiE_pinf by lia. apply zle_pinf.
Qed.

(* For the lower bound of the quotient: a member z with yl ≤ Whi(M,z), given
   that some corner tdiv(Y0,e) is at most M (yl ≤ Y0). *)
Lemma zstar_tdiv_lo : forall (yl Y0 : Zinf) (Zi : Itv) (M : Z),
  Y0 <> PInf -> zle yl Y0 -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (zmin (ztdiv Y0 (fst Zi)) (ztdiv Y0 (snd Zi))) (Fin M) ->
  exists z, imem z Zi /\ 1 <= z /\ zle yl (Fin (WhiZ M z)).
Proof.
  intros yl Y0 [zl zu] M HY0 HylY0 Hnb Hlb1 Hmin.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  cbn [fst snd] in *.
  destruct zl as [|l|]; [simpl in Hlb1; contradiction | | congruence].
  simpl in Hlb1.
  assert (Hmeml : imem l (Fin l, zu)).
  { split; [simpl; lia | exact H1]. }
  destruct Y0 as [|w|]; [| | congruence].
  { (* Y0 = -inf, hence yl = -inf *)
    apply zle_minf_eq in HylY0. subst yl.
    exists l. split; [exact Hmeml|]. split; [lia | exact I]. }
  (* Y0 = Fin w *)
  destruct (zmin_case (ztdiv (Fin w) (Fin l)) (ztdiv (Fin w) zu))
    as [[E _]|[E _]]; rewrite E in Hmin.
  - (* corner at zl = Fin l *)
    exists l. split; [exact Hmeml|]. split; [lia|].
    simpl in Hmin.
    assert (Hw : w <= WhiZ M l) by (apply tdivZ_win_le; [lia | exact Hmin]).
    destruct yl as [|c|].
    + exact I.
    + apply zle_fin. simpl in HylY0. lia.
    + simpl in HylY0. contradiction.
  - (* corner at zu *)
    destruct zu as [|u|]; [congruence| |].
    + exists u. simpl in H1. split; [split; simpl; lia|].
      split; [lia|].
      simpl in Hmin.
      assert (Hw : w <= WhiZ M u) by (apply tdivZ_win_le; [lia | exact Hmin]).
      destruct yl as [|c|].
      * exact I.
      * apply zle_fin. simpl in HylY0. lia.
      * simpl in HylY0. contradiction.
    + (* zu = +inf: the corner is tdiv(w,∞) = 0, so M ≥ 0 *)
      simpl in Hmin.
      destruct yl as [|c|]; [| | simpl in HylY0; contradiction].
      * exists l. split; [exact Hmeml|]. split; [lia | exact I].
      * simpl in HylY0.
        exists (Z.max l (cdivZ (c + 1) (M + 1))). split.
        { split; simpl; [lia | exact I]. }
        split; [lia|].
        apply zle_fin.
        pose proof (proj1 (cdivZ_le (c + 1) (M + 1)
                     (Z.max l (cdivZ (c + 1) (M + 1))) ltac:(lia))
                     ltac:(lia)) as Hcc.
        unfold WhiZ.
        destruct (M <? 0) eqn:EM; zbool; lia.
Qed.

(* For the upper bound of the quotient: a member z with Wlo(M,z) ≤ yu, given
   that some corner tdiv(Y1,e) is at least M (Y1 ≤ yu). *)
Lemma zstar_tdiv_hi : forall (yu Y1 : Zinf) (Zi : Itv) (M : Z),
  yu <> MInf -> zle Y1 yu -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (Fin M) (zmax (ztdiv Y1 (fst Zi)) (ztdiv Y1 (snd Zi))) ->
  exists z, imem z Zi /\ 1 <= z /\ zle (Fin (WloZ M z)) yu.
Proof.
  intros yu Y1 [zl zu] M Hyu HY1yu Hnb Hlb1 Hmax.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  cbn [fst snd] in *.
  destruct zl as [|l|]; [simpl in Hlb1; contradiction | | congruence].
  simpl in Hlb1.
  assert (Hmeml : imem l (Fin l, zu)).
  { split; [simpl; lia | exact H1]. }
  destruct Y1 as [|w|].
  { (* Y1 = -inf *)
    destruct (zmax_case (ztdiv MInf (Fin l)) (ztdiv MInf zu))
      as [[E _]|[E _]]; rewrite E in Hmax.
    - (* corner at zu *)
      destruct zu as [|u|]; [congruence| |].
      + simpl in H1. rewrite ztdiv_minf_pos in Hmax by lia.
        simpl in Hmax. contradiction.
      + (* zu = +inf: tdiv(-inf,∞) = 0, so M ≤ 0 *)
        simpl in Hmax.
        destruct yu as [|c|]; [congruence| |].
        * exists (Z.max l (cdivZ (c - 1) (M - 1))). split.
          { split; simpl; [lia | exact I]. }
          split; [lia|].
          apply zle_fin.
          pose proof (proj1 (cdivZ_le_neg (c - 1) (M - 1)
                       (Z.max l (cdivZ (c - 1) (M - 1))) ltac:(lia))
                       ltac:(lia)) as Hcc.
          unfold WloZ.
          destruct (0 <? M) eqn:EM; zbool; lia.
        * exists l. split; [exact Hmeml|]. split; [lia | apply zle_pinf].
    - rewrite ztdiv_minf_pos in Hmax by lia. simpl in Hmax. contradiction. }
  2:{ (* Y1 = +inf, hence yu = +inf *)
    apply zle_pinf_eq in HY1yu. subst yu.
    exists l. split; [exact Hmeml|]. split; [lia | apply zle_pinf]. }
  (* Y1 = Fin w *)
  destruct (zmax_case (ztdiv (Fin w) (Fin l)) (ztdiv (Fin w) zu))
    as [[E _]|[E _]]; rewrite E in Hmax.
  - (* corner at zu *)
    destruct zu as [|u|]; [congruence| |].
    + exists u. simpl in H1. split; [split; simpl; lia|].
      split; [lia|].
      simpl in Hmax.
      assert (Hw : WloZ M u <= w) by (apply tdivZ_win_ge; [lia | exact Hmax]).
      destruct yu as [|c|]; [congruence| |].
      * apply zle_fin. simpl in HY1yu. lia.
      * apply zle_pinf.
    + (* zu = +inf: tdiv(w,∞) = 0, so M ≤ 0 *)
      simpl in Hmax.
      destruct yu as [|c|]; [congruence| |].
      * exists (Z.max l (cdivZ (c - 1) (M - 1))). split.
        { split; simpl; [lia | exact I]. }
        split; [lia|].
        apply zle_fin.
        pose proof (proj1 (cdivZ_le_neg (c - 1) (M - 1)
                     (Z.max l (cdivZ (c - 1) (M - 1))) ltac:(lia))
                     ltac:(lia)) as Hcc.
        unfold WloZ.
        destruct (0 <? M) eqn:EM; zbool; lia.
      * exists l. split; [exact Hmeml|]. split; [lia | apply zle_pinf].
  - (* corner at zl = Fin l *)
    exists l. split; [exact Hmeml|]. split; [lia|].
    simpl in Hmax.
    assert (Hw : WloZ M l <= w) by (apply tdivZ_win_ge; [lia | exact Hmax]).
    destruct yu as [|c|]; [congruence| |].
    + apply zle_fin. simpl in HY1yu. lia.
    + apply zle_pinf.
Qed.

(* ---------- α-completeness of the tdiv⁺ propagator ---------- *)

Section TdivBest.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  Lemma prop_tdivp_complete : forall d,
    leI V3 (prop_tdivp r p q d) (bestR (Rtdp r p q) d).
  Proof.
    intros d. unfold prop_tdivp.
    destruct (isbotb (tdvZ r p q d)) eqn:EZ.
    { apply isbotb_isbot in EZ. left. exists q. rewrite vupd_same. exact EZ. }
    apply isbotb_false in EZ.
    destruct (isbotb (tdvY r p q d)) eqn:EY.
    { apply isbotb_isbot in EY. left. exists p. rewrite vupd_same. exact EY. }
    apply isbotb_false in EY.
    destruct (classic (isbot (tdvX r p q d))) as [EX|EX].
    { left. exists r. rewrite vupd_same. exact EX. }
    assert (HdR : ~ isbot (d r)).
    { intro Hb. apply EX. apply isbot_imeet_l. exact Hb. }
    assert (HdP : ~ isbot (d p)).
    { intro Hb. apply EY. apply isbot_imeet_l. exact Hb. }
    assert (HdQ : ~ isbot (d q)).
    { intro Hb. apply EZ. apply isbot_imeet_l. exact Hb. }
    pose proof (tdvZ_lb1 r p q d) as HZlb.
    assert (HZlele : zle (fst (tdvZ r p q d)) (snd (tdvZ r p q d))).
    { destruct (tdvZ r p q d) as [a b] eqn:EE.
      apply not_isbot_char in EZ. cbn [fst snd]. tauto. }
    assert (HYchar := EY).
    destruct (tdvY r p q d) as [Yl Yu] eqn:EYI.
    apply not_isbot_char in HYchar. destruct HYchar as [HY1 [HY2 HY3]].
    right. intros w.
    destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
    - (* variable r: the interval tdvX *)
      rewrite vupd_same.
      apply isle_bestR_of_wit.
      + (* lower bound of x *)
        intros M HM.
        unfold tdvX in HM. rewrite EYI in HM.
        unfold imeet in HM. cbn [fst] in HM.
        assert (HxlM : zle (fst (d r)) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_l | exact HM]. }
        assert (Hmin4 : zle (fst (tfwdP (Yl, Yu) (tdvZ r p q d))) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_r | exact HM]. }
        unfold tfwdP in Hmin4. cbn [fst snd] in Hmin4.
        assert (Hrow : zle (zmin (ztdiv Yl (fst (tdvZ r p q d)))
                                 (ztdiv Yl (snd (tdvZ r p q d)))) (Fin M)).
        { destruct (zmin_case
              (zmin (ztdiv Yl (fst (tdvZ r p q d)))
                    (ztdiv Yl (snd (tdvZ r p q d))))
              (zmin (ztdiv Yu (fst (tdvZ r p q d)))
                    (ztdiv Yu (snd (tdvZ r p q d)))))
            as [[E _]|[E _]]; rewrite E in Hmin4; [exact Hmin4|].
          eapply zle_trans; [|exact Hmin4].
          apply zmin_glb.
          - eapply zle_trans; [apply zmin_le_l|].
            apply ztdiv_mono_y; [exact HZlb | exact HY1].
          - eapply zle_trans; [apply zmin_le_r|].
            apply ztdiv_mono_y;
              [eapply zle_trans; [exact HZlb | exact HZlele] | exact HY1]. }
        assert (HylYl : zle (fst (d p)) Yl).
        { assert (E := EYI). unfold tdvY in E.
          unfold imeet in E. injection E as E1 E2.
          rewrite <- E1. apply zmax_ge_l. }
        destruct (zstar_tdiv_lo (fst (d p)) Yl (tdvZ r p q d) M HY2 HylYl EZ HZlb Hrow)
          as [z [Hmz [Hz1 Hyl]]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z MInf
                    (Fin (WhiZ M z)) HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [_ Hycu]]]]]]].
        * apply zle_minf.
        * unfold Twin. unfold imeet. cbn [fst].
          apply zmax_lub; [exact Hyl|].
          eapply zle_trans;
            [apply (wloE_mono_x_fin (fst (d r)) M z HxlM Hz1)|].
          apply zle_fin. apply WloZ_le_WhiZ. exact Hz1.
        * apply zle_minf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          destruct HR as [_ Hreq]. rewrite Hreq, Hpy, Hqz.
          simpl in Hycu. apply tdivZ_win_le; [lia | exact Hycu].
      + (* upper bound of x *)
        intros M HM.
        unfold tdvX in HM. rewrite EYI in HM.
        unfold imeet in HM. cbn [snd] in HM.
        assert (HxuM : zle (Fin M) (snd (d r))).
        { eapply zle_trans; [exact HM | apply zmin_le_l]. }
        assert (Hmax4 : zle (Fin M) (snd (tfwdP (Yl, Yu) (tdvZ r p q d)))).
        { eapply zle_trans; [exact HM | apply zmin_le_r]. }
        unfold tfwdP in Hmax4. cbn [fst snd] in Hmax4.
        assert (Hrow : zle (Fin M) (zmax (ztdiv Yu (fst (tdvZ r p q d)))
                                         (ztdiv Yu (snd (tdvZ r p q d))))).
        { eapply zle_trans; [exact Hmax4|].
          destruct (zmax_case
              (zmax (ztdiv Yl (fst (tdvZ r p q d)))
                    (ztdiv Yl (snd (tdvZ r p q d))))
              (zmax (ztdiv Yu (fst (tdvZ r p q d)))
                    (ztdiv Yu (snd (tdvZ r p q d)))))
            as [[E _]|[E _]]; rewrite E.
          - apply zle_refl.
          - apply zmax_lub.
            + eapply zle_trans; [|apply zmax_ge_l].
              apply ztdiv_mono_y; [exact HZlb | exact HY1].
            + eapply zle_trans; [|apply zmax_ge_r].
              apply ztdiv_mono_y;
                [eapply zle_trans; [exact HZlb | exact HZlele] | exact HY1]. }
        assert (HYuyu : zle Yu (snd (d p))).
        { assert (E := EYI). unfold tdvY in E.
          unfold imeet in E. injection E as E1 E2.
          rewrite <- E2. apply zmin_le_l. }
        assert (Hyu : snd (d p) <> MInf).
        { apply not_isbot_char in HdP.
          destruct (d p) as [pl pu]. cbn [fst snd] in *. tauto. }
        destruct (zstar_tdiv_hi (snd (d p)) Yu (tdvZ r p q d) M Hyu HYuyu EZ HZlb Hrow)
          as [z [Hmz [Hz1 Hyu']]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z (Fin (WloZ M z))
                    PInf HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [Hycl _]]]]]]].
        * unfold Twin. unfold imeet. cbn [snd].
          apply zmin_glb; [exact Hyu'|].
          eapply zle_trans;
            [| apply (whiE_mono_x_fin (snd (d r)) M z HxuM Hz1)].
          apply zle_fin. apply WloZ_le_WhiZ. exact Hz1.
        * apply zle_pinf.
        * apply zle_pinf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          destruct HR as [_ Hreq]. rewrite Hreq, Hpy, Hqz.
          simpl in Hycl. apply tdivZ_win_ge; [lia | exact Hycl].
    - (* variable p: the interval tdvY *)
      rewrite (vupd_other _ r _ p) by congruence.
      rewrite vupd_same.
      apply isle_bestR_of_wit.
      + intros M HM.
        assert (E := EYI). unfold tdvY, tnumP in E.
        unfold imeet in E. injection E as E1 E2.
        rewrite <- E1 in HM. cbn [fst snd] in HM.
        assert (HylM : zle (fst (d p)) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_l | exact HM]. }
        assert (Hnum : zle (zmin (wloE (fst (d r)) (fst (tdvZ r p q d)))
                                 (wloE (fst (d r)) (snd (tdvZ r p q d)))) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_r | exact HM]. }
        assert (HxlP : fst (d r) <> PInf).
        { apply not_isbot_char in HdR.
          destruct (d r) as [rl ru]. cbn [fst snd] in *. tauto. }
        destruct (zstar_wlo_lo (fst (d r)) (tdvZ r p q d) M HxlP EZ HZlb Hnum)
          as [z [Hmz [Hz1 Hxlz]]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z MInf (Fin M) HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [_ Hycu]]]]]]].
        * apply zle_minf.
        * unfold Twin. unfold imeet. cbn [fst].
          apply zmax_lub; [exact HylM | exact Hxlz].
        * apply zle_minf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          rewrite Hpy. simpl in Hycu. exact Hycu.
      + intros M HM.
        assert (E := EYI). unfold tdvY, tnumP in E.
        unfold imeet in E. injection E as E1 E2.
        rewrite <- E2 in HM. cbn [fst snd] in HM.
        assert (HyuM : zle (Fin M) (snd (d p))).
        { eapply zle_trans; [exact HM | apply zmin_le_l]. }
        assert (Hnum : zle (Fin M)
                  (zmax (whiE (snd (d r)) (fst (tdvZ r p q d)))
                        (whiE (snd (d r)) (snd (tdvZ r p q d))))).
        { eapply zle_trans; [exact HM | apply zmin_le_r]. }
        assert (HxuM : snd (d r) <> MInf).
        { apply not_isbot_char in HdR.
          destruct (d r) as [rl ru]. cbn [fst snd] in *. tauto. }
        destruct (zstar_whi_hi (snd (d r)) (tdvZ r p q d) M HxuM EZ HZlb Hnum)
          as [z [Hmz [Hz1 Hhi]]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z (Fin M) PInf HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [Hycl _]]]]]]].
        * unfold Twin. unfold imeet. cbn [snd].
          apply zmin_glb; [exact HyuM | exact Hhi].
        * apply zle_pinf.
        * apply zle_pinf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          rewrite Hpy. simpl in Hycl. exact Hycl.
    - (* variable q: the interval tdvZ *)
      rewrite (vupd_other _ r _ q) by congruence.
      rewrite (vupd_other _ p _ q) by congruence.
      rewrite vupd_same.
      apply isle_bestR_of_wit.
      + intros M HM.
        destruct (mem_below (tdvZ r p q d) M EZ HM) as [z [Hmz HzM]].
        destruct (sol_of_z r p q Hrp Hrq Hpq d z HdR HdP Hmz)
          as [asn [Hb [HR Hqz]]].
        exists asn. split; [exact Hb|]. split; [exact HR|]. lia.
      + intros M HM.
        destruct (mem_above (tdvZ r p q d) M EZ HM) as [z [Hmz HzM]].
        destruct (sol_of_z r p q Hrp Hrq Hpq d z HdR HdP Hmz)
          as [asn [Hb [HR Hqz]]].
        exists asn. split; [exact Hb|]. split; [exact HR|]. lia.
  Qed.

  (* The tdiv⁺ propagator is the best propagator of its relation. *)
  Theorem prop_tdivp_best : forall d,
    eqI V3 (prop_tdivp r p q d) (bestR (Rtdp r p q) d).
  Proof.
    intros d. apply (ole_antisym (o := I_OSet V3)).
    - apply prop_tdivp_complete.
    - apply prop_tdivp_sound; assumption.
  Qed.

End TdivBest.

(* ==================== The simplified tdiv propagator ==================== *)

Section TdivSimpl.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  (* The appendix figure:
     I[x = tdiv(y,z)] = I[x=tdiv⁺(y,z)] ⊔̈ (zneg_xz ∘ I[x=tdiv⁺(y,z)] ∘ zneg_xz). *)
  Definition prop_tdiv_simpl (d : istore V3) : istore V3 :=
    sjoin (prop_tdivp r p q d)
          (sflip (flip2 r q) (prop_tdivp r p q (sflip (flip2 r q) d))).

  Lemma aflip_rq2 : forall a,
    aflip (flip2 r q) a r = (- a r)%Z /\
    aflip (flip2 r q) a p = a p /\
    aflip (flip2 r q) a q = (- a q)%Z.
  Proof.
    intros a. unfold aflip.
    rewrite (flip2_other r q p) by congruence.
    rewrite flip2_at_u, flip2_at_v. auto.
  Qed.

  (* Solution-set decomposition: tdiv splits on the sign of the divisor,
     using that truncated division is odd in the divisor. *)
  Lemma rel_tdiv_simpl_decomp : forall a,
    rel (MkC r p q OTdiv) a <->
    (Rtdp r p q a \/ Rtdp r p q (aflip (flip2 r q) a)).
  Proof.
    intros a. unfold rel, Rtdp. cbn [op_rel cop cx cy cz].
    destruct (aflip_rq2 a) as [Er [Ep Eq]]. rewrite Er, Ep, Eq.
    split.
    - intros [Hz Heq].
      destruct (Z_le_gt_dec 1 (a q)) as [Hq|Hq].
      + left. split; [lia | exact Heq].
      + right. split; [lia|].
        rewrite (tdivZ_opp_den (a p) (a q)) by lia. lia.
    - intros [[Hz Heq]|[Hz Heq]].
      + split; [lia | exact Heq].
      + rewrite (tdivZ_opp_den (a p) (a q)) in Heq by lia.
        split; [lia | lia].
  Qed.

  Theorem prop_tdiv_simpl_best : forall d,
    eqI V3 (prop_tdiv_simpl d) (bestI (MkC r p q OTdiv) d).
  Proof.
    intros d. unfold prop_tdiv_simpl.
    eapply eqI_trans3.
    - apply sjoin_proper.
      + apply prop_tdivp_best; assumption.
      + apply conj_best. intros d'. apply prop_tdivp_best; assumption.
    - eapply eqI_trans3.
      + apply eqI_sym3. apply bestR_union.
      + apply eqI_of_pointwise. intros w.
        rewrite bestI_is_bestR.
        apply bestR_ext. intros asn.
        pose proof (rel_tdiv_simpl_decomp asn). tauto.
  Qed.

End TdivSimpl.

(* ======================= CLAIM 21 ======================= *)
(* The simplified truncated-division propagator of the appendix is the best
   interval propagator of the constraint x = tdiv(y,z). *)
Theorem claim21 : forall d : istore V3,
  eqI V3 (prop_tdiv_simpl Vx Vy Vz d) (bestI (MkC Vx Vy Vz OTdiv) d).
Proof.
  intros d. apply prop_tdiv_simpl_best; congruence.
Qed.
