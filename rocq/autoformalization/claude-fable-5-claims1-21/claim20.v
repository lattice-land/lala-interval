(* ========================================================================= *)
(* Claim 20:                                                                 *)
(* "Using autoformalization, we obtained the Rocq proofs that all four       *)
(*  propagators are the best possible ones."                                 *)
(*                                                                           *)
(* The four division propagators of Figure VI:                               *)
(*   I[x = fdiv(y,z)] = I[x = fdiv⁺(y,z)] ⊔̈ (zneg_yz ∘ I[x=fdiv⁺] ∘ zneg_yz) *)
(*   I[x = cdiv(y,z)] = (zneg_xy ∘ I[x=fdiv⁺] ∘ zneg_xy) ⊔̈                   *)
(*                      (zneg_xz ∘ I[x=fdiv⁺] ∘ zneg_xz)                     *)
(*   I[x = ediv(y,z)] = I[x = fdiv⁺(y,z)] ⊔̈ (zneg_xz ∘ I[x=fdiv⁺] ∘ zneg_xz) *)
(*   I[x = tdiv(y,z)] = (I[x=fdiv⁺] ∘ pos_y) ⊔̈ ... (four sign quadrants)     *)
(* are all equal (in the quotient I) to the best interval propagators        *)
(* I[c] = αI ∘ S×[c] ∘ γI of their constraints.                              *)
(*                                                                           *)
(* Structure of the proof:                                                   *)
(*  1. The core propagator I[x = fdiv⁺(y,z)] (Figure V) is proved to be the  *)
(*     best propagator of the relation z ≥ 1 ∧ x = ⌊y/z⌋.                    *)
(*  2. Best propagators (w.r.t. arbitrary relations) decompose over unions   *)
(*     of relations as pointwise joins (α is a left adjoint), are preserved  *)
(*     under conjugation by sign flips, and turn pre-meets into relation     *)
(*     restrictions.                                                         *)
(*  3. The solution sets of the four divisions decompose accordingly.        *)
(* ========================================================================= *)

From Stdlib Require Import ZArith Lia Classical FunctionalExtensionality
  PropExtensionality.
From Paper Require Import claim1 claim2 claim3 claim4 claim8 claim9 claim10
  claim11 claim12 claim15 claim16.
Open Scope Z_scope.

(* ==================== Boolean tests on Z∞ ==================== *)

Definition zltb (a b : Zinf) : bool := negb (zleb b a).

Lemma zltb_lt : forall a b, zltb a b = true <-> zlt a b.
Proof.
  intros a b. unfold zltb. rewrite Bool.negb_true_iff. split.
  - intros H. apply znle_lt. intros Hc. apply zleb_le in Hc. congruence.
  - intros H. destruct (zleb b a) eqn:E; [|reflexivity].
    apply zleb_le in E. exfalso. exact (zlt_nle _ _ H E).
Qed.

Lemma zltb_false : forall a b, zltb a b = false <-> zle b a.
Proof.
  intros a b. split.
  - intros H. destruct (classic (zle b a)) as [Hc|Hc]; [exact Hc|].
    apply znle_lt in Hc. apply zltb_lt in Hc. congruence.
  - intros H. destruct (zltb a b) eqn:E; [|reflexivity].
    apply zltb_lt in E. exfalso. exact (zlt_nle _ _ E H).
Qed.

Definition zeqb (a b : Zinf) : bool :=
  match a, b with
  | MInf, MInf => true
  | PInf, PInf => true
  | Fin x, Fin y => x =? y
  | _, _ => false
  end.

Lemma zeqb_eq : forall a b, zeqb a b = true <-> a = b.
Proof.
  intros [|x|] [|y|]; simpl; split; try congruence.
  - intros H. apply Z.eqb_eq in H. congruence.
  - intros H. apply Z.eqb_eq. congruence.
Qed.

Lemma zeqb_neq : forall a b, zeqb a b = false <-> a <> b.
Proof.
  intros a b. split.
  - intros H Hc. apply zeqb_eq in Hc. congruence.
  - intros H. destruct (zeqb a b) eqn:E; [|reflexivity].
    apply zeqb_eq in E. congruence.
Qed.

(* ==================== Multiplication and division on Z∞ ==================== *)

(* Multiplication of Figure I: 0 is absorbing even against infinities. *)
Definition zmul (x y : Zinf) : Zinf :=
  match x, y with
  | Fin a, Fin b => Fin (a * b)
  | MInf, MInf => PInf
  | MInf, PInf => MInf
  | PInf, MInf => MInf
  | PInf, PInf => PInf
  | MInf, Fin b => if b =? 0 then Fin 0 else if 0 <? b then MInf else PInf
  | PInf, Fin b => if b =? 0 then Fin 0 else if 0 <? b then PInf else MInf
  | Fin a, MInf => if a =? 0 then Fin 0 else if 0 <? a then MInf else PInf
  | Fin a, PInf => if a =? 0 then Fin 0 else if 0 <? a then PInf else MInf
  end.

(* Floor division of Figure I (the divisor is never 0 in our usage). *)
Definition zfdiv (x y : Zinf) : Zinf :=
  match y with
  | PInf => match x with
            | MInf => Fin (-1)
            | Fin a => if a <? 0 then Fin (-1) else Fin 0
            | PInf => Fin 0
            end
  | MInf => match x with
            | PInf => Fin (-1)
            | Fin a => if 0 <? a then Fin (-1) else Fin 0
            | MInf => Fin 0
            end
  | Fin b => match x with
             | Fin a => Fin (fdivZ a b)
             | MInf => if 0 <? b then MInf else PInf
             | PInf => if 0 <? b then PInf else MInf
             end
  end.

(* Ceiling division: ⌈x/y⌉ = -⌊-x/y⌋. *)
Definition zcdiv (x y : Zinf) : Zinf := zneg (zfdiv (zneg x) y).

(* ==================== Integer division bound lemmas ==================== *)

(* The fundamental characterization of floor division by a positive
   divisor: q = ⌊y/z⌋ iff z·q ≤ y ≤ z·q + z - 1. *)
Lemma fdivZ_char : forall y z q,
  1 <= z -> (fdivZ y z = q <-> z * q <= y <= z * q + z - 1).
Proof.
  intros y z q Hz. unfold fdivZ. split.
  - intros <-. split.
    + apply Z.mul_div_le. lia.
    + pose proof (Z.mod_pos_bound y z ltac:(lia)) as Hm.
      pose proof (Z.div_mod y z ltac:(lia)) as He. lia.
  - intros [H1 H2]. symmetry. apply Z.div_unique_pos with (y - z * q); lia.
Qed.

Lemma fdivZ_char_refl : forall y z, 1 <= z ->
  z * fdivZ y z <= y <= z * fdivZ y z + z - 1.
Proof. intros y z Hz. apply fdivZ_char; [lia | reflexivity]. Qed.

Lemma fdivZ_lb : forall y z q, 1 <= z -> (q <= fdivZ y z <-> z * q <= y).
Proof.
  intros y z q Hz. split.
  - intros H. pose proof (fdivZ_char_refl y z Hz) as [Hc _].
    assert (z * q <= z * fdivZ y z) by nia. lia.
  - intros H. unfold fdivZ. apply Z.div_le_lower_bound; lia.
Qed.

Lemma fdivZ_ub : forall y z q, 1 <= z -> (fdivZ y z <= q <-> y <= z * q + z - 1).
Proof.
  intros y z q Hz. split.
  - intros H. pose proof (fdivZ_char_refl y z Hz) as [_ Hc].
    assert (z * fdivZ y z <= z * q) by nia. lia.
  - intros H. unfold fdivZ.
    assert (Hlt : y / z < q + 1) by (apply Z.div_lt_upper_bound; nia).
    lia.
Qed.

(* Bounds through a negative divisor, reduced to a positive one. *)
Lemma fdivZ_opp_opp : forall y z, z <> 0 -> fdivZ (- y) (- z) = fdivZ y z.
Proof. intros y z Hz. unfold fdivZ. apply Z.div_opp_opp. lia. Qed.

Lemma cdivZ_as_fdiv : forall y z, cdivZ y z = - fdivZ (- y) z.
Proof. reflexivity. Qed.

Lemma cdivZ_opp : forall y z, z <> 0 -> cdivZ y z = - fdivZ y (- z).
Proof.
  intros y z Hz. unfold cdivZ, fdivZ.
  f_equal. rewrite <- (Z.div_opp_opp y (- z)) by lia.
  f_equal. lia.
Qed.

(* Monotonicity of floor division. *)
Lemma fdivZ_mono_num : forall y y' z, 1 <= z -> y <= y' -> fdivZ y z <= fdivZ y' z.
Proof. intros y y' z Hz Hy. unfold fdivZ. apply Z.div_le_mono; lia. Qed.

(* Value of an interior point of a linear function lies between the values
   at the endpoints. *)
Lemma linear_between : forall c d zl zu z,
  zl <= z <= zu ->
  Z.min (c * zl + d) (c * zu + d) <= c * z + d <= Z.max (c * zl + d) (c * zu + d).
Proof.
  intros c d zl zu z [H1 H2].
  destruct (Z_le_gt_dec 0 c) as [Hc|Hc]; split.
  - eapply Z.le_trans; [apply Z.le_min_l | nia].
  - eapply Z.le_trans; [| apply Z.le_max_r]. nia.
  - eapply Z.le_trans; [apply Z.le_min_r | nia].
  - eapply Z.le_trans; [| apply Z.le_max_l]. nia.
Qed.

(* Truncated-division-style integer facts about fdivZ with negative and
   positive divisors. *)
Lemma fdivZ_antitone_div : forall y q r,
  0 <= y -> 0 < q <= r -> fdivZ y r <= fdivZ y q.
Proof. intros y q r Hy Hq. unfold fdivZ. apply Z.div_le_compat_l; lia. Qed.

Lemma fdivZ_monotone_div_neg : forall y q r,
  y < 0 -> 0 < q <= r -> fdivZ y q <= fdivZ y r.
Proof.
  intros y q r Hy Hq.
  assert (Hr : fdivZ y r <= -1).
  { apply fdivZ_ub; lia. }
  pose proof (fdivZ_char_refl y r ltac:(lia)) as [_ H2].
  apply fdivZ_ub; [lia|]. nia.
Qed.

(* cdivZ bound lemmas through a positive divisor. *)
Lemma cdivZ_le : forall w v q, 1 <= v -> (cdivZ w v <= q <-> w <= v * q).
Proof.
  intros w v q Hv. unfold cdivZ.
  rewrite Z.opp_le_mono, Z.opp_involutive.
  rewrite (fdivZ_lb (- w) v (- q) Hv). lia.
Qed.

Lemma cdivZ_ge : forall w v q, 1 <= v -> (q <= cdivZ w v <-> v * q <= w + v - 1).
Proof.
  intros w v q Hv. unfold cdivZ.
  rewrite Z.opp_le_mono, Z.opp_involutive.
  rewrite (fdivZ_ub (- w) v (- q) Hv).
  replace (v * - q) with (- (v * q)) by ring. lia.
Qed.


(* ==================== Z∞ arithmetic helper lemmas ==================== *)

(* Normal forms of zmul/zfdiv at positive finite arguments. *)
Lemma zmul_minf_pos : forall z : Z, 1 <= z -> zmul MInf (Fin z) = MInf.
Proof.
  intros z Hz. simpl. destruct (z =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? z) eqn:E2; [reflexivity|]. apply Z.ltb_ge in E2. lia.
Qed.

Lemma zmul_pinf_pos : forall z : Z, 1 <= z -> zmul PInf (Fin z) = PInf.
Proof.
  intros z Hz. simpl. destruct (z =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? z) eqn:E2; [reflexivity|]. apply Z.ltb_ge in E2. lia.
Qed.

Lemma zmul_fin_pinf_neg : forall a : Z, a < 0 -> zmul (Fin a) PInf = MInf.
Proof.
  intros a Ha. simpl. destruct (a =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? a) eqn:E2; [apply Z.ltb_lt in E2; lia | reflexivity].
Qed.

Lemma zmul_fin_pinf_pos : forall a : Z, 0 < a -> zmul (Fin a) PInf = PInf.
Proof.
  intros a Ha. simpl. destruct (a =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? a) eqn:E2; [reflexivity | apply Z.ltb_ge in E2; lia].
Qed.

Lemma zmul_fin_minf_neg : forall a : Z, a < 0 -> zmul (Fin a) MInf = PInf.
Proof.
  intros a Ha. simpl. destruct (a =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? a) eqn:E2; [apply Z.ltb_lt in E2; lia | reflexivity].
Qed.

Lemma zmul_fin_minf_pos : forall a : Z, 0 < a -> zmul (Fin a) MInf = MInf.
Proof.
  intros a Ha. simpl. destruct (a =? 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - destruct (0 <? a) eqn:E2; [reflexivity | apply Z.ltb_ge in E2; lia].
Qed.

Lemma zmul_fin0_l : forall w, zmul (Fin 0) w = Fin 0.
Proof. intros [|b|]; reflexivity. Qed.

Lemma zfdiv_minf_pos : forall z : Z, 1 <= z -> zfdiv MInf (Fin z) = MInf.
Proof.
  intros z Hz. simpl. destruct (0 <? z) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E. lia.
Qed.

Lemma zfdiv_pinf_pos : forall z : Z, 1 <= z -> zfdiv PInf (Fin z) = PInf.
Proof.
  intros z Hz. simpl. destruct (0 <? z) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E. lia.
Qed.

(* Monotonicity of zmul in its Z∞ argument. *)
Lemma zmul_mono_l_fin : forall l (x z : Z),
  zle l (Fin x) -> 1 <= z -> zle (zmul l (Fin z)) (Fin (x * z)).
Proof.
  intros [|a|] x z H Hz.
  - rewrite zmul_minf_pos by lia. exact I.
  - simpl in *. nia.
  - simpl in H. contradiction.
Qed.

Lemma zmul_mono_r_fin : forall u (x z : Z),
  zle (Fin x) u -> 1 <= z -> zle (Fin (x * z)) (zmul u (Fin z)).
Proof.
  intros [|b|] x z H Hz.
  - simpl in H. contradiction.
  - simpl in *. nia.
  - rewrite zmul_pinf_pos by lia. exact I.
Qed.

Lemma zmul_mono2 : forall l l' (z : Z),
  zle l l' -> 1 <= z -> zle (zmul l (Fin z)) (zmul l' (Fin z)).
Proof.
  intros [|a|] [|b|] z H Hz; simpl in H; try contradiction;
    try (rewrite zmul_minf_pos by lia); try (rewrite zmul_pinf_pos by lia);
    try exact I; simpl; nia.
Qed.

Lemma zmul_pinf_inv : forall l (z : Z),
  1 <= z -> zmul l (Fin z) = PInf -> l = PInf.
Proof.
  intros [|a|] z Hz H.
  - rewrite zmul_minf_pos in H by lia. discriminate.
  - simpl in H. discriminate.
  - reflexivity.
Qed.

Lemma zmul_minf_inv : forall l (z : Z),
  1 <= z -> zmul l (Fin z) = MInf -> l = MInf.
Proof.
  intros [|a|] z Hz H.
  - reflexivity.
  - simpl in H. discriminate.
  - rewrite zmul_pinf_pos in H by lia. discriminate.
Qed.

(* Successor and predecessor bounds. *)
Lemma zadd1_mono_l : forall l (x : Z),
  zle l (Fin x) -> zle (zadd l (Fin 1)) (Fin (x + 1)).
Proof. intros [|a|] x H; simpl in *; try tauto; lia. Qed.

Lemma zadd1_mono_r : forall u (x : Z),
  zle (Fin x) u -> zle (Fin (x + 1)) (zadd u (Fin 1)).
Proof. intros [|b|] x H; simpl in *; try tauto; lia. Qed.

Lemma zadd1_minf_inv : forall u, zadd u (Fin 1) = MInf -> u = MInf.
Proof. intros [|b|]; simpl; congruence. Qed.

Lemma zadd1_pinf_inv : forall u, zadd u (Fin 1) = PInf -> u = PInf.
Proof. intros [|b|]; simpl; congruence. Qed.

Lemma zle_sub1_of_add1 : forall l v,
  zle (zadd l (Fin 1)) v -> zle l (zsub v (Fin 1)).
Proof. intros [|a|] [|b|] H; simpl in *; try tauto; lia. Qed.

Lemma zadd1_le_of_sub1 : forall l v,
  zle l (zsub v (Fin 1)) -> zle (zadd l (Fin 1)) v.
Proof. intros [|a|] [|b|] H; simpl in *; try tauto; lia. Qed.

Lemma zsub1_minf_inv : forall v, zsub v (Fin 1) = MInf -> v = MInf.
Proof. intros [|b|]; simpl; congruence. Qed.

Lemma zsub1_mono : forall u v, zle u v -> zle (zsub u (Fin 1)) (zsub v (Fin 1)).
Proof. intros [|a|] [|b|] H; simpl in *; try tauto; lia. Qed.

Lemma zmul_succ_ge : forall u (z : Z),
  1 <= z ->
  zle (zmul u (Fin z)) (zsub (zmul (zadd u (Fin 1)) (Fin z)) (Fin 1)).
Proof.
  intros [|b|] z Hz.
  - cbn [zadd]. rewrite !zmul_minf_pos by lia. simpl. exact I.
  - simpl. nia.
  - cbn [zadd]. rewrite !zmul_pinf_pos by lia. simpl. exact I.
Qed.

(* Bridging zmul bounds and floor division. *)
Lemma zmul_le_fdiv : forall l (y z : Z),
  1 <= z -> zle (zmul l (Fin z)) (Fin y) -> zle l (Fin (fdivZ y z)).
Proof.
  intros [|a|] y z Hz H.
  - exact I.
  - simpl in *. apply fdivZ_lb; nia.
  - rewrite zmul_pinf_pos in H by lia. simpl in H. contradiction.
Qed.

Lemma fdiv_le_zmul : forall u (y z : Z),
  1 <= z ->
  zle (Fin y) (zsub (zmul (zadd u (Fin 1)) (Fin z)) (Fin 1)) ->
  zle (Fin (fdivZ y z)) u.
Proof.
  intros [|b|] y z Hz H.
  - cbn [zadd] in H. rewrite zmul_minf_pos in H by lia. simpl in H. contradiction.
  - simpl in H. simpl. apply fdivZ_ub; nia.
  - exact I.
Qed.

(* Corner bounds: the product of a bound c by any positive z inside [zl,zu]
   lies between the two corner products. *)
Lemma zmul_corner_lb : forall c zl zu (z : Z),
  1 <= z -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (zmin (zmul c zl) (zmul c zu)) (zmul c (Fin z)).
Proof.
  intros c zl zu z Hz H1 H2.
  destruct c as [|a|].
  - (* c = -inf *)
    rewrite zmul_minf_pos by lia.
    eapply zle_trans; [apply zmin_le_r|].
    destruct zu as [|u|].
    + simpl in H2. contradiction.
    + simpl in H2. rewrite zmul_minf_pos by lia. exact I.
    + simpl. exact I.
  - destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
    + (* a < 0: antitone, the zu corner is below *)
      eapply zle_trans; [apply zmin_le_r|].
      destruct zu as [|u|].
      * simpl in H2. contradiction.
      * simpl in *. nia.
      * rewrite zmul_fin_pinf_neg by lia. exact I.
    + (* a = 0 *)
      subst a. rewrite !zmul_fin0_l.
      eapply zle_trans; [apply zmin_le_l|].
      destruct zl as [|l|]; rewrite ?zmul_fin0_l; simpl; try exact I; lia.
    + (* a > 0: monotone, the zl corner is below *)
      eapply zle_trans; [apply zmin_le_l|].
      destruct zl as [|l|].
      * rewrite zmul_fin_minf_pos by lia. exact I.
      * simpl in *. nia.
      * simpl in H1. contradiction.
  - (* c = +inf *)
    rewrite zmul_pinf_pos by lia.
    destruct (zmin (zmul PInf zl) (zmul PInf zu)); exact I.
Qed.

Lemma zmul_corner_ub : forall c zl zu (z : Z),
  1 <= z -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (zmul c (Fin z)) (zmax (zmul c zl) (zmul c zu)).
Proof.
  intros c zl zu z Hz H1 H2.
  destruct c as [|a|].
  - rewrite zmul_minf_pos by lia.
    destruct (zmax (zmul MInf zl) (zmul MInf zu)); exact I.
  - destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
    + (* a < 0: the zl corner is above *)
      eapply zle_trans; [|apply zmax_ge_l].
      destruct zl as [|l|].
      * rewrite zmul_fin_minf_neg by lia. exact I.
      * simpl in *. nia.
      * simpl in H1. contradiction.
    + subst a. rewrite !zmul_fin0_l.
      eapply zle_trans; [|apply zmax_ge_l].
      destruct zl as [|l|]; rewrite ?zmul_fin0_l; simpl; try exact I; lia.
    + (* a > 0: the zu corner is above *)
      eapply zle_trans; [|apply zmax_ge_r].
      destruct zu as [|u|].
      * simpl in H2. contradiction.
      * simpl in *. nia.
      * rewrite zmul_fin_pinf_pos by lia. exact I.
  - rewrite zmul_pinf_pos by lia.
    eapply zle_trans; [|apply zmax_ge_r].
    destruct zu as [|u|].
    + simpl in H2. contradiction.
    + simpl in H2. rewrite zmul_pinf_pos by lia. exact I.
    + simpl. exact I.
Qed.

(* Monotonicity of Z∞ floor division in the numerator. *)
Lemma zfdiv_mono_y : forall w w' v,
  zle (Fin 1) v -> zle w w' -> zle (zfdiv w v) (zfdiv w' v).
Proof.
  intros w w' [|c|] Hv H; simpl in Hv; [contradiction| |].
  - (* v = Fin c with 1 <= c *)
    destruct w as [|a|]; destruct w' as [|b|]; simpl in H; try contradiction.
    + rewrite zfdiv_minf_pos by lia. exact I.
    + rewrite zfdiv_minf_pos by lia. exact I.
    + rewrite zfdiv_minf_pos by lia. exact I.
    + simpl. apply fdivZ_mono_num; lia.
    + rewrite zfdiv_pinf_pos by lia. exact I.
    + rewrite zfdiv_pinf_pos by lia. exact I.
  - (* v = +inf *)
    destruct w as [|a|]; destruct w' as [|b|]; simpl in H; try contradiction;
      simpl;
      try (destruct (a <? 0) eqn:Ea);
      try (destruct (b <? 0) eqn:Eb);
      simpl;
      repeat match goal with
      | E : (_ <? _) = true |- _ => apply Z.ltb_lt in E
      | E : (_ <? _) = false |- _ => apply Z.ltb_ge in E
      end; lia.
Qed.

(* Corner bounds for Z∞ floor division of a finite numerator by a positive
   interval of divisors. *)
Lemma zfdiv_corner_lb : forall (y : Z) zl zu (z : Z),
  1 <= z -> zle (Fin 1) zl -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (zmin (zfdiv (Fin y) zl) (zfdiv (Fin y) zu)) (Fin (fdivZ y z)).
Proof.
  intros y [|l|] [|u|] z Hz H0 H1 H2; simpl in H0, H1, H2; try contradiction.
  - (* zl = Fin l, zu = Fin u *)
    destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [apply zmin_le_r|]. simpl.
      apply fdivZ_antitone_div; lia.
    + eapply zle_trans; [apply zmin_le_l|]. simpl.
      apply fdivZ_monotone_div_neg; lia.
  - (* zl = Fin l, zu = +inf *)
    destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [apply zmin_le_r|]. simpl.
      destruct (y <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
      simpl. apply fdivZ_lb; lia.
    + eapply zle_trans; [apply zmin_le_l|]. simpl.
      apply fdivZ_monotone_div_neg; lia.
Qed.

Lemma zfdiv_corner_ub : forall (y : Z) zl zu (z : Z),
  1 <= z -> zle (Fin 1) zl -> zle zl (Fin z) -> zle (Fin z) zu ->
  zle (Fin (fdivZ y z)) (zmax (zfdiv (Fin y) zl) (zfdiv (Fin y) zu)).
Proof.
  intros y [|l|] [|u|] z Hz H0 H1 H2; simpl in H0, H1, H2; try contradiction.
  - destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [|apply zmax_ge_l]. simpl.
      apply fdivZ_antitone_div; lia.
    + eapply zle_trans; [|apply zmax_ge_r]. simpl.
      apply fdivZ_monotone_div_neg; lia.
  - destruct (Z_le_gt_dec 0 y) as [Hy|Hy].
    + eapply zle_trans; [|apply zmax_ge_l]. simpl.
      apply fdivZ_antitone_div; lia.
    + eapply zle_trans; [|apply zmax_ge_r]. simpl.
      destruct (y <? 0) eqn:E; [|apply Z.ltb_ge in E; lia].
      simpl. apply fdivZ_ub; lia.
Qed.

(* Trivial order facts used everywhere below. *)
Lemma zle_pinf : forall w, zle w PInf.
Proof. intros [|a|]; simpl; exact I. Qed.

Lemma zle_minf : forall w, zle MInf w.
Proof. intros w; simpl; exact I. Qed.

Lemma imem_pair : forall v l u, imem v (l, u) <-> (zle l (Fin v) /\ zle (Fin v) u).
Proof. intros. unfold imem. cbn [fst snd]. tauto. Qed.

(* More characterizations of integer division bounds with negative divisors. *)
Lemma cdivZ_le_neg : forall b a z, a < 0 -> (cdivZ b a <= z <-> a * z <= b).
Proof.
  intros b a z Ha. rewrite (cdivZ_opp b a) by lia.
  pose proof (fdivZ_lb b (- a) (- z) ltac:(lia)) as H.
  replace (- a * - z) with (a * z) in H by ring. lia.
Qed.

Lemma fdivZ_le_neg : forall w v z, v < 0 -> (z <= fdivZ w v <-> w <= v * z).
Proof.
  intros w v z Hv. rewrite <- (fdivZ_opp_opp w v) by lia.
  pose proof (fdivZ_lb (- w) (- v) z ltac:(lia)) as H.
  replace (- v * z) with (- (v * z)) in H by ring. lia.
Qed.

(* Ceiling division by an infinite divisor is always at most any z ≥ 1. *)
Lemma zcdiv_minf_le : forall yu (z : Z), 1 <= z -> zle (zcdiv yu MInf) (Fin z).
Proof.
  intros [|b|] z Hz; unfold zcdiv; simpl.
  - lia.
  - destruct (0 <? - b) eqn:E; simpl; lia.
  - lia.
Qed.

Lemma zcdiv_pinf_le : forall w (z : Z), 1 <= z -> zle (zcdiv w PInf) (Fin z).
Proof.
  intros [|c|] z Hz; unfold zcdiv; simpl.
  - lia.
  - destruct (- c <? 0) eqn:E; simpl; lia.
  - lia.
Qed.

(* ==================== The fdiv⁺ propagator (Figure V) ==================== *)

(* First phase of fden⁺: enforce xl·z ≤ yu on z ∈ [1,∞]. *)
Definition fdenP1 (xl yu : Zinf) : Itv :=
  if zltb (Fin 0) xl then imeet (Fin 1, PInf) (MInf, zfdiv yu xl)
  else if negb (zeqb xl (Fin 0)) then imeet (Fin 1, PInf) (zcdiv yu xl, PInf)
  else if zltb yu (Fin 0) then (PInf, MInf)
  else (Fin 1, PInf).

(* Second phase of fden⁺: enforce (xu+1)·z ≥ yl+1. *)
Definition fdenP2 (xu yl : Zinf) (z1 : Itv) : Itv :=
  if zltb (Fin (-1)) xu
    then imeet z1 (zcdiv (zadd yl (Fin 1)) (zadd xu (Fin 1)), PInf)
  else if negb (zeqb xu (Fin (-1)))
    then imeet z1 (MInf, zfdiv (zadd yl (Fin 1)) (zadd xu (Fin 1)))
  else if zleb (Fin 0) yl then (PInf, MInf)
  else z1.

Definition fdenP (Xi Yi : Itv) : Itv :=
  fdenP2 (snd Xi) (fst Yi) (fdenP1 (fst Xi) (snd Yi)).

(* fnum⁺: hull of [xl·z, (xu+1)·z - 1] over z in Zi. *)
Definition fnumP (Xi Zi : Itv) : Itv :=
  (zmin (zmul (fst Xi) (fst Zi)) (zmul (fst Xi) (snd Zi)),
   zmax (zsub (zmul (zadd (snd Xi) (Fin 1)) (fst Zi)) (Fin 1))
        (zsub (zmul (zadd (snd Xi) (Fin 1)) (snd Zi)) (Fin 1))).

(* Forward fdiv⁺: hull of the four corner divisions. *)
Definition ffwdP (Yi Zi : Itv) : Itv :=
  (zmin (zmin (zfdiv (fst Yi) (fst Zi)) (zfdiv (fst Yi) (snd Zi)))
        (zmin (zfdiv (snd Yi) (fst Zi)) (zfdiv (snd Yi) (snd Zi))),
   zmax (zmax (zfdiv (fst Yi) (fst Zi)) (zfdiv (fst Yi) (snd Zi)))
        (zmax (zfdiv (snd Yi) (fst Zi)) (zfdiv (snd Yi) (snd Zi)))).

(* ---------- Membership characterization of fden⁺ ---------- *)

Lemma fdenP1_mem : forall xl yu (z : Z),
  xl <> PInf -> yu <> MInf ->
  (imem z (fdenP1 xl yu) <->
   (1 <= z /\ zle (zmul xl (Fin z)) yu)).
Proof.
  intros xl yu z HX HY. unfold fdenP1.
  destruct xl as [|a|]; [| |congruence].
  - (* xl = -inf: no constraint beyond z >= 1 *)
    change (zltb (Fin 0) MInf) with false.
    change (negb (zeqb MInf (Fin 0))) with true.
    rewrite imem_imeet, !imem_pair. split.
    + intros [[H1 _] _]. simpl in H1. split; [lia|].
      rewrite zmul_minf_pos by (simpl in H1; lia). apply zle_minf.
    + intros [Hz _]. repeat split; simpl; try lia; try apply zle_pinf.
      apply zcdiv_minf_le. exact Hz.
  - (* xl = Fin a *)
    destruct (Z.lt_trichotomy 0 a) as [Ha|[Ha|Ha]].
    + (* a > 0 *)
      assert (E1 : zltb (Fin 0) (Fin a) = true) by (apply zltb_lt; simpl; lia).
      rewrite E1. rewrite imem_imeet, !imem_pair. split.
      * intros [[H1 _] [_ H4]]. simpl in H1. split; [lia|].
        destruct yu as [|b|]; [congruence| |].
        -- simpl in H4. simpl. apply fdivZ_lb in H4; [|lia]. nia.
        -- apply zle_pinf.
      * intros [Hz HC]. repeat split; simpl; try lia; try apply zle_pinf;
          try apply zle_minf.
        destruct yu as [|b|]; [congruence| |].
        -- simpl in HC. simpl. apply fdivZ_lb; [lia|]. nia.
        -- destruct (0 <? a) eqn:E3; simpl;
             [exact I | apply Z.ltb_ge in E3; lia].
    + (* a = 0 *)
      subst a.
      change (zltb (Fin 0) (Fin 0)) with false.
      change (negb (zeqb (Fin 0) (Fin 0))) with false.
      destruct yu as [|b|]; [congruence| |].
      * destruct (zltb (Fin b) (Fin 0)) eqn:Eb.
        -- apply zltb_lt in Eb. simpl in Eb.
           rewrite imem_pair. split.
           ++ intros [H1 H2]. simpl in *. lia.
           ++ intros [Hz HC]. simpl in HC. lia.
        -- apply zltb_false in Eb. simpl in Eb.
           rewrite imem_pair. split.
           ++ intros [H1 H2]. simpl in *. split; [lia|]. simpl. lia.
           ++ intros [Hz HC]. split; simpl; [lia | exact I].
      * change (zltb PInf (Fin 0)) with false.
        rewrite imem_pair. split.
        -- intros [H1 H2]. simpl in H1. split; [lia | apply zle_pinf].
        -- intros [Hz _]. split; simpl; [lia | exact I].
    + (* a < 0 *)
      assert (E1 : zltb (Fin 0) (Fin a) = false) by (apply zltb_false; simpl; lia).
      assert (E2 : zeqb (Fin a) (Fin 0) = false)
        by (apply zeqb_neq; intros Hc; injection Hc; lia).
      rewrite E1, E2. simpl negb.
      rewrite imem_imeet, !imem_pair. split.
      * intros [[H1 _] [H3 _]]. simpl in H1. split; [lia|].
        destruct yu as [|b|]; [congruence| |].
        -- exact (proj1 (cdivZ_le_neg b a z ltac:(lia)) H3).
        -- apply zle_pinf.
      * intros [Hz HC]. repeat split; simpl; try lia; try apply zle_pinf.
        destruct yu as [|b|]; [congruence| |].
        -- exact (proj2 (cdivZ_le_neg b a z ltac:(lia)) HC).
        -- unfold zcdiv. simpl.
           destruct (0 <? a) eqn:E3; [apply Z.ltb_lt in E3; lia|]. simpl. exact I.
Qed.

Lemma fdenP2_z1 : forall xu yl z1 (z : Z),
  imem z (fdenP2 xu yl z1) -> imem z z1.
Proof.
  intros xu yl z1 z H. unfold fdenP2 in H.
  destruct (zltb (Fin (-1)) xu).
  - apply imem_imeet in H. tauto.
  - destruct (negb (zeqb xu (Fin (-1)))).
    + apply imem_imeet in H. tauto.
    + destruct (zleb (Fin 0) yl); [|exact H].
      exfalso. eapply isbot_no_mem; [|exact H].
      right; left; reflexivity.
Qed.

Lemma fdenP2_mem : forall xu yl z1 (z : Z),
  xu <> MInf -> yl <> PInf -> 1 <= z ->
  (imem z (fdenP2 xu yl z1) <->
   (imem z z1 /\
    zle (zadd yl (Fin 1)) (zmul (zadd xu (Fin 1)) (Fin z)))).
Proof.
  intros xu yl z1 z HX HY Hz. unfold fdenP2.
  destruct xu as [|b|]; [congruence| |].
  - (* xu = Fin b *)
    destruct (Z.lt_trichotomy (-1) b) as [Hb|[Hb|Hb]].
    + (* b > -1 *)
      assert (E1 : zltb (Fin (-1)) (Fin b) = true) by (apply zltb_lt; simpl; lia).
      rewrite E1. rewrite imem_imeet, imem_pair.
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
           exact (proj1 (cdivZ_le (c + 1) (b + 1) z ltac:(lia)) H3).
        -- intros [H1 HC]. split; [exact H1|]. split; [|apply zle_pinf].
           exact (proj2 (cdivZ_le (c + 1) (b + 1) z ltac:(lia)) HC).
    + (* b = -1 *)
      subst b.
      change (zltb (Fin (-1)) (Fin (-1))) with false.
      change (negb (zeqb (Fin (-1)) (Fin (-1)))) with false.
      destruct yl as [|c|]; [| | congruence].
      * change (zleb (Fin 0) MInf) with false. split.
        -- intros H1. split; [exact H1 | apply zle_minf].
        -- intros [H1 _]. exact H1.
      * destruct (zleb (Fin 0) (Fin c)) eqn:Ec.
        -- apply zleb_le in Ec. simpl in Ec.
           split.
           ++ intros [H1 _]. simpl in H1. contradiction.
           ++ intros [_ HC]. cbn [zadd] in HC.
              rewrite zmul_fin0_l in HC. simpl in HC. lia.
        -- assert (Hc : c < 0).
           { destruct (Z_le_gt_dec 0 c) as [Hc|Hc]; [|lia].
             assert (zleb (Fin 0) (Fin c) = true) by (apply zleb_le; simpl; lia).
             congruence. }
           split.
           ++ intros H1. split; [exact H1|].
              cbn [zadd]. rewrite zmul_fin0_l. simpl. lia.
           ++ intros [H1 _]. exact H1.
    + (* b < -1 *)
      assert (E1 : zltb (Fin (-1)) (Fin b) = false)
        by (apply zltb_false; simpl; lia).
      assert (E2 : zeqb (Fin b) (Fin (-1)) = false)
        by (apply zeqb_neq; intros Hc; injection Hc; lia).
      rewrite E1, E2. simpl negb.
      rewrite imem_imeet, imem_pair.
      destruct yl as [|c|]; [| | congruence].
      * split.
        -- intros [H1 _]. split; [exact H1 | apply zle_minf].
        -- intros [H1 _]. split; [exact H1|]. split; [apply zle_minf|].
           cbn [zadd]. simpl.
           destruct (0 <? b + 1) eqn:E3; [apply Z.ltb_lt in E3; lia|].
           simpl. exact I.
      * split.
        -- intros [H1 [_ H4]]. split; [exact H1|].
           exact (proj1 (fdivZ_le_neg (c + 1) (b + 1) z ltac:(lia)) H4).
        -- intros [H1 HC]. split; [exact H1|]. split; [apply zle_minf|].
           exact (proj2 (fdivZ_le_neg (c + 1) (b + 1) z ltac:(lia)) HC).
  - (* xu = +inf *)
    change (zltb (Fin (-1)) PInf) with true.
    rewrite imem_imeet, imem_pair.
    split.
    + intros [H1 _]. split; [exact H1|].
      cbn [zadd]. rewrite zmul_pinf_pos by lia. apply zle_pinf.
    + intros [H1 _]. split; [exact H1|]. split; [|apply zle_pinf].
      cbn [zadd]. apply zcdiv_pinf_le. exact Hz.
Qed.

(* The complete membership characterization of fden⁺:
   z belongs iff z ≥ 1, xl·z ≤ yu and yl+1 ≤ (xu+1)·z. *)
Lemma fdenP_mem : forall Xi Yi (z : Z),
  ~ isbot Xi -> ~ isbot Yi ->
  (imem z (fdenP Xi Yi) <->
   (1 <= z /\
    zle (zmul (fst Xi) (Fin z)) (snd Yi) /\
    zle (zadd (fst Yi) (Fin 1)) (zmul (zadd (snd Xi) (Fin 1)) (Fin z)))).
Proof.
  intros [xl xu] [yl yu] z HX HY.
  apply not_isbot_char in HX. destruct HX as [HX1 [HX2 HX3]].
  apply not_isbot_char in HY. destruct HY as [HY1 [HY2 HY3]].
  unfold fdenP. cbn [fst snd].
  split.
  - intros H.
    pose proof (fdenP2_z1 _ _ _ _ H) as Hz1.
    apply fdenP1_mem in Hz1; [|exact HX2|exact HY3].
    destruct Hz1 as [Hz HC1].
    apply fdenP2_mem in H; [|exact HX3|exact HY2|exact Hz].
    destruct H as [_ HC2]. auto.
  - intros [Hz [HC1 HC2]].
    apply fdenP2_mem; [exact HX3|exact HY2|exact Hz|].
    split; [|exact HC2].
    apply fdenP1_mem; [exact HX2|exact HY3|]. auto.
Qed.

(* Lower bound 1 on the fden⁺ output. *)
Lemma fdenP1_lb1 : forall xl yu, zle (Fin 1) (fst (fdenP1 xl yu)).
Proof.
  intros xl yu. unfold fdenP1.
  destruct (zltb (Fin 0) xl).
  - cbn [imeet fst]. apply zmax_ge_l.
  - destruct (negb (zeqb xl (Fin 0))).
    + cbn [imeet fst]. apply zmax_ge_l.
    + destruct (zltb yu (Fin 0)); simpl; [exact I | lia].
Qed.

Lemma fdenP_lb1 : forall Xi Yi, zle (Fin 1) (fst (fdenP Xi Yi)).
Proof.
  intros Xi Yi. unfold fdenP, fdenP2.
  destruct (zltb (Fin (-1)) (snd Xi)).
  - cbn [imeet fst]. eapply zle_trans; [apply fdenP1_lb1 | apply zmax_ge_l].
  - destruct (negb (zeqb (snd Xi) (Fin (-1)))).
    + cbn [imeet fst]. eapply zle_trans; [apply fdenP1_lb1 | apply zmax_ge_l].
    + destruct (zleb (Fin 0) (fst Yi)); simpl; [exact I | apply fdenP1_lb1].
Qed.

(* max/min through predecessor. *)
Lemma zsub1_le_zmax : forall A B,
  zle (zsub (zmax A B) (Fin 1)) (zmax (zsub A (Fin 1)) (zsub B (Fin 1))).
Proof.
  intros A B. destruct (zmax_case A B) as [[E _]|[E _]]; rewrite E.
  - apply zmax_ge_r.
  - apply zmax_ge_l.
Qed.

Lemma zmin_le_zsub1 : forall A B,
  zle (zmin (zsub A (Fin 1)) (zsub B (Fin 1))) (zsub (zmin A B) (Fin 1)).
Proof.
  intros A B. destruct (zmin_case A B) as [[E _]|[E _]]; rewrite E.
  - apply zmin_le_l.
  - apply zmin_le_r.
Qed.

(* ==================== Best propagators for arbitrary relations ============ *)

Section BestR.
  Context {X : Type}.

  Definition bestR (R : powerset (Asn X)) (d : istore X) : istore X :=
    ihull (inter (ibox d) R).

  Lemma bestI_is_bestR : forall (c : constraint X) d,
    bestI c d = bestR (rel c) d.
  Proof. reflexivity. Qed.

  Lemma sol_in_bestR : forall R d asn,
    ibox d asn -> R asn -> forall w, imem (asn w) (bestR R d w).
  Proof.
    intros R d asn Hb HR w. unfold bestR, ihull, alphai. split; cbn [fst snd].
    - apply zinfS_lb. exists (asn w). split; [|reflexivity].
      exists asn. split; [split; assumption | reflexivity].
    - apply zsup_ub. exists (asn w). split; [|reflexivity].
      exists asn. split; [split; assumption | reflexivity].
  Qed.

  Lemma no_sol_bestR_bot : forall R d (x0 : X),
    (forall asn, ibox d asn -> ~ R asn) -> isbotI X (bestR R d).
  Proof.
    intros R d x0 Hno. exists x0. unfold bestR, ihull.
    apply alphai_bot_of_empty. intros v [asn [[Hb HR] _]].
    exact (Hno asn Hb HR).
  Qed.

  Lemma sols_preserved_sound_R :
    forall (R : powerset (Asn X)) (x0 : X) (e : istore X) (d : istore X),
      (forall asn, ibox d asn -> R asn -> forall w, imem (asn w) (e w)) ->
      leI X (bestR R d) e.
  Proof.
    intros R x0 e d Hpres.
    destruct (classic (exists asn, ibox d asn /\ R asn)) as [[asn0 [Hb0 HR0]]|Hno].
    - right. intros w. right.
      unfold bestR, ihull, alphai. split; cbn [fst snd].
      + apply zinfS_greatest. intros v' [v [[asn [[Hb HR] Hv]] Heq]].
        subst v' v. destruct (Hpres asn Hb HR w) as [H1 _]. exact H1.
      + apply zsup_least. intros v' [v [[asn [[Hb HR] Hv]] Heq]].
        subst v' v. destruct (Hpres asn Hb HR w) as [_ H2]. exact H2.
    - left. apply (no_sol_bestR_bot R d x0).
      intros asn Hb HR. apply Hno. eauto.
  Qed.

  Lemma isle_bestR_of_wit :
    forall (R : powerset (Asn X)) (d : istore X) (i : Itv) (w : X),
      (forall M : Z, zle (fst i) (Fin M) ->
         exists asn, ibox d asn /\ R asn /\ (asn w <= M)%Z) ->
      (forall M : Z, zle (Fin M) (snd i) ->
         exists asn, ibox d asn /\ R asn /\ (M <= asn w)%Z) ->
      isle i (bestR R d w).
  Proof.
    intros R d i w Hlo Hhi. right.
    unfold bestR, ihull, alphai. split; cbn [fst snd].
    - apply zinf_le_of_wit. intros M HM.
      destruct (Hlo M HM) as [asn [Hb [HR Hle]]].
      exists (asn w). split; [|exact Hle].
      exists asn. split; [split; assumption | reflexivity].
    - apply zsup_ge_of_wit. intros M HM.
      destruct (Hhi M HM) as [asn [Hb [HR Hle]]].
      exists (asn w). split; [|exact Hle].
      exists asn. split; [split; assumption | reflexivity].
  Qed.

  (* Best propagators only depend on the solution set inside the box. *)
  Lemma bestR_ext : forall (R R' : powerset (Asn X)) (d d' : istore X),
    (forall asn, (ibox d asn /\ R asn) <-> (ibox d' asn /\ R' asn)) ->
    forall w, bestR R d w = bestR R' d' w.
  Proof.
    intros R R' d d' Hiff w.
    unfold bestR, ihull, alphai.
    assert (Hset : forall v,
      (exists asn, (ibox d asn /\ R asn) /\ asn w = v)
      <-> (exists asn, (ibox d' asn /\ R' asn) /\ asn w = v)).
    { intros v. split; intros [asn [Hs Hv]]; exists asn;
        (split; [apply Hiff; exact Hs | exact Hv]). }
    f_equal.
    - apply zle_antisym; apply zinfS_greatest; intros x [v [Hv Heq]]; subst;
        apply zinfS_lb; exists v; (split; [apply Hset; exact Hv | reflexivity]).
    - apply zle_antisym; apply zsup_least; intros x [v [Hv Heq]]; subst;
        apply zsup_ub; exists v; (split; [apply Hset; exact Hv | reflexivity]).
  Qed.

End BestR.

(* ==================== The fdiv⁺ propagator over V3 ==================== *)

Section FdivPropagator.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  (* The relation of the constraint x = fdiv⁺(y,z):  z ≥ 1 ∧ x = ⌊y/z⌋. *)
  Definition Rfdp (a : Asn V3) : Prop := 1 <= a q /\ a r = fdivZ (a p) (a q).

  (* The three successive refinements of Figure V. *)
  Definition divZ (d : istore V3) : Itv := imeet (d q) (fdenP (d r) (d p)).
  Definition divY (d : istore V3) : Itv := imeet (d p) (fnumP (d r) (divZ d)).
  Definition divX (d : istore V3) : Itv := imeet (d r) (ffwdP (divY d) (divZ d)).

  Definition prop_fdivp (d : istore V3) : istore V3 :=
    if isbotb (divZ d) then vupd d q (divZ d)
    else if isbotb (divY d) then vupd (vupd d q (divZ d)) p (divY d)
    else vupd (vupd (vupd d q (divZ d)) p (divY d)) r (divX d).

  Lemma divZ_lb1 : forall d, zle (Fin 1) (fst (divZ d)).
  Proof.
    intros d. unfold divZ. cbn [imeet fst].
    eapply zle_trans; [apply fdenP_lb1 | apply zmax_ge_r].
  Qed.

  (* --------- Solutions are preserved by the three refinements --------- *)

  Lemma sol_mem_divZ : forall d asn,
    ibox d asn -> Rfdp asn -> imem (asn q) (divZ d).
  Proof.
    intros d asn Hbox [Hq Hr].
    pose proof (fdivZ_char_refl (asn p) (asn q) Hq) as [Hc1 Hc2].
    apply imem_imeet. split; [apply Hbox|].
    apply fdenP_mem.
    - exact (imem_not_isbot _ _ (Hbox r)).
    - exact (imem_not_isbot _ _ (Hbox p)).
    - split; [exact Hq|]. split.
      + (* xl·z ≤ yu *)
        eapply zle_trans.
        * apply (zmul_mono_l_fin (fst (d r)) (asn r) (asn q));
            [apply (Hbox r) | exact Hq].
        * eapply zle_trans; [|apply (Hbox p)].
          simpl. nia.
      + (* yl+1 ≤ (xu+1)·z *)
        eapply zle_trans.
        * apply (zadd1_mono_l (fst (d p)) (asn p)). apply (Hbox p).
        * eapply zle_trans;
            [|apply (zmul_mono_r_fin (zadd (snd (d r)) (Fin 1)) (asn r + 1) (asn q));
              [apply zadd1_mono_r, (Hbox r) | exact Hq]].
          simpl. nia.
  Qed.

  Lemma sol_mem_divY : forall d asn,
    ibox d asn -> Rfdp asn -> imem (asn p) (divY d).
  Proof.
    intros d asn Hbox HR.
    pose proof (sol_mem_divZ d asn Hbox HR) as [HZ1 HZ2].
    destruct HR as [Hq Hr].
    pose proof (fdivZ_char_refl (asn p) (asn q) Hq) as [Hc1 Hc2].
    apply imem_imeet. split; [apply Hbox|].
    unfold fnumP. apply imem_pair. split.
    - (* lower corner ≤ y *)
      eapply zle_trans.
      + apply (zmul_corner_lb (fst (d r)) (fst (divZ d)) (snd (divZ d)) (asn q));
          [exact Hq | exact HZ1 | exact HZ2].
      + eapply zle_trans.
        * apply (zmul_mono_l_fin (fst (d r)) (asn r) (asn q));
            [apply (Hbox r) | exact Hq].
        * simpl. nia.
    - (* y ≤ upper corner *)
      eapply zle_trans;
        [| eapply zle_trans;
           [apply (zsub1_mono (zmul (zadd (snd (d r)) (Fin 1)) (Fin (asn q)))
                              (zmax (zmul (zadd (snd (d r)) (Fin 1)) (fst (divZ d)))
                                    (zmul (zadd (snd (d r)) (Fin 1)) (snd (divZ d)))))
           | apply zsub1_le_zmax]].
      + eapply zle_trans;
          [| apply (zsub1_mono (Fin ((asn r + 1) * asn q)))].
        * simpl. nia.
        * apply (zmul_mono_r_fin (zadd (snd (d r)) (Fin 1)) (asn r + 1) (asn q));
            [apply zadd1_mono_r, (Hbox r) | exact Hq].
      + apply (zmul_corner_ub (zadd (snd (d r)) (Fin 1))
                 (fst (divZ d)) (snd (divZ d)) (asn q));
          [exact Hq | exact HZ1 | exact HZ2].
  Qed.

  Lemma sol_mem_divX : forall d asn,
    ibox d asn -> Rfdp asn -> imem (asn r) (divX d).
  Proof.
    intros d asn Hbox HR.
    pose proof (sol_mem_divZ d asn Hbox HR) as [HZ1 HZ2].
    pose proof (sol_mem_divY d asn Hbox HR) as [HY1 HY2].
    pose proof (divZ_lb1 d) as HZlb.
    destruct HR as [Hq Hr].
    apply imem_imeet. split; [apply Hbox|].
    unfold ffwdP. apply imem_pair. split.
    - (* min4 ≤ ⌊y/z⌋ *)
      rewrite Hr.
      eapply zle_trans;
        [| apply (zfdiv_corner_lb (asn p) (fst (divZ d)) (snd (divZ d)) (asn q));
           [exact Hq | exact HZlb | exact HZ1 | exact HZ2]].
      apply zmin_glb.
      + eapply zle_trans; [apply zmin_le_l|].
        eapply zle_trans; [apply zmin_le_l|].
        apply zfdiv_mono_y; [exact HZlb | exact HY1].
      + eapply zle_trans; [apply zmin_le_l|].
        eapply zle_trans; [apply zmin_le_r|].
        apply zfdiv_mono_y; [|exact HY1].
        eapply zle_trans; [exact HZlb|].
        eapply zle_trans; [exact HZ1 | exact HZ2].
    - (* ⌊y/z⌋ ≤ max4 *)
      rewrite Hr.
      eapply zle_trans;
        [apply (zfdiv_corner_ub (asn p) (fst (divZ d)) (snd (divZ d)) (asn q));
         [exact Hq | exact HZlb | exact HZ1 | exact HZ2] |].
      apply zmax_lub.
      + eapply zle_trans; [|apply zmax_ge_r].
        eapply zle_trans; [|apply zmax_ge_l].
        apply zfdiv_mono_y; [exact HZlb | exact HY2].
      + eapply zle_trans; [|apply zmax_ge_r].
        eapply zle_trans; [|apply zmax_ge_r].
        apply zfdiv_mono_y; [|exact HY2].
        eapply zle_trans; [exact HZlb|].
        eapply zle_trans; [exact HZ1 | exact HZ2].
  Qed.

  (* Soundness of the fdiv⁺ propagator. *)
  Lemma prop_fdivp_preserves : forall d asn,
    ibox d asn -> Rfdp asn -> forall w, imem (asn w) (prop_fdivp d w).
  Proof.
    intros d asn Hbox HR w.
    pose proof (sol_mem_divZ d asn Hbox HR) as HmZ.
    pose proof (sol_mem_divY d asn Hbox HR) as HmY.
    pose proof (sol_mem_divX d asn Hbox HR) as HmX.
    unfold prop_fdivp.
    destruct (isbotb (divZ d)) eqn:EZ.
    { exfalso. apply isbotb_isbot in EZ. exact (imem_not_isbot _ _ HmZ EZ). }
    destruct (isbotb (divY d)) eqn:EY.
    { exfalso. apply isbotb_isbot in EY. exact (imem_not_isbot _ _ HmY EY). }
    destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
    - rewrite vupd_same. exact HmX.
    - rewrite (vupd_other _ r _ p) by congruence.
      rewrite vupd_same. exact HmY.
    - rewrite (vupd_other _ r _ q) by congruence.
      rewrite (vupd_other _ p _ q) by congruence.
      rewrite vupd_same. exact HmZ.
  Qed.

  Lemma prop_fdivp_sound : forall d, leI V3 (bestR Rfdp d) (prop_fdivp d).
  Proof.
    intros d. apply (sols_preserved_sound_R Rfdp r).
    intros asn Hb HR. apply prop_fdivp_preserves; assumption.
  Qed.

End FdivPropagator.

(* ==================== α-completeness of the fdiv⁺ propagator ============= *)

Section FdivComplete.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  (* The y-window of a given denominator z: y must lie in
     [xl·z, (xu+1)·z - 1] ∩ (d p). *)
  Definition Wwin (d : istore V3) (z : Z) : Itv :=
    imeet (d p)
      (zmul (fst (d r)) (Fin z),
       zsub (zmul (zadd (snd (d r)) (Fin 1)) (Fin z)) (Fin 1)).

  Lemma Wwin_nonbot : forall d (z : Z),
    ~ isbot (d r) -> ~ isbot (d p) -> 1 <= z ->
    zle (zmul (fst (d r)) (Fin z)) (snd (d p)) ->
    zle (zadd (fst (d p)) (Fin 1)) (zmul (zadd (snd (d r)) (Fin 1)) (Fin z)) ->
    ~ isbot (Wwin d z).
  Proof.
    intros d z HdR HdP Hz HC1 HC2.
    destruct (d r) as [xl xu] eqn:ER. destruct (d p) as [yl yu] eqn:EP.
    apply not_isbot_char in HdR. destruct HdR as [HR1 [HR2 HR3]].
    apply not_isbot_char in HdP. destruct HdP as [HP1 [HP2 HP3]].
    cbn [fst snd] in *.
    unfold Wwin. rewrite ER, EP. unfold imeet. cbn [fst snd].
    apply not_isbot_char. repeat split.
    - apply zmax_lub; apply zmin_glb.
      + exact HP1.
      + apply zle_sub1_of_add1. exact HC2.
      + exact HC1.
      + eapply zle_trans; [apply (zmul_mono2 xl xu z HR1 Hz)|].
        apply zmul_succ_ge. exact Hz.
    - intros Hc. apply zmax_pinf in Hc. destruct Hc as [Hc|Hc].
      + exact (HP2 Hc).
      + exact (HR2 (zmul_pinf_inv xl z Hz Hc)).
    - intros Hc. apply zmin_minf in Hc. destruct Hc as [Hc|Hc].
      + exact (HP3 Hc).
      + apply zsub1_minf_inv in Hc.
        apply (zmul_minf_inv _ z Hz) in Hc.
        exact (HR3 (zadd1_minf_inv _ Hc)).
  Qed.

  (* Any y in the window of a member z of d(q) yields a solution. *)
  Lemma sol_of_wy : forall d (z y : Z),
    1 <= z -> imem z (d q) -> imem y (Wwin d z) ->
    exists asn, ibox d asn /\ Rfdp r p q asn /\ asn p = y /\ asn q = z.
  Proof.
    intros d z y Hz Hqz Hy.
    apply imem_imeet in Hy. destruct Hy as [Hyp Hy].
    apply imem_pair in Hy. destruct Hy as [Hy1 Hy2].
    exists (asn_rpq r p q (fdivZ y z) y z).
    assert (Br : imem (fdivZ y z) (d r)).
    { split.
      - apply (zmul_le_fdiv (fst (d r)) y z Hz Hy1).
      - apply (fdiv_le_zmul (snd (d r)) y z Hz Hy2). }
    split; [|split; [|split]].
    - intros w. destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
      + rewrite asn_rpq_r. exact Br.
      + rewrite asn_rpq_p by exact Hrp. exact Hyp.
      + rewrite asn_rpq_q by assumption. exact Hqz.
    - unfold Rfdp. rewrite asn_rpq_r, asn_rpq_p, asn_rpq_q by assumption.
      split; [exact Hz | reflexivity].
    - apply asn_rpq_p. exact Hrp.
    - apply asn_rpq_q; assumption.
  Qed.

  (* Every member of the refined denominator interval yields a solution. *)
  Lemma sol_of_z : forall d (z : Z),
    ~ isbot (d r) -> ~ isbot (d p) ->
    imem z (divZ r p q d) ->
    exists asn, ibox d asn /\ Rfdp r p q asn /\ asn q = z.
  Proof.
    intros d z HdR HdP Hm.
    apply imem_imeet in Hm. destruct Hm as [Hq Hden].
    apply fdenP_mem in Hden; [|exact HdR|exact HdP].
    destruct Hden as [Hz [HC1 HC2]].
    destruct (not_isbot_mem (Wwin d z) (Wwin_nonbot d z HdR HdP Hz HC1 HC2))
      as [y Hy].
    destruct (sol_of_wy d z y Hz Hq Hy) as [asn [Hb [HR [_ Hqz]]]].
    exists asn. auto.
  Qed.

  (* A member z of the refined denominator whose window is further clamped
     also yields a solution. *)
  Lemma sol_of_z_clamped : forall d (z : Z) (cl cu : Zinf),
    ~ isbot (d r) -> ~ isbot (d p) ->
    imem z (divZ r p q d) ->
    zle cl (snd (Wwin d z)) -> zle (fst (Wwin d z)) cu ->
    zle cl cu -> cl <> PInf -> cu <> MInf ->
    exists asn y, ibox d asn /\ Rfdp r p q asn /\ asn q = z /\ asn p = y /\
                  zle cl (Fin y) /\ zle (Fin y) cu.
  Proof.
    intros d z cl cu HdR HdP Hm Hcl Hcu Hclu HclP HcuM.
    apply imem_imeet in Hm. destruct Hm as [Hq Hden].
    apply fdenP_mem in Hden; [|exact HdR|exact HdP].
    destruct Hden as [Hz [HC1 HC2]].
    pose proof (Wwin_nonbot d z HdR HdP Hz HC1 HC2) as HW.
    destruct (Wwin d z) as [wl wu] eqn:EW.
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

End FdivComplete.

Lemma zmin_id : forall x, zmin x x = x.
Proof. intros x. unfold zmin. destruct (zleb x x); reflexivity. Qed.

Lemma zle_minf_eq : forall x, zle x MInf -> x = MInf.
Proof. intros [|a|] H; simpl in H; try contradiction; reflexivity. Qed.

Lemma zle_pinf_eq : forall x, zle PInf x -> x = PInf.
Proof. intros [|a|] H; simpl in H; try contradiction; reflexivity. Qed.

(* ---------- Choice of a good denominator for each bound obligation ------- *)

(* For the lower bound of the numerator: a member z with xl·z ≤ M. *)
Lemma zstar_mul_lo : forall (xl : Zinf) (Zi : Itv) (M : Z),
  xl <> PInf -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (zmin (zmul xl (fst Zi)) (zmul xl (snd Zi))) (Fin M) ->
  exists z, imem z Zi /\ 1 <= z /\ zle (zmul xl (Fin z)) (Fin M).
Proof.
  intros xl [zl zu] M HxlP Hnb Hlb1 Hmin.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  cbn [fst snd] in *.
  destruct zl as [|l|]; [simpl in Hlb1; contradiction | | congruence].
  simpl in Hlb1.
  assert (Hmeml : imem l (Fin l, zu)).
  { split; [simpl; lia | exact H1]. }
  destruct xl as [|a|]; [| | congruence].
  - exists l. split; [exact Hmeml|]. split; [lia|].
    rewrite zmul_minf_pos by lia. exact I.
  - destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
    + destruct (zmin_case (zmul (Fin a) (Fin l)) (zmul (Fin a) zu))
        as [[E _]|[E _]]; rewrite E in Hmin.
      * exists l. split; [exact Hmeml|]. split; [lia | exact Hmin].
      * destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia | exact Hmin].
        -- rewrite zmul_fin_pinf_neg in Hmin by lia.
           exists (Z.max l (cdivZ M a)). split.
           { split; simpl; [lia | exact I]. }
           split; [lia|].
           simpl. apply (proj1 (cdivZ_le_neg M a (Z.max l (cdivZ M a)) Ha)). lia.
    + subst a. rewrite !zmul_fin0_l, zmin_id in Hmin. simpl in Hmin.
      exists l. split; [exact Hmeml|]. split; [lia|].
      rewrite zmul_fin0_l. simpl. lia.
    + destruct (zmin_case (zmul (Fin a) (Fin l)) (zmul (Fin a) zu))
        as [[E _]|[E _]]; rewrite E in Hmin.
      * exists l. split; [exact Hmeml|]. split; [lia | exact Hmin].
      * destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia | exact Hmin].
        -- rewrite zmul_fin_pinf_pos in Hmin by lia. simpl in Hmin. contradiction.
Qed.

(* For the upper bound of the numerator: a member z with (xu+1)·z - 1 ≥ M. *)
Lemma zstar_mul_hi : forall (xu : Zinf) (Zi : Itv) (M : Z),
  xu <> MInf -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (Fin M) (zmax (zsub (zmul (zadd xu (Fin 1)) (fst Zi)) (Fin 1))
                    (zsub (zmul (zadd xu (Fin 1)) (snd Zi)) (Fin 1))) ->
  exists z, imem z Zi /\ 1 <= z /\
            zle (Fin M) (zsub (zmul (zadd xu (Fin 1)) (Fin z)) (Fin 1)).
Proof.
  intros xu [zl zu] M HxuM Hnb Hlb1 Hmax.
  apply not_isbot_char in Hnb. destruct Hnb as [H1 [H2 H3]].
  cbn [fst snd] in *.
  destruct zl as [|l|]; [simpl in Hlb1; contradiction | | congruence].
  simpl in Hlb1.
  assert (Hmeml : imem l (Fin l, zu)).
  { split; [simpl; lia | exact H1]. }
  destruct xu as [|b|]; [congruence| |].
  - (* xu = Fin b, C = Fin (b+1) *)
    cbn [zadd] in *.
    destruct (Z.lt_trichotomy 0 (b + 1)) as [Hb|[Hb|Hb]].
    + (* b+1 > 0 *)
      destruct (zmax_case (zsub (zmul (Fin (b + 1)) (Fin l)) (Fin 1))
                          (zsub (zmul (Fin (b + 1)) zu) (Fin 1)))
        as [[E _]|[E _]]; rewrite E in Hmax.
      * (* max at zu *)
        destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia | exact Hmax].
        -- rewrite zmul_fin_pinf_pos in Hmax by lia.
           exists (Z.max l (cdivZ (M + 1) (b + 1))). split.
           { split; simpl; [lia | exact I]. }
           split; [lia|].
           simpl.
           pose proof (proj1 (cdivZ_le (M + 1) (b + 1)
                        (Z.max l (cdivZ (M + 1) (b + 1))) ltac:(lia))
                        ltac:(lia)) as Hcc.
           nia.
      * exists l. split; [exact Hmeml|]. split; [lia | exact Hmax].
    + (* b+1 = 0 *)
      rewrite <- Hb in *.
      rewrite !zmul_fin0_l in Hmax.
      cbn [zsub] in Hmax. rewrite zmin_id in Hmax || idtac.
      exists l. split; [exact Hmeml|]. split; [lia|].
      rewrite zmul_fin0_l. cbn [zsub].
      destruct (zmax_case (Fin (0 - 1)) (Fin (0 - 1))) as [[E _]|[E _]];
        rewrite E in Hmax; simpl in Hmax; simpl; lia.
    + (* b+1 < 0 *)
      destruct (zmax_case (zsub (zmul (Fin (b + 1)) (Fin l)) (Fin 1))
                          (zsub (zmul (Fin (b + 1)) zu) (Fin 1)))
        as [[E _]|[E _]]; rewrite E in Hmax.
      * destruct zu as [|u|]; [congruence| |].
        -- exists u. simpl in H1. split; [split; simpl; lia|].
           split; [lia | exact Hmax].
        -- rewrite zmul_fin_pinf_neg in Hmax by lia.
           cbn [zsub] in Hmax. simpl in Hmax. contradiction.
      * exists l. split; [exact Hmeml|]. split; [lia | exact Hmax].
  - (* xu = +inf *)
    exists l. split; [exact Hmeml|]. split; [lia|].
    cbn [zadd]. rewrite zmul_pinf_pos by lia. cbn [zsub]. apply zle_pinf.
Qed.

(* For the lower bound of the quotient: a member z with yl ≤ (M+1)·z - 1,
   given that some corner ⌊Y0/e⌋ is at most M (yl ≤ Y0). *)
Lemma zstar_div_lo : forall (yl Y0 : Zinf) (Zi : Itv) (M : Z),
  Y0 <> PInf -> zle yl Y0 -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (zmin (zfdiv Y0 (fst Zi)) (zfdiv Y0 (snd Zi))) (Fin M) ->
  exists z, imem z Zi /\ 1 <= z /\ zle yl (Fin (z * M + z - 1)).
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
  destruct (zmin_case (zfdiv (Fin w) (Fin l)) (zfdiv (Fin w) zu))
    as [[E _]|[E _]]; rewrite E in Hmin.
  - (* corner at zl = Fin l *)
    exists l. split; [exact Hmeml|]. split; [lia|].
    simpl in Hmin.
    assert (Hw : w <= l * M + l - 1) by (apply fdivZ_ub; lia).
    destruct yl as [|c|]; simpl in HylY0; try contradiction; simpl; lia.
  - (* corner at zu *)
    destruct zu as [|u|]; [congruence| |].
    + exists u. simpl in H1. split; [split; simpl; lia|].
      split; [lia|].
      simpl in Hmin.
      assert (Hw : w <= u * M + u - 1) by (apply fdivZ_ub; lia).
      destruct yl as [|c|]; simpl in HylY0; try contradiction; simpl; lia.
    + (* zu = +inf *)
      simpl in Hmin. destruct (w <? 0) eqn:Ew; simpl in Hmin.
      * (* w < 0, so M >= -1 and yl ≤ w ≤ -1 *)
        apply Z.ltb_lt in Ew.
        exists l. split; [exact Hmeml|]. split; [lia|].
        destruct yl as [|c|]; simpl in HylY0; try contradiction; simpl; nia.
      * (* w >= 0, so M >= 0 *)
        apply Z.ltb_ge in Ew.
        destruct yl as [|c|]; simpl in HylY0; try contradiction.
        -- exists l. split; [exact Hmeml|]. split; [lia | exact I].
        -- exists (Z.max l (cdivZ (c + 1) (M + 1))). split.
           { split; simpl; [lia | exact I]. }
           split; [lia|].
           simpl.
           pose proof (proj1 (cdivZ_le (c + 1) (M + 1)
                        (Z.max l (cdivZ (c + 1) (M + 1))) ltac:(lia))
                        ltac:(lia)) as Hcc.
           nia.
Qed.

(* For the upper bound of the quotient: a member z with M·z ≤ yu, given that
   some corner ⌊Y1/e⌋ is at least M (Y1 ≤ yu). *)
Lemma zstar_div_hi : forall (yu Y1 : Zinf) (Zi : Itv) (M : Z),
  yu <> MInf -> zle Y1 yu -> ~ isbot Zi -> zle (Fin 1) (fst Zi) ->
  zle (Fin M) (zmax (zfdiv Y1 (fst Zi)) (zfdiv Y1 (snd Zi))) ->
  exists z, imem z Zi /\ 1 <= z /\ zle (Fin (M * z)) yu.
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
    destruct (zmax_case (zfdiv MInf (Fin l)) (zfdiv MInf zu))
      as [[E _]|[E _]]; rewrite E in Hmax.
    - destruct zu as [|u|]; [congruence| |].
      + simpl in H1. rewrite zfdiv_minf_pos in Hmax by lia.
        simpl in Hmax. contradiction.
      + (* ⌊-inf/+inf⌋ = -1, so M ≤ -1 < 0 *)
        simpl in Hmax.
        destruct yu as [|c|]; [congruence| |].
        * exists (Z.max l (cdivZ c M)). split.
          { split; simpl; [lia | exact I]. }
          split; [lia|].
          simpl.
          pose proof (proj1 (cdivZ_le_neg c M
                       (Z.max l (cdivZ c M)) ltac:(lia)) ltac:(lia)) as Hcc.
          nia.
        * exists l. split; [exact Hmeml|]. split; [lia | apply zle_pinf].
    - rewrite zfdiv_minf_pos in Hmax by lia. simpl in Hmax. contradiction. }
  2:{ (* Y1 = +inf, hence yu = +inf *)
    apply zle_pinf_eq in HY1yu. subst yu.
    exists l. split; [exact Hmeml|]. split; [lia | apply zle_pinf]. }
  (* Y1 = Fin w *)
  destruct (zmax_case (zfdiv (Fin w) (Fin l)) (zfdiv (Fin w) zu))
    as [[E _]|[E _]]; rewrite E in Hmax.
  - (* corner at zu *)
    destruct zu as [|u|]; [congruence| |].
    + exists u. simpl in H1. split; [split; simpl; lia|].
      split; [lia|].
      simpl in Hmax.
      assert (Hw : u * M <= w) by (apply fdivZ_lb; lia).
      destruct yu as [|c|]; simpl in HY1yu; try contradiction; simpl; try exact I; nia.
    + (* zu = +inf: corner is the sign indicator of w *)
      simpl in Hmax. destruct (w <? 0) eqn:Ew; simpl in Hmax.
      * (* w < 0, M ≤ -1 *)
        apply Z.ltb_lt in Ew.
        destruct yu as [|c|]; [congruence| | ].
        -- (* yu = Fin c *)
           exists (Z.max l (cdivZ c M)). split.
           { split; simpl; [lia | exact I]. }
           split; [lia|].
           simpl.
           pose proof (proj1 (cdivZ_le_neg c M
                        (Z.max l (cdivZ c M)) ltac:(lia)) ltac:(lia)) as Hcc.
           nia.
        -- exists l. split; [exact Hmeml|]. split; [lia | apply zle_pinf].
      * (* w >= 0, M ≤ 0, and yu ≥ Y1 = w ≥ 0 *)
        apply Z.ltb_ge in Ew.
        exists l. split; [exact Hmeml|]. split; [lia|].
        destruct yu as [|c|]; simpl in HY1yu; try contradiction; simpl; try exact I; nia.
  - (* corner at zl = Fin l *)
    exists l. split; [exact Hmeml|]. split; [lia|].
    simpl in Hmax.
    assert (Hw : l * M <= w) by (apply fdivZ_lb; lia).
    destruct yu as [|c|]; simpl in HY1yu; try contradiction; simpl; try exact I; nia.
Qed.

(* ---------- α-completeness of the fdiv⁺ propagator ---------- *)

Section FdivBest.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  Lemma prop_fdivp_complete : forall d,
    leI V3 (prop_fdivp r p q d) (bestR (Rfdp r p q) d).
  Proof.
    intros d. unfold prop_fdivp.
    destruct (isbotb (divZ r p q d)) eqn:EZ.
    { apply isbotb_isbot in EZ. left. exists q. rewrite vupd_same. exact EZ. }
    apply isbotb_false in EZ.
    destruct (isbotb (divY r p q d)) eqn:EY.
    { apply isbotb_isbot in EY. left. exists p. rewrite vupd_same. exact EY. }
    apply isbotb_false in EY.
    destruct (classic (isbot (divX r p q d))) as [EX|EX].
    { left. exists r. rewrite vupd_same. exact EX. }
    assert (HdR : ~ isbot (d r)).
    { intro Hb. apply EX. apply isbot_imeet_l. exact Hb. }
    assert (HdP : ~ isbot (d p)).
    { intro Hb. apply EY. apply isbot_imeet_l. exact Hb. }
    assert (HdQ : ~ isbot (d q)).
    { intro Hb. apply EZ. apply isbot_imeet_l. exact Hb. }
    pose proof (divZ_lb1 r p q d) as HZlb.
    assert (HZlele : zle (fst (divZ r p q d)) (snd (divZ r p q d))).
    { destruct (divZ r p q d) as [a b] eqn:EE.
      apply not_isbot_char in EZ. cbn [fst snd]. tauto. }
    assert (HYchar := EY). 
    destruct (divY r p q d) as [Yl Yu] eqn:EYI.
    apply not_isbot_char in HYchar. destruct HYchar as [HY1 [HY2 HY3]].
    right. intros w.
    destruct (V3_cover r p q Hrp Hrq Hpq w) as [Hw|[Hw|Hw]]; subst w.
    - (* variable r: the interval divX *)
      rewrite vupd_same.
      apply isle_bestR_of_wit.
      + (* lower bound of x *)
        intros M HM.
        unfold divX in HM. rewrite EYI in HM.
        unfold imeet in HM. cbn [fst] in HM.
        assert (HxlM : zle (fst (d r)) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_l | exact HM]. }
        assert (Hmin4 : zle (fst (ffwdP (Yl, Yu) (divZ r p q d))) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_r | exact HM]. }
        unfold ffwdP in Hmin4. cbn [fst snd] in Hmin4.
        assert (Hrow : zle (zmin (zfdiv Yl (fst (divZ r p q d)))
                                 (zfdiv Yl (snd (divZ r p q d)))) (Fin M)).
        { destruct (zmin_case
              (zmin (zfdiv Yl (fst (divZ r p q d)))
                    (zfdiv Yl (snd (divZ r p q d))))
              (zmin (zfdiv Yu (fst (divZ r p q d)))
                    (zfdiv Yu (snd (divZ r p q d)))))
            as [[E _]|[E _]]; rewrite E in Hmin4; [exact Hmin4|].
          eapply zle_trans; [|exact Hmin4].
          apply zmin_glb.
          - eapply zle_trans; [apply zmin_le_l|].
            apply zfdiv_mono_y; [exact HZlb | exact HY1].
          - eapply zle_trans; [apply zmin_le_r|].
            apply zfdiv_mono_y;
              [eapply zle_trans; [exact HZlb | exact HZlele] | exact HY1]. }
        assert (HylYl : zle (fst (d p)) Yl).
        { assert (E := EYI). unfold divY in E.
          unfold imeet in E. injection E as E1 E2.
          rewrite <- E1. apply zmax_ge_l. }
        destruct (zstar_div_lo (fst (d p)) Yl (divZ r p q d) M HY2 HylYl EZ HZlb Hrow)
          as [z [Hmz [Hz1 Hyl]]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z MInf
                    (Fin (z * M + z - 1)) HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [_ Hycu]]]]]]].
        * apply zle_minf.
        * unfold Wwin. unfold imeet. cbn [fst].
          apply zmax_lub; [exact Hyl|].
          eapply zle_trans;
            [apply (zmul_mono_l_fin (fst (d r)) M z HxlM Hz1)|].
          simpl. nia.
        * apply zle_minf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          destruct HR as [_ Hreq]. rewrite Hreq, Hpy, Hqz.
          simpl in Hycu. apply fdivZ_ub; [lia|]. nia.
      + (* upper bound of x *)
        intros M HM.
        unfold divX in HM. rewrite EYI in HM.
        unfold imeet in HM. cbn [snd] in HM.
        assert (HxuM : zle (Fin M) (snd (d r))).
        { eapply zle_trans; [exact HM | apply zmin_le_l]. }
        assert (Hmax4 : zle (Fin M) (snd (ffwdP (Yl, Yu) (divZ r p q d)))).
        { eapply zle_trans; [exact HM | apply zmin_le_r]. }
        unfold ffwdP in Hmax4. cbn [fst snd] in Hmax4.
        assert (Hrow : zle (Fin M) (zmax (zfdiv Yu (fst (divZ r p q d)))
                                         (zfdiv Yu (snd (divZ r p q d))))).
        { eapply zle_trans; [exact Hmax4|].
          destruct (zmax_case
              (zmax (zfdiv Yl (fst (divZ r p q d)))
                    (zfdiv Yl (snd (divZ r p q d))))
              (zmax (zfdiv Yu (fst (divZ r p q d)))
                    (zfdiv Yu (snd (divZ r p q d)))))
            as [[E _]|[E _]]; rewrite E.
          - apply zle_refl.
          - apply zmax_lub.
            + eapply zle_trans; [|apply zmax_ge_l].
              apply zfdiv_mono_y; [exact HZlb | exact HY1].
            + eapply zle_trans; [|apply zmax_ge_r].
              apply zfdiv_mono_y;
                [eapply zle_trans; [exact HZlb | exact HZlele] | exact HY1]. }
        assert (HYuyu : zle Yu (snd (d p))).
        { assert (E := EYI). unfold divY in E.
          unfold imeet in E. injection E as E1 E2.
          rewrite <- E2. apply zmin_le_l. }
        assert (Hyu : snd (d p) <> MInf).
        { apply not_isbot_char in HdP.
          destruct (d p) as [pl pu]. cbn [fst snd] in *. tauto. }
        destruct (zstar_div_hi (snd (d p)) Yu (divZ r p q d) M Hyu HYuyu EZ HZlb Hrow)
          as [z [Hmz [Hz1 Hyu']]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z (Fin (M * z))
                    PInf HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [Hycl _]]]]]]].
        * unfold Wwin. unfold imeet. cbn [snd].
          apply zmin_glb; [exact Hyu'|].
          eapply zle_trans;
            [| apply zsub1_mono, (zmul_mono_r_fin (zadd (snd (d r)) (Fin 1))
                                    (M + 1) z (zadd1_mono_r _ _ HxuM) Hz1)].
          simpl. nia.
        * apply zle_pinf.
        * apply zle_pinf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          destruct HR as [_ Hreq]. rewrite Hreq, Hpy, Hqz.
          simpl in Hycl. apply fdivZ_lb; [lia|]. nia.
    - (* variable p: the interval divY *)
      rewrite (vupd_other _ r _ p) by congruence.
      rewrite vupd_same.
      apply isle_bestR_of_wit.
      + intros M HM.
        assert (E := EYI). unfold divY, fnumP in E.
        unfold imeet in E. injection E as E1 E2.
        rewrite <- E1 in HM. cbn [fst snd] in HM.
        assert (HylM : zle (fst (d p)) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_l | exact HM]. }
        assert (Hnum : zle (zmin (zmul (fst (d r)) (fst (divZ r p q d)))
                                 (zmul (fst (d r)) (snd (divZ r p q d)))) (Fin M)).
        { eapply zle_trans; [apply zmax_ge_r | exact HM]. }
        assert (HxlP : fst (d r) <> PInf).
        { apply not_isbot_char in HdR.
          destruct (d r) as [rl ru]. cbn [fst snd] in *. tauto. }
        destruct (zstar_mul_lo (fst (d r)) (divZ r p q d) M HxlP EZ HZlb Hnum)
          as [z [Hmz [Hz1 Hxlz]]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z MInf (Fin M) HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [_ Hycu]]]]]]].
        * apply zle_minf.
        * unfold Wwin. unfold imeet. cbn [fst].
          apply zmax_lub; [exact HylM | exact Hxlz].
        * apply zle_minf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          rewrite Hpy. simpl in Hycu. exact Hycu.
      + intros M HM.
        assert (E := EYI). unfold divY, fnumP in E.
        unfold imeet in E. injection E as E1 E2.
        rewrite <- E2 in HM. cbn [fst snd] in HM.
        assert (HyuM : zle (Fin M) (snd (d p))).
        { eapply zle_trans; [exact HM | apply zmin_le_l]. }
        assert (Hnum : zle (Fin M)
                  (zmax (zsub (zmul (zadd (snd (d r)) (Fin 1))
                                    (fst (divZ r p q d))) (Fin 1))
                        (zsub (zmul (zadd (snd (d r)) (Fin 1))
                                    (snd (divZ r p q d))) (Fin 1)))).
        { eapply zle_trans; [exact HM | apply zmin_le_r]. }
        assert (HxuM : snd (d r) <> MInf).
        { apply not_isbot_char in HdR.
          destruct (d r) as [rl ru]. cbn [fst snd] in *. tauto. }
        destruct (zstar_mul_hi (snd (d r)) (divZ r p q d) M HxuM EZ HZlb Hnum)
          as [z [Hmz [Hz1 Hhi]]].
        destruct (sol_of_z_clamped r p q Hrp Hrq Hpq d z (Fin M) PInf HdR HdP Hmz)
          as [asn [y [Hb [HR [Hqz [Hpy [Hycl _]]]]]]].
        * unfold Wwin. unfold imeet. cbn [snd].
          apply zmin_glb; [exact HyuM | exact Hhi].
        * apply zle_pinf.
        * apply zle_pinf.
        * congruence.
        * congruence.
        * exists asn. split; [exact Hb|]. split; [exact HR|].
          rewrite Hpy. simpl in Hycl. exact Hycl.
    - (* variable q: the interval divZ *)
      rewrite (vupd_other _ r _ q) by congruence.
      rewrite (vupd_other _ p _ q) by congruence.
      rewrite vupd_same.
      apply isle_bestR_of_wit.
      + intros M HM.
        destruct (mem_below (divZ r p q d) M EZ HM) as [z [Hmz HzM]].
        destruct (sol_of_z r p q Hrp Hrq Hpq d z HdR HdP Hmz)
          as [asn [Hb [HR Hqz]]].
        exists asn. split; [exact Hb|]. split; [exact HR|]. lia.
      + intros M HM.
        destruct (mem_above (divZ r p q d) M EZ HM) as [z [Hmz HzM]].
        destruct (sol_of_z r p q Hrp Hrq Hpq d z HdR HdP Hmz)
          as [asn [Hb [HR Hqz]]].
        exists asn. split; [exact Hb|]. split; [exact HR|]. lia.
  Qed.

  (* The fdiv⁺ propagator is the best propagator of its relation. *)
  Theorem prop_fdivp_best : forall d,
    eqI V3 (prop_fdivp r p q d) (bestR (Rfdp r p q) d).
  Proof.
    intros d. apply (ole_antisym (o := I_OSet V3)).
    - apply prop_fdivp_complete.
    - apply prop_fdivp_sound; assumption.
  Qed.

End FdivBest.

(* ==================== Store joins, reflections, restrictions ============= *)

Definition isbotIb (d : istore V3) : bool :=
  isbotb (d Vx) || isbotb (d Vy) || isbotb (d Vz).

Lemma isbotIb_true : forall d, isbotIb d = true <-> isbotI V3 d.
Proof.
  intros d. unfold isbotIb. rewrite !Bool.orb_true_iff, !isbotb_isbot.
  split.
  - intros [[H|H]|H]; [exists Vx | exists Vy | exists Vz]; exact H.
  - intros [x Hx]. destruct x; tauto.
Qed.

Lemma isbotIb_false : forall d, isbotIb d = false <-> ~ isbotI V3 d.
Proof.
  intros d. split.
  - intros H Hc. apply isbotIb_true in Hc. congruence.
  - intros H. destruct (isbotIb d) eqn:E; [|reflexivity].
    apply isbotIb_true in E. contradiction.
Qed.

(* The store join ⊔̇ of the paper, and the pointwise join ⊔̈ of propagators. *)
Definition sjoin (d1 d2 : istore V3) : istore V3 :=
  if isbotIb d1 then d2 else if isbotIb d2 then d1
  else fun w => isjoin (d1 w) (d2 w).

Definition pjoin (p1 p2 : istore V3 -> istore V3) : istore V3 -> istore V3 :=
  fun d => sjoin (p1 d) (p2 d).

(* eqI from pointwise equality. *)
Lemma eqI_of_pointwise : forall (d1 d2 : istore V3),
  (forall w, d1 w = d2 w) -> eqI V3 d1 d2.
Proof. intros d1 d2 H. right. intros w. rewrite H. apply ieq_refl. Qed.

Lemma eqI_trans3 : forall (a b c : istore V3),
  eqI V3 a b -> eqI V3 b c -> eqI V3 a c.
Proof. exact (oeq_trans (o := I_OSet V3)). Qed.

Lemma eqI_isbotI : forall (a b : istore V3),
  eqI V3 a b -> isbotI V3 a -> isbotI V3 b.
Proof.
  intros a b [[H1 H2]|H] Hb; [exact H2|].
  destruct Hb as [w Hw]. exists w. exact (ieq_isbot _ _ (H w) Hw).
Qed.

(* ---------- Extensionality of hulls ---------- *)

Lemma alphai_ext : forall (V V' : powerset Z),
  (forall v, V v <-> V' v) -> alphai V = alphai V'.
Proof.
  intros V V' Hiff. unfold alphai.
  f_equal.
  - apply zle_antisym; apply zinfS_greatest; intros x [v [Hv Heq]]; subst;
      apply zinfS_lb; exists v; (split; [apply Hiff; exact Hv | reflexivity]).
  - apply zle_antisym; apply zsup_least; intros x [v [Hv Heq]]; subst;
      apply zsup_ub; exists v; (split; [apply Hiff; exact Hv | reflexivity]).
Qed.

(* ---------- Union of relations = store join of best propagators ---------- *)

Lemma zinfS_union_min : forall (V1 V2 : Z -> Prop),
  zinfS (finset (fun v => V1 v \/ V2 v))
  = zmin (zinfS (finset V1)) (zinfS (finset V2)).
Proof.
  intros V1 V2. apply zle_antisym.
  - apply zmin_glb; apply zinfS_greatest; intros x [v [Hv Heq]]; subst;
      apply zinfS_lb; exists v; (split; [tauto | reflexivity]).
  - apply zinfS_greatest. intros x [v [[Hv|Hv] Heq]]; subst.
    + eapply zle_trans; [apply zmin_le_l|].
      apply zinfS_lb. exists v. split; [exact Hv | reflexivity].
    + eapply zle_trans; [apply zmin_le_r|].
      apply zinfS_lb. exists v. split; [exact Hv | reflexivity].
Qed.

Lemma zsup_union_max : forall (V1 V2 : Z -> Prop),
  zsup (finset (fun v => V1 v \/ V2 v))
  = zmax (zsup (finset V1)) (zsup (finset V2)).
Proof.
  intros V1 V2. apply zle_antisym.
  - apply zsup_least. intros x [v [[Hv|Hv] Heq]]; subst.
    + eapply zle_trans; [|apply zmax_ge_l].
      apply zsup_ub. exists v. split; [exact Hv | reflexivity].
    + eapply zle_trans; [|apply zmax_ge_r].
      apply zsup_ub. exists v. split; [exact Hv | reflexivity].
  - apply zmax_lub; apply zsup_least; intros x [v [Hv Heq]]; subst;
      apply zsup_ub; exists v; (split; [tauto | reflexivity]).
Qed.

Lemma bestR_no_sol_all_bot : forall (R : powerset (Asn V3)) d,
  (forall asn, ibox d asn -> ~ R asn) -> forall w, isbot (bestR R d w).
Proof.
  intros R d Hno w. unfold bestR, ihull.
  apply alphai_bot_of_empty. intros v [asn [[Hb HR] _]].
  exact (Hno asn Hb HR).
Qed.

Lemma bestR_union : forall (R1 R2 : powerset (Asn V3)) (d : istore V3),
  eqI V3 (bestR (fun a => R1 a \/ R2 a) d)
         (sjoin (bestR R1 d) (bestR R2 d)).
Proof.
  intros R1 R2 d. unfold sjoin.
  destruct (classic (exists asn, ibox d asn /\ R1 asn)) as [Hs1|Hn1];
    destruct (classic (exists asn, ibox d asn /\ R2 asn)) as [Hs2|Hn2].
  - (* both satisfiable: componentwise raw join *)
    destruct Hs1 as [a1 [Hb1 HR1]]. destruct Hs2 as [a2 [Hb2 HR2]].
    assert (E1 : isbotIb (bestR R1 d) = false).
    { apply isbotIb_false. intros [w Hw].
      exact (imem_not_isbot _ _ (sol_in_bestR R1 d a1 Hb1 HR1 w) Hw). }
    assert (E2 : isbotIb (bestR R2 d) = false).
    { apply isbotIb_false. intros [w Hw].
      exact (imem_not_isbot _ _ (sol_in_bestR R2 d a2 Hb2 HR2 w) Hw). }
    rewrite E1, E2.
    apply eqI_of_pointwise. intros w.
    unfold isjoin.
    assert (E1w : isbotb (bestR R1 d w) = false).
    { apply isbotb_false. intro Hw.
      exact (imem_not_isbot _ _ (sol_in_bestR R1 d a1 Hb1 HR1 w) Hw). }
    assert (E2w : isbotb (bestR R2 d w) = false).
    { apply isbotb_false. intro Hw.
      exact (imem_not_isbot _ _ (sol_in_bestR R2 d a2 Hb2 HR2 w) Hw). }
    rewrite E1w, E2w.
    unfold bestR, ihull, alphai, ijoin. cbn [fst snd].
    f_equal.
    + rewrite <- zinfS_union_min. f_equal.
      apply functional_extensionality. intro x.
      apply propositional_extensionality.
      split.
      * intros [v [[asn [[Hb [HR|HR]] Hv]] Heq]];
          exists v; (split; [|exact Heq]); [left|right]; exists asn;
          (split; [split; assumption | assumption]).
      * intros [v [[Hv|Hv] Heq]];
          destruct Hv as [asn [[Hb HR] Hv']];
          exists v; (split; [|exact Heq]); exists asn;
          (split; [split;
             [assumption | (left; assumption) || (right; assumption)]
           | assumption]).
    + rewrite <- zsup_union_max. f_equal.
      apply functional_extensionality. intro x.
      apply propositional_extensionality.
      split.
      * intros [v [[asn [[Hb [HR|HR]] Hv]] Heq]];
          exists v; (split; [|exact Heq]); [left|right]; exists asn;
          (split; [split; assumption | assumption]).
      * intros [v [[Hv|Hv] Heq]];
          destruct Hv as [asn [[Hb HR] Hv']];
          exists v; (split; [|exact Heq]); exists asn;
          (split; [split;
             [assumption | (left; assumption) || (right; assumption)]
           | assumption]).
  - (* only R1 satisfiable *)
    assert (E2 : isbotIb (bestR R2 d) = true).
    { apply isbotIb_true. exists Vx. apply bestR_no_sol_all_bot.
      intros asn Hb HR. apply Hn2. eauto. }
    destruct Hs1 as [a1 [Hb1 HR1]].
    assert (E1 : isbotIb (bestR R1 d) = false).
    { apply isbotIb_false. intros [w Hw].
      exact (imem_not_isbot _ _ (sol_in_bestR R1 d a1 Hb1 HR1 w) Hw). }
    rewrite E1, E2.
    apply eqI_of_pointwise. intros w.
    apply bestR_ext. intros asn. split.
    + intros [Hb [HR|HR]]; [tauto|]. exfalso. apply Hn2. eauto.
    + intros [Hb HR]. tauto.
  - (* only R2 satisfiable *)
    assert (E1 : isbotIb (bestR R1 d) = true).
    { apply isbotIb_true. exists Vx. apply bestR_no_sol_all_bot.
      intros asn Hb HR. apply Hn1. eauto. }
    rewrite E1.
    apply eqI_of_pointwise. intros w.
    apply bestR_ext. intros asn. split.
    + intros [Hb [HR|HR]]; [|tauto]. exfalso. apply Hn1. eauto.
    + intros [Hb HR]. tauto.
  - (* neither satisfiable: all stores are failed *)
    assert (E1 : isbotIb (bestR R1 d) = true).
    { apply isbotIb_true. exists Vx. apply bestR_no_sol_all_bot.
      intros asn Hb HR. apply Hn1. eauto. }
    rewrite E1. left. split.
    + exists Vx. apply bestR_no_sol_all_bot.
      intros asn Hb [HR|HR]; [apply Hn1 | apply Hn2]; eauto.
    + exists Vx. apply bestR_no_sol_all_bot.
      intros asn Hb HR. apply Hn2. eauto.
Qed.

(* ---------- Conjugation by sign flips (the zneg_uv reflections) ---------- *)

Lemma ineg_involutive : forall i, ineg (ineg i) = i.
Proof.
  intros [a b]. unfold ineg. cbn [fst snd]. rewrite !zneg_involutive.
  reflexivity.
Qed.

Definition sflip (f : V3 -> bool) (d : istore V3) : istore V3 :=
  fun w => if f w then ineg (d w) else d w.

Definition aflip (f : V3 -> bool) (asn : Asn V3) : Asn V3 :=
  fun w => if f w then (- asn w)%Z else asn w.

Lemma aflip_involutive : forall f a, aflip f (aflip f a) = a.
Proof.
  intros f a. apply functional_extensionality. intro w.
  unfold aflip. destruct (f w); lia.
Qed.

Lemma sflip_involutive_pt : forall f d w, sflip f (sflip f d) w = d w.
Proof.
  intros f d w. unfold sflip. destruct (f w); [apply ineg_involutive | reflexivity].
Qed.

Lemma ibox_sflip : forall f d a, ibox (sflip f d) a <-> ibox d (aflip f a).
Proof.
  intros f d a. split; intros H w; specialize (H w); unfold sflip, aflip in *;
    destruct (f w).
  - apply imem_ineg. exact H.
  - exact H.
  - apply imem_ineg in H.
    replace (- - a w)%Z with (a w) in H by lia. exact H.
  - exact H.
Qed.

Lemma zneg_le_swap : forall a b, zle (zneg a) b <-> zle (zneg b) a.
Proof. intros [|x|] [|y|]; simpl; try tauto; lia. Qed.

Lemma alphai_neg : forall (V : powerset Z),
  alphai (fun v => V (- v)%Z) = ineg (alphai V).
Proof.
  intros V. unfold alphai, ineg. cbn [fst snd].
  f_equal.
  - (* zinfS of negated set = zneg of zsup *)
    apply zle_antisym.
    + rewrite <- (zneg_involutive (zinfS (finset (fun v => V (- v)%Z)))).
      apply zneg_antitone.
      apply zsup_least. intros x [w [Hw Heq]]. subst.
      rewrite <- (zneg_involutive (Fin w)).
      apply zneg_antitone.
      apply zinfS_lb. exists (- w)%Z.
      split; [|reflexivity].
      replace (- - w)%Z with w by lia. exact Hw.
    + apply zinfS_greatest. intros x [v [Hv Heq]]. subst.
      apply zneg_le_swap.
      apply zsup_ub. exists (- v)%Z. split; [exact Hv | reflexivity].
  - apply zle_antisym.
    + apply zsup_least. intros x [v [Hv Heq]]. subst.
      rewrite <- (zneg_involutive (Fin v)).
      apply zneg_antitone.
      apply zinfS_lb. exists (- v)%Z. split; [exact Hv | reflexivity].
    + rewrite <- (zneg_involutive (zsup (finset (fun v => V (- v)%Z)))).
      apply zneg_antitone.
      apply zinfS_greatest. intros x [w [Hw Heq]]. subst.
      apply zneg_le_swap.
      apply zsup_ub. exists (- w)%Z.
      split; [|reflexivity].
      replace (- - w)%Z with w by lia. exact Hw.
Qed.

Lemma bestR_sflip : forall (R : powerset (Asn V3)) f d w,
  bestR R (sflip f d) w = sflip f (bestR (fun a => R (aflip f a)) d) w.
Proof.
  intros R f d w. unfold sflip at 2.
  destruct (f w) eqn:Ef.
  - (* flipped variable *)
    unfold bestR, ihull.
    rewrite <- alphai_neg.
    apply alphai_ext. intros v. split.
    + intros [asn [[Hb HR] Hv]].
      exists (aflip f asn). split.
      * split.
        -- apply ibox_sflip in Hb. exact Hb.
        -- rewrite aflip_involutive. exact HR.
      * unfold aflip. rewrite Ef. lia.
    + intros [asn [[Hb HR] Hv]].
      exists (aflip f asn). split.
      * split.
        -- apply ibox_sflip. rewrite aflip_involutive. exact Hb.
        -- exact HR.
      * unfold aflip. rewrite Ef. lia.
  - unfold bestR, ihull.
    apply alphai_ext. intros v. split.
    + intros [asn [[Hb HR] Hv]].
      exists (aflip f asn). split.
      * split.
        -- apply ibox_sflip in Hb. exact Hb.
        -- rewrite aflip_involutive. exact HR.
      * unfold aflip. rewrite Ef. exact Hv.
    + intros [asn [[Hb HR] Hv]].
      exists (aflip f asn). split.
      * split.
        -- apply ibox_sflip. rewrite aflip_involutive. exact Hb.
        -- exact HR.
      * unfold aflip. rewrite Ef. exact Hv.
Qed.

Lemma ieq_ineg : forall i j, ieq i j -> ieq (ineg i) (ineg j).
Proof.
  intros i j [[H1 H2]|H].
  - left. split; apply isbot_ineg; assumption.
  - right. congruence.
Qed.

Lemma sflip_proper : forall f (a b : istore V3),
  eqI V3 a b -> eqI V3 (sflip f a) (sflip f b).
Proof.
  intros f a b [[H1 H2]|H].
  - left. split.
    + destruct H1 as [w Hw]. exists w. unfold sflip.
      destruct (f w); [apply isbot_ineg; exact Hw | exact Hw].
    + destruct H2 as [w Hw]. exists w. unfold sflip.
      destruct (f w); [apply isbot_ineg; exact Hw | exact Hw].
  - right. intros w. unfold sflip. destruct (f w).
    + apply ieq_ineg, H.
    + apply H.
Qed.

(* Conjugates of best propagators are best for the flipped relation. *)
Lemma conj_best : forall (R : powerset (Asn V3)) (f : V3 -> bool)
                         (prop : istore V3 -> istore V3),
  (forall d, eqI V3 (prop d) (bestR R d)) ->
  forall d, eqI V3 (sflip f (prop (sflip f d)))
                   (bestR (fun a => R (aflip f a)) d).
Proof.
  intros R f prop Hbest d.
  eapply eqI_trans3.
  - apply sflip_proper. apply (Hbest (sflip f d)).
  - apply eqI_of_pointwise. intros w.
    unfold sflip at 1.
    rewrite (bestR_sflip R f d w).
    unfold sflip. destruct (f w).
    + apply ineg_involutive.
    + reflexivity.
Qed.

(* ---------- Pre-meet on one variable = relation restriction ---------- *)

Definition smeet1 (w0 : V3) (j : Itv) (d : istore V3) : istore V3 :=
  vupd d w0 (imeet (d w0) j).

Lemma ibox_smeet1 : forall w0 j d a,
  ibox (smeet1 w0 j d) a <-> (ibox d a /\ imem (a w0) j).
Proof.
  intros w0 j d a. split.
  - intros H. split.
    + intros w. specialize (H w). unfold smeet1, vupd in H.
      destruct (V3_eq_dec w w0) as [->|Hne]; [|exact H].
      apply imem_imeet in H. tauto.
    + specialize (H w0). unfold smeet1, vupd in H.
      destruct (V3_eq_dec w0 w0) as [_|Hne]; [|congruence].
      apply imem_imeet in H. tauto.
  - intros [Hb Hm] w. unfold smeet1, vupd.
    destruct (V3_eq_dec w w0) as [->|Hne]; [|apply Hb].
    apply imem_imeet. split; [apply Hb | exact Hm].
Qed.

Lemma bestR_smeet1 : forall (R : powerset (Asn V3)) w0 j d w,
  bestR R (smeet1 w0 j d) w = bestR (fun a => R a /\ imem (a w0) j) d w.
Proof.
  intros R w0 j d w. apply bestR_ext.
  intros asn. rewrite ibox_smeet1. tauto.
Qed.

(* ---------- eqI congruence of the store join ---------- *)

Lemma eqI_sym3 : forall (a b : istore V3), eqI V3 a b -> eqI V3 b a.
Proof. exact (oeq_sym (o := I_OSet V3)). Qed.

Lemma isbotIb_proper : forall a b, eqI V3 a b -> isbotIb a = isbotIb b.
Proof.
  intros a b H.
  destruct (isbotIb a) eqn:Ea; destruct (isbotIb b) eqn:Eb; try reflexivity.
  - apply isbotIb_true in Ea. apply isbotIb_false in Eb.
    exfalso. apply Eb. exact (eqI_isbotI a b H Ea).
  - apply isbotIb_false in Ea. apply isbotIb_true in Eb.
    exfalso. apply Ea. exact (eqI_isbotI b a (eqI_sym3 a b H) Eb).
Qed.

Lemma eqI_nonbot_pointwise : forall (a b : istore V3),
  ~ isbotI V3 a -> eqI V3 a b -> forall w, a w = b w.
Proof.
  intros a b Hnb [[H1 _]|H] w; [contradiction|].
  destruct (H w) as [[Hb _]|He]; [|exact He].
  exfalso. apply Hnb. exists w. exact Hb.
Qed.

Lemma sjoin_proper : forall a a' b b',
  eqI V3 a a' -> eqI V3 b b' -> eqI V3 (sjoin a b) (sjoin a' b').
Proof.
  intros a a' b b' Ha Hb. unfold sjoin.
  rewrite <- (isbotIb_proper a a' Ha), <- (isbotIb_proper b b' Hb).
  destruct (isbotIb a) eqn:Ea; [exact Hb|].
  destruct (isbotIb b) eqn:Eb; [exact Ha|].
  apply isbotIb_false in Ea. apply isbotIb_false in Eb.
  apply eqI_of_pointwise. intros w.
  rewrite (eqI_nonbot_pointwise a a' Ea Ha w).
  rewrite (eqI_nonbot_pointwise b b' Eb Hb w).
  reflexivity.
Qed.

(* ---------- Variable pair flips ---------- *)

Definition flip2 (u v : V3) : V3 -> bool :=
  fun w => if V3_eq_dec w u then true else if V3_eq_dec w v then true else false.

Lemma flip2_at_u : forall u v, flip2 u v u = true.
Proof.
  intros u v. unfold flip2. destruct (V3_eq_dec u u); congruence.
Qed.

Lemma flip2_at_v : forall u v, flip2 u v v = true.
Proof.
  intros u v. unfold flip2.
  destruct (V3_eq_dec v u); [reflexivity|].
  destruct (V3_eq_dec v v); congruence.
Qed.

Lemma flip2_other : forall u v w, w <> u -> w <> v -> flip2 u v w = false.
Proof.
  intros u v w H1 H2. unfold flip2.
  destruct (V3_eq_dec w u); [congruence|].
  destruct (V3_eq_dec w v); congruence.
Qed.

(* ---------- Integer sign lemmas for the four divisions ---------- *)

Lemma fdivZ_zero_num : forall z, z <> 0 -> fdivZ 0 z = 0.
Proof. intros z Hz. unfold fdivZ. apply Z.div_0_l. lia. Qed.

Lemma cdivZ_zero_num : forall z, z <> 0 -> cdivZ 0 z = 0.
Proof.
  intros z Hz. unfold cdivZ.
  replace (- 0) with 0 by lia. rewrite Z.div_0_l by lia. lia.
Qed.

Lemma tdivZ_eq_fdiv : forall y z, 0 <= y * z -> tdivZ y z = fdivZ y z.
Proof.
  intros y z H. unfold tdivZ.
  destruct (Z.leb_spec 0 (y * z)); [reflexivity | lia].
Qed.

Lemma tdivZ_eq_cdiv : forall y z, y * z < 0 -> tdivZ y z = cdivZ y z.
Proof.
  intros y z H. unfold tdivZ.
  destruct (Z.leb_spec 0 (y * z)); [lia | reflexivity].
Qed.

Lemma tdiv_q1 : forall y z, 0 <= y -> 1 <= z -> tdivZ y z = fdivZ y z.
Proof. intros y z Hy Hz. apply tdivZ_eq_fdiv. nia. Qed.

Lemma tdiv_q2 : forall y z, 0 <= y -> z <= -1 -> tdivZ y z = cdivZ y z.
Proof.
  intros y z Hy Hz.
  destruct (Z.eq_dec y 0) as [->|Hy0].
  - rewrite tdivZ_eq_fdiv by nia.
    rewrite fdivZ_zero_num, cdivZ_zero_num by lia. reflexivity.
  - apply tdivZ_eq_cdiv. nia.
Qed.

Lemma tdiv_q3 : forall y z, y <= 0 -> 1 <= z -> tdivZ y z = cdivZ y z.
Proof.
  intros y z Hy Hz.
  destruct (Z.eq_dec y 0) as [->|Hy0].
  - rewrite tdivZ_eq_fdiv by nia.
    rewrite fdivZ_zero_num, cdivZ_zero_num by lia. reflexivity.
  - apply tdivZ_eq_cdiv. nia.
Qed.

Lemma tdiv_q4 : forall y z, y <= 0 -> z <= -1 -> tdivZ y z = fdivZ y z.
Proof. intros y z Hy Hz. apply tdivZ_eq_fdiv. nia. Qed.

(* ==================== The four division propagators ==================== *)

Section DivisionPropagators.
  Variables (r p q : V3).
  Hypothesis Hrp : r <> p.
  Hypothesis Hrq : r <> q.
  Hypothesis Hpq : p <> q.

  (* Figure VI. *)
  Definition prop_fdiv (d : istore V3) : istore V3 :=
    sjoin (prop_fdivp r p q d)
          (sflip (flip2 p q) (prop_fdivp r p q (sflip (flip2 p q) d))).

  Definition prop_cdiv (d : istore V3) : istore V3 :=
    sjoin (sflip (flip2 r p) (prop_fdivp r p q (sflip (flip2 r p) d)))
          (sflip (flip2 r q) (prop_fdivp r p q (sflip (flip2 r q) d))).

  Definition prop_ediv (d : istore V3) : istore V3 :=
    sjoin (prop_fdivp r p q d)
          (sflip (flip2 r q) (prop_fdivp r p q (sflip (flip2 r q) d))).

  Definition posP (d : istore V3) := smeet1 p (Fin 0, PInf) d.
  Definition negP (d : istore V3) := smeet1 p (MInf, Fin 0) d.

  Definition prop_tdiv (d : istore V3) : istore V3 :=
    sjoin (sjoin (prop_fdivp r p q (posP d))
                 (sflip (flip2 r q)
                    (prop_fdivp r p q (sflip (flip2 r q) (posP d)))))
          (sjoin (sflip (flip2 r p)
                    (prop_fdivp r p q (sflip (flip2 r p) (negP d))))
                 (sflip (flip2 p q)
                    (prop_fdivp r p q (sflip (flip2 p q) (negP d))))).

  (* ---------- Solution-set decompositions ---------- *)

  Lemma aflip_pq : forall a,
    aflip (flip2 p q) a r = a r /\
    aflip (flip2 p q) a p = (- a p)%Z /\
    aflip (flip2 p q) a q = (- a q)%Z.
  Proof.
    intros a. unfold aflip.
    rewrite (flip2_other p q r) by congruence.
    rewrite flip2_at_u, flip2_at_v. auto.
  Qed.

  Lemma aflip_rp : forall a,
    aflip (flip2 r p) a r = (- a r)%Z /\
    aflip (flip2 r p) a p = (- a p)%Z /\
    aflip (flip2 r p) a q = a q.
  Proof.
    intros a. unfold aflip.
    rewrite (flip2_other r p q) by congruence.
    rewrite flip2_at_u, flip2_at_v. auto.
  Qed.

  Lemma aflip_rq : forall a,
    aflip (flip2 r q) a r = (- a r)%Z /\
    aflip (flip2 r q) a p = a p /\
    aflip (flip2 r q) a q = (- a q)%Z.
  Proof.
    intros a. unfold aflip.
    rewrite (flip2_other r q p) by congruence.
    rewrite flip2_at_u, flip2_at_v. auto.
  Qed.

  Lemma rel_fdiv_decomp : forall a,
    rel (MkC r p q OFdiv) a <->
    (Rfdp r p q a \/ Rfdp r p q (aflip (flip2 p q) a)).
  Proof.
    intros a. unfold rel, Rfdp. cbn [op_rel cop cx cy cz].
    destruct (aflip_pq a) as [Er [Ep Eq]]. rewrite Er, Ep, Eq.
    split.
    - intros [Hz Heq].
      destruct (Z_le_gt_dec 1 (a q)) as [Hq|Hq]; [left; auto|].
      right. split; [lia|].
      rewrite fdivZ_opp_opp by lia. exact Heq.
    - intros [[Hz Heq]|[Hz Heq]].
      + split; [lia | exact Heq].
      + split; [lia|]. rewrite fdivZ_opp_opp in Heq by lia. exact Heq.
  Qed.

  Lemma rel_cdiv_decomp : forall a,
    rel (MkC r p q OCdiv) a <->
    (Rfdp r p q (aflip (flip2 r p) a) \/ Rfdp r p q (aflip (flip2 r q) a)).
  Proof.
    intros a. unfold rel, Rfdp. cbn [op_rel cop cx cy cz].
    destruct (aflip_rp a) as [Er1 [Ep1 Eq1]]. rewrite Er1, Ep1, Eq1.
    destruct (aflip_rq a) as [Er2 [Ep2 Eq2]]. rewrite Er2, Ep2, Eq2.
    split.
    - intros [Hz Heq].
      destruct (Z_le_gt_dec 1 (a q)) as [Hq|Hq].
      + left. rewrite cdivZ_as_fdiv in Heq. split; lia.
      + right. rewrite (cdivZ_opp (a p) (a q)) in Heq by lia. split; lia.
    - intros [[Hz Heq]|[Hz Heq]].
      + split; [lia|]. rewrite cdivZ_as_fdiv. lia.
      + split; [lia|]. rewrite (cdivZ_opp (a p) (a q)) by lia. lia.
  Qed.

  Lemma rel_ediv_decomp : forall a,
    rel (MkC r p q OEdiv) a <->
    (Rfdp r p q a \/ Rfdp r p q (aflip (flip2 r q) a)).
  Proof.
    intros a. unfold rel, Rfdp. cbn [op_rel cop cx cy cz].
    destruct (aflip_rq a) as [Er [Ep Eq]]. rewrite Er, Ep, Eq.
    split.
    - intros [Hz Heq].
      destruct (Z_le_gt_dec 1 (a q)) as [Hq|Hq].
      + left.
        assert (E : (0 <? a q) = true) by (apply Z.ltb_lt; lia).
        unfold edivZ in Heq. rewrite E in Heq.
        split; [lia | exact Heq].
      + right.
        assert (E : (0 <? a q) = false) by (apply Z.ltb_ge; lia).
        unfold edivZ in Heq. rewrite E in Heq.
        rewrite (cdivZ_opp (a p) (a q)) in Heq by lia. split; lia.
    - intros [[Hz Heq]|[Hz Heq]].
      + assert (E : (0 <? a q) = true) by (apply Z.ltb_lt; lia).
        unfold edivZ. rewrite E.
        split; [lia | exact Heq].
      + assert (E : (0 <? a q) = false) by (apply Z.ltb_ge; lia).
        unfold edivZ. rewrite E.
        split; [lia|].
        rewrite (cdivZ_opp (a p) (a q)) by lia. lia.
  Qed.

  Lemma imem_pos_iff : forall v : Z, imem v (Fin 0, PInf) <-> 0 <= v.
  Proof. intros v. rewrite imem_pair. simpl. tauto. Qed.

  Lemma imem_neg_iff : forall v : Z, imem v (MInf, Fin 0) <-> v <= 0.
  Proof. intros v. rewrite imem_pair. simpl. tauto. Qed.

  Lemma rel_tdiv_decomp : forall a,
    rel (MkC r p q OTdiv) a <->
    (((Rfdp r p q a /\ imem (a p) (Fin 0, PInf)) \/
      (Rfdp r p q (aflip (flip2 r q) a) /\ imem (a p) (Fin 0, PInf))) \/
     ((Rfdp r p q (aflip (flip2 r p) a) /\ imem (a p) (MInf, Fin 0)) \/
      (Rfdp r p q (aflip (flip2 p q) a) /\ imem (a p) (MInf, Fin 0)))).
  Proof.
    intros a. unfold rel, Rfdp. cbn [op_rel cop cx cy cz].
    destruct (aflip_pq a) as [Ar1 [Ap1 Aq1]]. rewrite Ar1, Ap1, Aq1.
    destruct (aflip_rp a) as [Ar2 [Ap2 Aq2]]. rewrite Ar2, Ap2, Aq2.
    destruct (aflip_rq a) as [Ar3 [Ap3 Aq3]]. rewrite Ar3, Ap3, Aq3.
    rewrite !imem_pos_iff, !imem_neg_iff.
    split.
    - intros [Hz Heq].
      destruct (Z_le_gt_dec 0 (a p)) as [Hp|Hp];
        destruct (Z_le_gt_dec 1 (a q)) as [Hq|Hq].
      + left; left. rewrite tdiv_q1 in Heq by lia. auto.
      + left; right. rewrite tdiv_q2 in Heq by lia.
        rewrite (cdivZ_opp (a p) (a q)) in Heq by lia.
        split; [split; lia | lia].
      + right; left. rewrite tdiv_q3 in Heq by lia.
        rewrite cdivZ_as_fdiv in Heq.
        split; [split; lia | lia].
      + right; right. rewrite tdiv_q4 in Heq by lia.
        rewrite <- (fdivZ_opp_opp (a p) (a q)) in Heq by lia.
        split; [split; lia | lia].
    - intros [[[[Hz Heq] Hp]|[[Hz Heq] Hp]]|[[[Hz Heq] Hp]|[[Hz Heq] Hp]]].
      + split; [lia|]. rewrite tdiv_q1 by lia. exact Heq.
      + split; [lia|]. rewrite tdiv_q2 by lia.
        rewrite (cdivZ_opp (a p) (a q)) by lia. lia.
      + split; [lia|]. rewrite tdiv_q3 by lia.
        rewrite cdivZ_as_fdiv. lia.
      + split; [lia|]. rewrite tdiv_q4 by lia.
        rewrite <- (fdivZ_opp_opp (a p) (a q)) by lia. lia.
  Qed.

  (* ---------- The four best-propagator theorems ---------- *)

  Theorem prop_fdiv_best : forall d,
    eqI V3 (prop_fdiv d) (bestI (MkC r p q OFdiv) d).
  Proof.
    intros d. unfold prop_fdiv.
    eapply eqI_trans3.
    - apply sjoin_proper.
      + apply prop_fdivp_best; assumption.
      + apply conj_best. intros d'. apply prop_fdivp_best; assumption.
    - eapply eqI_trans3.
      + apply eqI_sym3. apply bestR_union.
      + apply eqI_of_pointwise. intros w.
        rewrite bestI_is_bestR.
        apply bestR_ext. intros asn.
        pose proof (rel_fdiv_decomp asn). tauto.
  Qed.

  Theorem prop_cdiv_best : forall d,
    eqI V3 (prop_cdiv d) (bestI (MkC r p q OCdiv) d).
  Proof.
    intros d. unfold prop_cdiv.
    eapply eqI_trans3.
    - apply sjoin_proper;
        apply conj_best; intros d'; apply prop_fdivp_best; assumption.
    - eapply eqI_trans3.
      + apply eqI_sym3. apply bestR_union.
      + apply eqI_of_pointwise. intros w.
        rewrite bestI_is_bestR.
        apply bestR_ext. intros asn.
        pose proof (rel_cdiv_decomp asn). tauto.
  Qed.

  Theorem prop_ediv_best : forall d,
    eqI V3 (prop_ediv d) (bestI (MkC r p q OEdiv) d).
  Proof.
    intros d. unfold prop_ediv.
    eapply eqI_trans3.
    - apply sjoin_proper.
      + apply prop_fdivp_best; assumption.
      + apply conj_best. intros d'. apply prop_fdivp_best; assumption.
    - eapply eqI_trans3.
      + apply eqI_sym3. apply bestR_union.
      + apply eqI_of_pointwise. intros w.
        rewrite bestI_is_bestR.
        apply bestR_ext. intros asn.
        pose proof (rel_ediv_decomp asn). tauto.
  Qed.

  Theorem prop_tdiv_best : forall d,
    eqI V3 (prop_tdiv d) (bestI (MkC r p q OTdiv) d).
  Proof.
    intros d. unfold prop_tdiv.
    eapply eqI_trans3.
    - apply sjoin_proper.
      + (* quadrants 1 and 2 *)
        eapply eqI_trans3.
        * apply sjoin_proper.
          -- eapply eqI_trans3.
             ++ apply (prop_fdivp_best r p q Hrp Hrq Hpq (posP d)).
             ++ apply eqI_of_pointwise. intros w. apply bestR_smeet1.
          -- eapply eqI_trans3.
             ++ apply (conj_best (Rfdp r p q) (flip2 r q)
                         (prop_fdivp r p q)
                         (prop_fdivp_best r p q Hrp Hrq Hpq) (posP d)).
             ++ apply eqI_of_pointwise. intros w. apply bestR_smeet1.
        * apply eqI_sym3. apply bestR_union.
      + (* quadrants 3 and 4 *)
        eapply eqI_trans3.
        * apply sjoin_proper.
          -- eapply eqI_trans3.
             ++ apply (conj_best (Rfdp r p q) (flip2 r p)
                         (prop_fdivp r p q)
                         (prop_fdivp_best r p q Hrp Hrq Hpq) (negP d)).
             ++ apply eqI_of_pointwise. intros w. apply bestR_smeet1.
          -- eapply eqI_trans3.
             ++ apply (conj_best (Rfdp r p q) (flip2 p q)
                         (prop_fdivp r p q)
                         (prop_fdivp_best r p q Hrp Hrq Hpq) (negP d)).
             ++ apply eqI_of_pointwise. intros w. apply bestR_smeet1.
        * apply eqI_sym3. apply bestR_union.
    - eapply eqI_trans3.
      + apply eqI_sym3. apply bestR_union.
      + apply eqI_of_pointwise. intros w.
        rewrite bestI_is_bestR.
        apply bestR_ext. intros asn.
        pose proof (rel_tdiv_decomp asn). tauto.
  Qed.

End DivisionPropagators.

(* ======================= CLAIM 20 ======================= *)
(* All four division propagators of Figure VI are the best propagators of
   their constraints. *)
Theorem claim20 : forall d : istore V3,
  eqI V3 (prop_fdiv Vx Vy Vz d) (bestI (MkC Vx Vy Vz OFdiv) d) /\
  eqI V3 (prop_cdiv Vx Vy Vz d) (bestI (MkC Vx Vy Vz OCdiv) d) /\
  eqI V3 (prop_ediv Vx Vy Vz d) (bestI (MkC Vx Vy Vz OEdiv) d) /\
  eqI V3 (prop_tdiv Vx Vy Vz d) (bestI (MkC Vx Vy Vz OTdiv) d).
Proof.
  intros d.
  split; [|split; [|split]].
  - apply prop_fdiv_best; congruence.
  - apply prop_cdiv_best; congruence.
  - apply prop_ediv_best; congruence.
  - apply prop_tdiv_best; congruence.
Qed.
