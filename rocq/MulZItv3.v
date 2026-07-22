(** * mul_zitv3: the multiplication propagator with INFINITE bounds

    Rocq model of the C++ [mul_zitv3] (zinterval.hpp): x = y * z over zinf
    intervals.  Constant-time structure: 4-corner product hull, zero-shaving
    of the factors when 0 is not in x, division-back by the cdiv/fdiv corner
    hull when the co-factor is sign-definite (on solutions y = x / z exactly),
    and the absolute-value bound |factor| <= |x| when it straddles zero.

    [mul_zitv3] is NOT a best transformer (no completeness), so its properties
    are proved DIRECTLY and COMPOSITIONALLY: the propagator is a functional
    composition of six narrowing steps of three kinds ([mul], [mul_back_zero],
    [mul_back_nz]); soundness, reductivity and monotonicity each compose, so
    they are proved once per step and assembled.  Properties:
      - soundness              : [mul_zitv3_soundness]   (compositional)
      - reductivity            : [mul_zitv3_reductive]   (compositional, unconditional)
      - monotonicity           : [mul_zitv3_monotone]    (compositional, unconditional)
      - completeness/singleton : [mul_zitv3_singleton_complete] *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import Concrete ZItv3 AddZItv3.
Open Scope Z_scope.

(* division-back corner hull (sound for EXACT quotients: y = x / z on
   solutions); only used on sign-definite ib *)
Definition mul_back_zitv3 (ix ib : zitv) : zitv :=
  ZItv (min_zinf (min_zinf (cdiv_zinf (lb ix) (lb ib)) (cdiv_zinf (lb ix) (ub ib)))
             (min_zinf (cdiv_zinf (ub ix) (lb ib)) (cdiv_zinf (ub ix) (ub ib))))
       (max_zinf (max_zinf (fdiv_zinf (lb ix) (lb ib)) (fdiv_zinf (lb ix) (ub ib)))
             (max_zinf (fdiv_zinf (ub ix) (lb ib)) (fdiv_zinf (ub ix) (ub ib)))).

(* |target| <= |x| window (used when the co-factor straddles 0 but 0 notin x,
   so the co-factor is a non-zero integer: |b| >= 1) *)
Definition absb_zitv (ix : zitv) : zitv :=
  ZItv (min_zinf (lb ix) (neg_zinf (ub ix))) (max_zinf (neg_zinf (lb ix)) (ub ix)).

Definition sgndefb (i : zitv) : bool := (ispos_zinf (lb i) || isneg_zinf (ub i))%bool.
Definition xnzb (i : zitv) : bool := sgndefb i.

Definition mul_zitv3 (s : zitv3) : zitv3 :=
  (* MUL *)
  let x := meet_zitv (x s) (mul_zitv (y s) (z s)) in
  let xnz := xnzb x in
  (* z.mul_back_zero(x) *)
  let z0 := if xnz then neq0_zitv (z s) else z s in
  (* y.mul_back_nz(x, z) *)
  let y0 := if sgndefb z0 then meet_zitv (y s) (mul_back_zitv3 x z0)
            else if xnz then meet_zitv (y s) (absb_zitv x)
            else y s in
  (* y.mul_back_zero(x) *)
  let y1 := if xnz then neq0_zitv y0 else y0 in
  (* z.mul_back_nz(x, y) *)
  let z1 := if sgndefb y1 then meet_zitv z0 (mul_back_zitv3 x y1)
            else if xnz then meet_zitv z0 (absb_zitv x)
            else z0 in
  (* MUL *)
  let x2 := meet_zitv x (mul_zitv y1 z1) in
  ZItv3 x2 y1 z1.

(* ================================================================== *)
(** ** Compositional structure

    [mul_zitv3] is not a best transformer (no completeness), so the closure
    machinery does not apply.  Instead it is a functional COMPOSITION of
    six narrowing steps of three kinds -- [mul] (forward), [mul_back_zero]
    and [mul_back_nz].  Soundness, reductivity and monotonicity each
    compose under functional composition, so we prove them once per step
    and assemble the global result. *)
(* ================================================================== *)

(* --- the six steps.  Each reads the (already refined) x-component from
       its input store, so the sequential data-flow is just composition. --- *)

Definition step_mul (s : zitv3) : zitv3 :=          (* MUL: refine x by the y*z hull *)
  ZItv3 (meet_zitv (x s) (mul_zitv (y s) (z s))) (y s) (z s).

Definition step_zbz (s : zitv3) : zitv3 :=          (* z.mul_back_zero(x) *)
  ZItv3 (x s) (y s) (if xnzb (x s) then neq0_zitv (z s) else z s).

Definition step_ybnz (s : zitv3) : zitv3 :=         (* y.mul_back_nz(x, z) *)
  ZItv3 (x s)
      (if sgndefb (z s) then meet_zitv (y s) (mul_back_zitv3 (x s) (z s))
       else if xnzb (x s) then meet_zitv (y s) (absb_zitv (x s))
       else y s)
      (z s).

Definition step_ybz (s : zitv3) : zitv3 :=          (* y.mul_back_zero(x) *)
  ZItv3 (x s) (if xnzb (x s) then neq0_zitv (y s) else y s) (z s).

Definition step_zbnz (s : zitv3) : zitv3 :=         (* z.mul_back_nz(x, y) *)
  ZItv3 (x s) (y s)
      (if sgndefb (y s) then meet_zitv (z s) (mul_back_zitv3 (x s) (y s))
       else if xnzb (x s) then meet_zitv (z s) (absb_zitv (x s))
       else z s).

(* the propagator as the six-fold composition *)
Definition mul_zitv3_pipe (s : zitv3) : zitv3 :=
  step_mul (step_zbnz (step_ybz (step_ybnz (step_zbz (step_mul s))))).

Lemma mul_zitv3_is_pipe : forall s, mul_zitv3 s = mul_zitv3_pipe s.
Proof. reflexivity. Qed.

(* --- the three properties as predicates on store transformers --- *)
Definition Sound (f : zitv3 -> zitv3) : Prop :=
  forall s vx vy vz, in_zitv3 s vx vy vz -> mul_rel vx vy vz -> in_zitv3 (f s) vx vy vz.
Definition Reductive (f : zitv3 -> zitv3) : Prop := forall s, leq_zitv3 (f s) s.
Definition Monotone (f : zitv3 -> zitv3) : Prop :=
  forall s t, leq_zitv3 s t -> leq_zitv3 (f s) (f t).

(* each property is closed under functional composition *)
Lemma Sound_comp : forall f g, Sound f -> Sound g -> Sound (fun s => g (f s)).
Proof. intros f g Hf Hg s vx vy vz Hin Hm. apply Hg; [ apply Hf | ]; assumption. Qed.
Lemma Reductive_comp : forall f g, Reductive f -> Reductive g -> Reductive (fun s => g (f s)).
Proof. intros f g Hf Hg s. eapply leq_zitv_transitivityitivity; [ apply Hg | apply Hf ]. Qed.
Lemma Monotone_comp : forall f g, Monotone f -> Monotone g -> Monotone (fun s => g (f s)).
Proof. intros f g Hf Hg s t Hst. apply Hg, Hf, Hst. Qed.

(* the zero-shave only moves bounds inward *)
Lemma neq0_leq_zitv3 : forall i, leq_zitv (neq0_zitv i) i.
Proof.
  intros [l u]; apply leq_zitv_intro; cbn [lb ub].
  - destruct l as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
  - destruct u as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reductivity of each step, composed                              *)
(* ------------------------------------------------------------------ *)

(* every step refines exactly one component (via [meet_zitv]/[neq0_zitv], both
   below the original) and leaves the others fixed *)
Ltac prove_reductive :=
  intro s; apply leq_zitv3_intro; cbn [x y z];
  repeat (match goal with |- context[if ?b then _ else _] => destruct b end);
  first [ apply leq_zitv_reflexivity | apply neq0_leq_zitv3 | apply inter_leq_zitv_l ].

Lemma step_mul_reductive  : Reductive step_mul.  Proof. unfold Reductive, step_mul;  prove_reductive. Qed.
Lemma step_zbz_reductive  : Reductive step_zbz.  Proof. unfold Reductive, step_zbz;  prove_reductive. Qed.
Lemma step_ybnz_reductive : Reductive step_ybnz. Proof. unfold Reductive, step_ybnz; prove_reductive. Qed.
Lemma step_ybz_reductive  : Reductive step_ybz.  Proof. unfold Reductive, step_ybz;  prove_reductive. Qed.
Lemma step_zbnz_reductive : Reductive step_zbnz. Proof. unfold Reductive, step_zbnz; prove_reductive. Qed.

Lemma mul_zitv3_pipe_reductive : Reductive mul_zitv3_pipe.
Proof.
  unfold mul_zitv3_pipe.
  apply Reductive_comp; [ | apply step_mul_reductive ].
  apply Reductive_comp; [ | apply step_zbnz_reductive ].
  apply Reductive_comp; [ | apply step_ybz_reductive ].
  apply Reductive_comp; [ | apply step_ybnz_reductive ].
  apply Reductive_comp; [ apply step_mul_reductive | apply step_zbz_reductive ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Soundness: corner lemmas, then each step, composed              *)
(* ------------------------------------------------------------------ *)

(* stage 1: collapse the second factor's interval onto the point vz *)
Lemma mul_zinf_z_lb : forall A lz hz vz,
  leq_zinf lz (Fin vz) -> leq_zinf (Fin vz) hz ->
  leq_zinf (min_zinf (mul_zinf A lz) (mul_zinf A hz)) (mul_zinf A (Fin vz)).
Proof.
  intros [a| |] [c| |] [d| |] vz Hc Hd; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 a); nia).
Qed.

Lemma mul_zinf_z_ub : forall A lz hz vz,
  leq_zinf lz (Fin vz) -> leq_zinf (Fin vz) hz ->
  leq_zinf (mul_zinf A (Fin vz)) (max_zinf (mul_zinf A lz) (mul_zinf A hz)).
Proof.
  intros [a| |] [c| |] [d| |] vz Hc Hd; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 a); nia).
Qed.

(* stage 2: collapse the first factor's interval onto the point vy *)
Lemma mul_zinf_point_lb : forall ly hy vy vz,
  leq_zinf ly (Fin vy) -> leq_zinf (Fin vy) hy ->
  leq_zinf (min_zinf (mul_zinf ly (Fin vz)) (mul_zinf hy (Fin vz))) (Fin (vy * vz)).
Proof.
  intros [a| |] [b| |] vy vz Ha Hb; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 vz); nia).
Qed.

Lemma mul_zinf_point_ub : forall ly hy vy vz,
  leq_zinf ly (Fin vy) -> leq_zinf (Fin vy) hy ->
  leq_zinf (Fin (vy * vz)) (max_zinf (mul_zinf ly (Fin vz)) (mul_zinf hy (Fin vz))).
Proof.
  intros [a| |] [b| |] vy vz Ha Hb; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 vz); nia).
Qed.

Lemma mul_zitv_soundness : forall iy iz vy vz,
  in_zitv iy vy -> in_zitv iz vz -> in_zitv (mul_zitv iy iz) (vy * vz).
Proof.
  intros [ly hy] [lz hz] vy vz [Hy1 Hy2] [Hz1 Hz2]; cbn [lb ub] in *.
  unfold mul_zitv, in_zitv; cbn [lb ub].
  split.
  - apply leq_zinf_trans with (b := min_zinf (mul_zinf ly (Fin vz)) (mul_zinf hy (Fin vz))).
    + apply min_zinf_monotone; apply mul_zinf_z_lb; assumption.
    + apply mul_zinf_point_lb; assumption.
  - apply leq_zinf_trans with (b := max_zinf (mul_zinf ly (Fin vz)) (mul_zinf hy (Fin vz))).
    + apply mul_zinf_point_ub; assumption.
    + apply max_zinf_monotone; apply mul_zinf_z_ub; assumption.
Qed.

Lemma neq0_zitv3_soundness : forall i v, in_zitv i v -> v <> 0 -> in_zitv (neq0_zitv i) v.
Proof.
  intros [l u] v [H1 H2] Hv; unfold neq0_zitv, in_zitv in *; cbn [lb ub] in *; split.
  - destruct l as [a| |]; cbn in *; try easy.
    destruct (Z.eqb_spec a 0); cbn; lia.
  - destruct u as [b| |]; cbn in *; try easy.
    destruct (Z.eqb_spec b 0); cbn; lia.
Qed.

(* a sign-definite interval in_zitv only strictly-signed values *)
Lemma sgndefb_sign : forall i v, sgndefb i = true -> in_zitv i v -> v < 0 \/ 0 < v.
Proof.
  intros [l u] v Hs [H1 H2]; unfold sgndefb in Hs; cbn [lb ub] in *.
  apply Bool.orb_true_iff in Hs; destruct Hs as [Hs|Hs].
  - destruct l as [a| |]; cbn in *; try easy.
    apply Z.ltb_lt in Hs; lia.
  - destruct u as [b| |]; cbn in *; try easy.
    apply Z.ltb_lt in Hs; lia.
Qed.

Lemma mul_back_zitv3_soundness : forall ix ib vx vb vq,
  in_zitv ix vx -> in_zitv ib vb -> sgndefb ib = true -> vx = vq * vb ->
  in_zitv (mul_back_zitv3 ix ib) vq.
Proof.
  intros [lx hx] [llb hb] vx vb vq [Hx1 Hx2] [Hb1 Hb2] Hsgn Heq.
  unfold sgndefb in Hsgn; cbn [lb ub] in *.
  apply Bool.orb_true_iff in Hsgn.
  unfold mul_back_zitv3, in_zitv; cbn [lb ub].
  destruct Hsgn as [Hp|Hn].
  - destruct llb as [l| |]; cbn in Hb1, Hp; [|destruct Hb1|discriminate].
    apply Z.ltb_lt in Hp.
    split.
    + apply leq_zinf_min_zinf4.
      destruct lx as [a| |]; cbn in Hx1;
        [|destruct Hx1
         |left; cbn; destruct (Z.ltb_spec 0 l); [exact I|lia]].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * right; left.
        destruct hb as [u| |]; cbn in Hb2; [|cbn|destruct Hb2].
        -- cbn. apply cdiv_ub; nia.
        -- destruct (Z.ltb_spec 0 a); cbn; nia.
      * left. cbn. apply cdiv_ub; nia.
    + apply leq_zinf_max_zinf4.
      destruct hx as [B| |]; cbn in Hx2;
        [|right; right; left; cbn; destruct (Z.ltb_spec 0 l); [exact I|lia]
         |destruct Hx2].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * right; right; left. cbn. apply Z.div_le_lower_bound; nia.
      * right; right; right.
        destruct hb as [u| |]; cbn in Hb2; [|cbn|destruct Hb2].
        -- cbn. apply Z.div_le_lower_bound; nia.
        -- destruct (Z.ltb_spec B 0); cbn; lia.
  - destruct hb as [u| |]; cbn in Hb2, Hn; [|discriminate|destruct Hb2].
    apply Z.ltb_lt in Hn.
    split.
    + apply leq_zinf_min_zinf4.
      destruct hx as [B| |]; cbn in Hx2;
        [|right; right; right; cbn; destruct (Z.ltb_spec 0 u); [lia|exact I]
         |destruct Hx2].
      destruct (Z.le_gt_cases vq 0) as [Hq|Hq].
      * right; right; right. cbn. apply cdiv_ub_neg; nia.
      * right; right; left.
        destruct llb as [l| |]; cbn in Hb1; [|destruct Hb1|cbn].
        -- cbn. apply cdiv_ub_neg; nia.
        -- destruct (Z.ltb_spec B 0); cbn; lia.
    + apply leq_zinf_max_zinf4.
      destruct lx as [a| |]; cbn in Hx1;
        [|destruct Hx1
         |right; left; cbn; destruct (Z.ltb_spec 0 u); [lia|exact I]].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * right; left. cbn. apply fdiv_lb_neg; nia.
      * left.
        destruct llb as [l| |]; cbn in Hb1; [|destruct Hb1|cbn].
        -- cbn. apply fdiv_lb_neg; nia.
        -- destruct (Z.ltb_spec 0 a); cbn; lia.
Qed.

(* |vq| <= |vx| window: vx = vq * vb with a non-zero integer vb *)
Lemma absb_zitv_soundness : forall ix vx vb vq,
  in_zitv ix vx -> vx = vq * vb -> vb <> 0 -> in_zitv (absb_zitv ix) vq.
Proof.
  intros [lx hx] vx vb vq [H1 H2] Heq Hb; cbn [lb ub] in *.
  unfold absb_zitv, in_zitv, neg_zinf; cbn [lb ub].
  assert (Hd : vb <= -1 \/ 1 <= vb) by lia.
  split.
  - destruct lx as [a| |]; destruct hx as [B| |]; cbn in *; try easy;
    destruct Hd as [Hd|Hd]; destruct (Z.le_gt_cases 0 vq); nia.
  - destruct lx as [a| |]; destruct hx as [B| |]; cbn in *; try easy;
    destruct Hd as [Hd|Hd]; destruct (Z.le_gt_cases 0 vq); nia.
Qed.

(* --- soundness of each step (each preserves the multiplication solutions) --- *)

Lemma step_mul_sound : Sound step_mul.
Proof.
  unfold Sound, mul_rel. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_mul, in_zitv3; cbn [x y z].
  split; [ | split; [exact Hy | exact Hz] ].
  apply contains_inter; [exact Hx | rewrite Heq; apply mul_zitv_soundness; assumption].
Qed.

Lemma step_zbz_sound : Sound step_zbz.
Proof.
  unfold Sound, mul_rel. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_zbz, in_zitv3; cbn [x y z]. split; [exact Hx | split; [exact Hy | ]].
  destruct (xnzb (x s)) eqn:E; [ | exact Hz ].
  unfold xnzb in E.
  assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx E Hx); lia).
  assert (Hvz : vz <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
  apply neq0_zitv3_soundness; [ exact Hz | exact Hvz ].
Qed.

Lemma step_ybnz_sound : Sound step_ybnz.
Proof.
  unfold Sound, mul_rel. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_ybnz, in_zitv3; cbn [x y z]. split; [exact Hx | split; [ | exact Hz]].
  destruct (sgndefb (z s)) eqn:Ez.
  - apply contains_inter; [exact Hy | eapply mul_back_zitv3_soundness; [exact Hx | exact Hz | exact Ez | exact Heq]].
  - destruct (xnzb (x s)) eqn:Ex; [ | exact Hy].
    unfold xnzb in Ex.
    assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx Ex Hx); lia).
    assert (Hvz : vz <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
    apply contains_inter; [exact Hy | eapply absb_zitv_soundness; [exact Hx | exact Heq | exact Hvz]].
Qed.

Lemma step_ybz_sound : Sound step_ybz.
Proof.
  unfold Sound, mul_rel. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_ybz, in_zitv3; cbn [x y z]. split; [exact Hx | split; [ | exact Hz]].
  destruct (xnzb (x s)) eqn:E; [ | exact Hy].
  unfold xnzb in E.
  assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx E Hx); lia).
  assert (Hvy : vy <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
  apply neq0_zitv3_soundness; [ exact Hy | exact Hvy ].
Qed.

Lemma step_zbnz_sound : Sound step_zbnz.
Proof.
  unfold Sound, mul_rel. intros s vx vy vz (Hx & Hy & Hz) Heq.
  assert (Heq' : vx = vz * vy) by (rewrite Heq; ring).
  unfold step_zbnz, in_zitv3; cbn [x y z]. split; [exact Hx | split; [exact Hy | ]].
  destruct (sgndefb (y s)) eqn:Ey.
  - apply contains_inter; [exact Hz | eapply mul_back_zitv3_soundness; [exact Hx | exact Hy | exact Ey | exact Heq']].
  - destruct (xnzb (x s)) eqn:Ex; [ | exact Hz].
    unfold xnzb in Ex.
    assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx Ex Hx); lia).
    assert (Hvy : vy <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
    apply contains_inter; [exact Hz | eapply absb_zitv_soundness; [exact Hx | exact Heq' | exact Hvy]].
Qed.

Lemma mul_zitv3_pipe_soundness : Sound mul_zitv3_pipe.
Proof.
  unfold mul_zitv3_pipe.
  apply Sound_comp; [ | apply step_mul_sound ].
  apply Sound_comp; [ | apply step_zbnz_sound ].
  apply Sound_comp; [ | apply step_ybz_sound ].
  apply Sound_comp; [ | apply step_ybnz_sound ].
  apply Sound_comp; [ apply step_mul_sound | apply step_zbz_sound ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Monotonicity: corner lemmas, then each step, composed           *)
(* ------------------------------------------------------------------ *)

(* --- zinf order / sign utilities --- *)
Lemma ne_lo_le_hi : forall i, is_not_bot_zitv i = true -> leq_zinf (lb i) (ub i).
Proof. intros [[a| |] [b| |]]; cbn; try easy. intro H; apply Z.leb_le in H; lia. Qed.

Lemma ne_leq_zitv3 : forall i j, leq_zitv i j -> is_not_bot_zitv i = true -> is_not_bot_zitv j = true.
Proof.
  intros i j Hij Hne. apply (all_is_geq_bot_zitv i j Hne) in Hij as [Hl Hh].
  exact (contains_not_bot_implies_not_bot_zitv i j Hne Hl Hh).
Qed.

Ltac bsolve :=
  repeat match goal with
    | H : (_ || _)%bool = true |- _ => apply orb_true_iff in H; destruct H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : false = true |- _ => discriminate H
    end;
  first [ reflexivity
        | apply orb_true_iff; first [ left; apply Z.ltb_lt; lia | right; apply Z.ltb_lt; lia ]
        | apply Z.ltb_lt; lia ].

Lemma sgndefb_dn : forall i j, leq_zitv i j -> is_not_bot_zitv i = true -> sgndefb j = true -> sgndefb i = true.
Proof.
  intros i j Hij Hne Hs. apply (all_is_geq_bot_zitv i j Hne) in Hij as [Hl Hh].
  destruct i as [[a| |] [b| |]], j as [[c| |] [d| |]]; unfold sgndefb in *; cbn in *;
  try easy; bsolve.
Qed.

Lemma sgn_mem : forall i w, sgndefb i = true -> leq_zinf (lb i) w -> leq_zinf w (ub i) ->
  (ispos_zinf w || isneg_zinf w)%bool = true.
Proof.
  intros [[c| |] [d| |]] [w| |] Hs Hl Hh; unfold sgndefb in *; cbn in *; try easy; bsolve.
Qed.

(* the zero-shave preserves emptiness (0-bounds only widen the gap) *)
Lemma neqz3_empty : forall i, is_not_bot_zitv i = false -> is_not_bot_zitv (neq0_zitv i) = false.
Proof.
  intros [[a| |] [b| |]] H; unfold neq0_zitv, is_not_bot_zitv in *; cbn in *;
    repeat (match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end);
    subst; cbn in *; try discriminate; try reflexivity;
    apply Z.leb_gt in H; apply Z.leb_gt; lia.
Qed.

Lemma neq0_zitv3_monotone : forall i j, leq_zitv i j -> leq_zitv (neq0_zitv i) (neq0_zitv j).
Proof.
  intros i j Hij. destruct (is_not_bot_zitv i) eqn:Ei;
    [ | apply bot_is_leq_all_zitv; apply neqz3_empty; exact Ei ].
  apply (all_is_geq_bot_zitv i j Ei) in Hij as [Hl Hh].
  destruct i as [li ui], j as [lj uj]; unfold neq0_zitv; apply leq_zitv_intro; cbn [lb ub] in *.
  - destruct lj as [x| |], li as [y| |]; cbn in *; try easy;
    repeat match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end; cbn; try easy; lia.
  - destruct ui as [x| |], uj as [y| |]; cbn in *; try easy;
    repeat match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end; cbn; try easy; lia.
Qed.

Lemma zshave_zitv3_monotone : forall i j (b b' : bool), leq_zitv i j -> (b' = true -> b = true) ->
  leq_zitv (if b then neq0_zitv i else i) (if b' then neq0_zitv j else j).
Proof.
  intros i j b b' Hij Himp. destruct b' eqn:E.
  - rewrite (Himp eq_refl). apply neq0_zitv3_monotone; assumption.
  - destruct b.
    + eapply leq_zitv_transitivity; [apply neq0_leq_zitv3|assumption].
    + assumption.
Qed.

Lemma isneg_zinf3_anti : forall a b, leq_zinf a b -> leq_zinf (neg_zinf b) (neg_zinf a).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

(* absb_zitv does NOT preserve emptiness, so monotonicity is guarded by ne on the source *)
Lemma absb_zitv3_monotone : forall i j, is_not_bot_zitv i = true -> leq_zitv i j -> leq_zitv (absb_zitv i) (absb_zitv j).
Proof.
  intros i j Hne Hij. apply (all_is_geq_bot_zitv i j Hne) in Hij as [Hl Hh].
  apply leq_zitv_intro; cbn [lb ub].
  - apply min_zinf_monotone; [assumption|apply isneg_zinf3_anti; assumption].
  - apply max_zinf_monotone; [apply isneg_zinf3_anti; assumption|assumption].
Qed.

Lemma mul_zinf_comm : forall a b, mul_zinf a b = mul_zinf b a.
Proof. intros [x| |] [y| |]; cbn; try reflexivity. f_equal; ring. Qed.

Ltac zif :=
  repeat (match goal with
    | |- context[if ?x =? ?y then _ else _] => destruct (Z.eqb_spec x y)
    | |- context[if ?x <? ?y then _ else _] => destruct (Z.ltb_spec x y)
    end; cbn).

Ltac bconv :=
  repeat match goal with
    | H : (_ || _)%bool = true |- _ => apply orb_true_iff in H; destruct H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
    | H : true = true |- _ => clear H
    | H : false = true |- _ => discriminate H
    end.

Lemma mul_zinf_min_lb : forall a c v d, leq_zinf c v -> leq_zinf v d ->
  leq_zinf (min_zinf (mul_zinf a c) (mul_zinf a d)) (mul_zinf a v).
Proof.
  intros [x| |] [cc| |] [vv| |] [dd| |] H1 H2; cbn in *; try easy; zif;
  try easy; try (apply mul_min_lb; lia); try lia; try nia.
Qed.

Lemma mul_zinf_max_ub : forall a c v d, leq_zinf c v -> leq_zinf v d ->
  leq_zinf (mul_zinf a v) (max_zinf (mul_zinf a c) (mul_zinf a d)).
Proof.
  intros [x| |] [cc| |] [vv| |] [dd| |] H1 H2; cbn in *; try easy; zif;
  try easy; try (apply mul_max_ub; lia); try lia; try nia.
Qed.

Lemma mul_zitv3_lb : forall i j u v,
  leq_zinf (lb i) u -> leq_zinf u (ub i) -> leq_zinf (lb j) v -> leq_zinf v (ub j) ->
  leq_zinf (min_zinf (min_zinf (mul_zinf (lb i) (lb j)) (mul_zinf (lb i) (ub j)))
            (min_zinf (mul_zinf (ub i) (lb j)) (mul_zinf (ub i) (ub j))))
      (mul_zinf u v).
Proof.
  intros i j u v Hu1 Hu2 Hv1 Hv2.
  apply leq_zinf_trans with (min_zinf (mul_zinf (lb i) v) (mul_zinf (ub i) v)).
  - apply leq_zinf_min_zinf_glb.
    + eapply leq_zinf_trans; [apply leq_zinf_min_zinf_l | apply mul_zinf_min_lb; assumption].
    + eapply leq_zinf_trans; [apply leq_zinf_min_zinf_r | apply mul_zinf_min_lb; assumption].
  - rewrite (mul_zinf_comm (lb i) v), (mul_zinf_comm (ub i) v), (mul_zinf_comm u v).
    apply mul_zinf_min_lb; assumption.
Qed.

Lemma mul_zitv3_ub : forall i j u v,
  leq_zinf (lb i) u -> leq_zinf u (ub i) -> leq_zinf (lb j) v -> leq_zinf v (ub j) ->
  leq_zinf (mul_zinf u v)
      (max_zinf (max_zinf (mul_zinf (lb i) (lb j)) (mul_zinf (lb i) (ub j)))
            (max_zinf (mul_zinf (ub i) (lb j)) (mul_zinf (ub i) (ub j)))).
Proof.
  intros i j u v Hu1 Hu2 Hv1 Hv2.
  apply leq_zinf_trans with (max_zinf (mul_zinf (lb i) v) (mul_zinf (ub i) v)).
  - rewrite (mul_zinf_comm (lb i) v), (mul_zinf_comm (ub i) v), (mul_zinf_comm u v).
    apply mul_zinf_max_ub; assumption.
  - apply max_zinf_lub.
    + apply leq_zinf_trans with (max_zinf (mul_zinf (lb i) (lb j)) (mul_zinf (lb i) (ub j)));
        [ apply mul_zinf_max_ub; assumption | apply leq_zinf_max_zinf_l ].
    + apply leq_zinf_trans with (max_zinf (mul_zinf (ub i) (lb j)) (mul_zinf (ub i) (ub j)));
        [ apply mul_zinf_max_ub; assumption | apply leq_zinf_max_zinf_r ].
Qed.

Lemma mul_zitv3_monotone_not_bot : forall i i' j j',
  is_not_bot_zitv i = true -> is_not_bot_zitv j = true -> leq_zitv i i' -> leq_zitv j j' ->
  leq_zitv (mul_zitv i j) (mul_zitv i' j').
Proof.
  intros i i' j j' Hnei Hnej Hii' Hjj'.
  apply (all_is_geq_bot_zitv i i' Hnei) in Hii' as [Hli Hhi].
  apply (all_is_geq_bot_zitv j j' Hnej) in Hjj' as [Hlj Hhj].
  pose proof (ne_lo_le_hi _ Hnei) as Hilh. pose proof (ne_lo_le_hi _ Hnej) as Hjlh.
  assert (Ma2 : leq_zinf (lb i) (ub i')) by (eapply leq_zinf_trans; eassumption).
  assert (Mb1 : leq_zinf (lb i') (ub i)) by (eapply leq_zinf_trans; eassumption).
  assert (Mc2 : leq_zinf (lb j) (ub j')) by (eapply leq_zinf_trans; eassumption).
  assert (Md1 : leq_zinf (lb j') (ub j)) by (eapply leq_zinf_trans; eassumption).
  apply leq_zitv_intro; unfold mul_zitv; cbn [lb ub].
  - apply leq_zinf_min_zinf_glb; apply leq_zinf_min_zinf_glb; apply mul_zitv3_lb; assumption.
  - apply max_zinf_lub; apply max_zinf_lub; apply mul_zitv3_ub; assumption.
Qed.

(* --- Division corner lemmas --- *)
Lemma cdiv_zinf_num_lb : forall a u b w, (ispos_zinf w || isneg_zinf w)%bool = true ->
  leq_zinf a u -> leq_zinf u b -> leq_zinf (min_zinf (cdiv_zinf a w) (cdiv_zinf b w)) (cdiv_zinf u w).
Proof.
  intros [av| |] [uv| |] [bv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (apply cdiv_num_min; lia); try (apply cdiv_mono_pos; lia); try (apply cdiv_anti_neg; lia).
Qed.

Lemma fdiv_zinf_num_ub : forall a u b w, (ispos_zinf w || isneg_zinf w)%bool = true ->
  leq_zinf a u -> leq_zinf u b -> leq_zinf (fdiv_zinf u w) (max_zinf (fdiv_zinf a w) (fdiv_zinf b w)).
Proof.
  intros [av| |] [uv| |] [bv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (apply fdiv_num_max; lia); try (apply fdiv_mono_pos; lia); try (apply fdiv_anti_neg; lia).
Qed.

Lemma cdiv_zinf_den_lb : forall n c w d, (ispos_zinf c || isneg_zinf d)%bool = true ->
  leq_zinf c w -> leq_zinf w d -> leq_zinf (min_zinf (cdiv_zinf n c) (cdiv_zinf n d)) (cdiv_zinf n w).
Proof.
  intros [nv| |] [cv| |] [wv| |] [dv| |] Hs H1 H2; cbn in *; try easy; bconv;
  try (apply cdiv_den_min_pos; lia); try (apply cdiv_den_min_neg; lia);
  try (apply cdiv_den_pinf_pos; lia); try (apply cdiv_den_ninf_neg; lia); zif; try easy; try lia.
Qed.

Lemma fdiv_zinf_den_ub : forall n c w d, (ispos_zinf c || isneg_zinf d)%bool = true ->
  leq_zinf c w -> leq_zinf w d -> leq_zinf (fdiv_zinf n w) (max_zinf (fdiv_zinf n c) (fdiv_zinf n d)).
Proof.
  intros [nv| |] [cv| |] [wv| |] [dv| |] Hs H1 H2; cbn in *; try easy; bconv;
  try (apply fdiv_den_max_pos; lia); try (apply fdiv_den_max_neg; lia);
  try (apply fdiv_den_pinf_pos; lia); try (apply fdiv_den_ninf_neg; lia); zif; try easy; try lia.
Qed.

Lemma cdiv_zinf_abs_lb : forall xl xu u w, (ispos_zinf w || isneg_zinf w)%bool = true ->
  leq_zinf xl u -> leq_zinf u xu -> leq_zinf (min_zinf xl (neg_zinf xu)) (cdiv_zinf u w).
Proof.
  intros [lv| |] [rv| |] [uv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (match goal with |- context[cdiv ?v ?mm] => pose proof (cdiv_abs_lb v mm ltac:(lia)) end; lia).
Qed.

Lemma fdiv_zinf_abs_ub : forall xl xu u w, (ispos_zinf w || isneg_zinf w)%bool = true ->
  leq_zinf xl u -> leq_zinf u xu -> leq_zinf (fdiv_zinf u w) (max_zinf (neg_zinf xl) xu).
Proof.
  intros [lv| |] [rv| |] [uv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (match goal with |- context[?v / ?mm] => pose proof (fdiv_abs_ub v mm ltac:(lia)) end; lia).
Qed.

(* --- mul_back_zitv3 hull bounds and monotonicity --- *)
Lemma mul_back_zitv3_lb : forall ix' ib' u w,
  (ispos_zinf (lb ib') || isneg_zinf (ub ib'))%bool = true ->
  leq_zinf (lb ix') u -> leq_zinf u (ub ix') -> leq_zinf (lb ib') w -> leq_zinf w (ub ib') ->
  leq_zinf (min_zinf (min_zinf (cdiv_zinf (lb ix') (lb ib')) (cdiv_zinf (lb ix') (ub ib')))
            (min_zinf (cdiv_zinf (ub ix') (lb ib')) (cdiv_zinf (ub ix') (ub ib'))))
      (cdiv_zinf u w).
Proof.
  intros ix' ib' u w Hs Hu1 Hu2 Hw1 Hw2.
  apply leq_zinf_trans with (min_zinf (cdiv_zinf (lb ix') w) (cdiv_zinf (ub ix') w)).
  - apply leq_zinf_min_zinf_glb.
    + eapply leq_zinf_trans; [apply leq_zinf_min_zinf_l | apply cdiv_zinf_den_lb; assumption].
    + eapply leq_zinf_trans; [apply leq_zinf_min_zinf_r | apply cdiv_zinf_den_lb; assumption].
  - apply cdiv_zinf_num_lb; try assumption. exact (sgn_mem ib' w Hs Hw1 Hw2).
Qed.

Lemma mul_back_zitv3_ub : forall ix' ib' u w,
  (ispos_zinf (lb ib') || isneg_zinf (ub ib'))%bool = true ->
  leq_zinf (lb ix') u -> leq_zinf u (ub ix') -> leq_zinf (lb ib') w -> leq_zinf w (ub ib') ->
  leq_zinf (fdiv_zinf u w)
      (max_zinf (max_zinf (fdiv_zinf (lb ix') (lb ib')) (fdiv_zinf (lb ix') (ub ib')))
            (max_zinf (fdiv_zinf (ub ix') (lb ib')) (fdiv_zinf (ub ix') (ub ib')))).
Proof.
  intros ix' ib' u w Hs Hu1 Hu2 Hw1 Hw2.
  apply leq_zinf_trans with (max_zinf (fdiv_zinf (lb ix') w) (fdiv_zinf (ub ix') w)).
  - apply fdiv_zinf_num_ub; try assumption. exact (sgn_mem ib' w Hs Hw1 Hw2).
  - apply max_zinf_lub.
    + apply leq_zinf_trans with (max_zinf (fdiv_zinf (lb ix') (lb ib')) (fdiv_zinf (lb ix') (ub ib')));
        [ apply fdiv_zinf_den_ub; assumption | apply leq_zinf_max_zinf_l ].
    + apply leq_zinf_trans with (max_zinf (fdiv_zinf (ub ix') (lb ib')) (fdiv_zinf (ub ix') (ub ib')));
        [ apply fdiv_zinf_den_ub; assumption | apply leq_zinf_max_zinf_r ].
Qed.

Lemma mul_back_zitv3_mono_ne : forall ix ix' ib ib',
  is_not_bot_zitv ix = true -> is_not_bot_zitv ib = true ->
  leq_zitv ix ix' -> leq_zitv ib ib' -> sgndefb ib' = true ->
  leq_zitv (mul_back_zitv3 ix ib) (mul_back_zitv3 ix' ib').
Proof.
  intros ix ix' ib ib' Hnex Hneb Hxx' Hbb' Hs.
  apply (all_is_geq_bot_zitv ix ix' Hnex) in Hxx' as [Hxl Hxh].
  apply (all_is_geq_bot_zitv ib ib' Hneb) in Hbb' as [Hbl Hbh].
  unfold sgndefb in Hs.
  pose proof (ne_lo_le_hi _ Hnex) as Hxlh. pose proof (ne_lo_le_hi _ Hneb) as Hblh.
  assert (Ma2 : leq_zinf (lb ix) (ub ix')) by (eapply leq_zinf_trans; eassumption).
  assert (Mb1 : leq_zinf (lb ix') (ub ix)) by (eapply leq_zinf_trans; eassumption).
  assert (Mc2 : leq_zinf (lb ib) (ub ib')) by (eapply leq_zinf_trans; eassumption).
  assert (Md1 : leq_zinf (lb ib') (ub ib)) by (eapply leq_zinf_trans; eassumption).
  apply leq_zitv_intro; unfold mul_back_zitv3; cbn [lb ub].
  - apply leq_zinf_min_zinf_glb; apply leq_zinf_min_zinf_glb; apply mul_back_zitv3_lb; assumption.
  - apply max_zinf_lub; apply max_zinf_lub; apply mul_back_zitv3_ub; assumption.
Qed.

Lemma db_sub_absb : forall ix ix' ib,
  is_not_bot_zitv ix = true -> is_not_bot_zitv ib = true -> sgndefb ib = true ->
  leq_zitv ix ix' -> leq_zitv (mul_back_zitv3 ix ib) (absb_zitv ix').
Proof.
  intros ix ix' ib Hnex Hneb Hs Hxx'.
  apply (all_is_geq_bot_zitv ix ix' Hnex) in Hxx' as [Hxl Hxh].
  pose proof (ne_lo_le_hi _ Hnex) as Hxlh. pose proof (ne_lo_le_hi _ Hneb) as Hblh.
  assert (Ma2 : leq_zinf (lb ix) (ub ix')) by (eapply leq_zinf_trans; eassumption).
  assert (Mb1 : leq_zinf (lb ix') (ub ix)) by (eapply leq_zinf_trans; eassumption).
  assert (W1 : (ispos_zinf (lb ib) || isneg_zinf (lb ib))%bool = true)
    by (apply (sgn_mem ib); [assumption | apply leq_zinf_refl | assumption]).
  assert (W2 : (ispos_zinf (ub ib) || isneg_zinf (ub ib))%bool = true)
    by (apply (sgn_mem ib); [assumption | assumption | apply leq_zinf_refl]).
  apply leq_zitv_intro; unfold mul_back_zitv3, absb_zitv; cbn [lb ub].
  - apply leq_zinf_min_zinf_glb; apply leq_zinf_min_zinf_glb; apply cdiv_zinf_abs_lb; assumption.
  - apply max_zinf_lub; apply max_zinf_lub; apply fdiv_zinf_abs_ub; assumption.
Qed.

(* --- the guarded back-propagation step is monotone (source non-empty) --- *)
Lemma zshave_leq_zitv3 : forall i (b : bool), leq_zitv (if b then neq0_zitv i else i) i.
Proof. intros i [|]; [apply neq0_leq_zitv3 | apply leq_zitv_reflexivity]. Qed.

Lemma mulback_leq_zitv3 : forall iy ix ib,
  leq_zitv (if sgndefb ib then meet_zitv iy (mul_back_zitv3 ix ib)
        else if xnzb ix then meet_zitv iy (absb_zitv ix) else iy) iy.
Proof.
  intros. destruct (sgndefb ib); [apply inter_leq_zitv_l|].
  destruct (xnzb ix); [apply inter_leq_zitv_l | apply leq_zitv_reflexivity].
Qed.

Lemma mulback_monotone : forall iy iy' ix ix' ib ib',
  leq_zitv iy iy' -> leq_zitv ix ix' -> leq_zitv ib ib' ->
  is_not_bot_zitv ix = true -> is_not_bot_zitv ib = true ->
  leq_zitv (if sgndefb ib then meet_zitv iy (mul_back_zitv3 ix ib)
        else if xnzb ix then meet_zitv iy (absb_zitv ix) else iy)
       (if sgndefb ib' then meet_zitv iy' (mul_back_zitv3 ix' ib')
        else if xnzb ix' then meet_zitv iy' (absb_zitv ix') else iy').
Proof.
  intros iy iy' ix ix' ib ib' Hy Hx Hb Hnex Hneb.
  destruct (sgndefb ib') eqn:EB'.
  - rewrite (sgndefb_dn _ _ Hb Hneb EB').
    apply inter_mono; [assumption | apply mul_back_zitv3_mono_ne; assumption].
  - destruct (sgndefb ib) eqn:EB.
    + destruct (xnzb ix') eqn:EX'.
      * apply inter_mono; [assumption | apply db_sub_absb; assumption].
      * eapply leq_zitv_transitivity; [apply inter_leq_zitv_l | assumption].
    + destruct (xnzb ix') eqn:EX'.
      * assert (EX : xnzb ix = true) by (unfold xnzb in *; exact (sgndefb_dn _ _ Hx Hnex EX')).
        rewrite EX.
        apply inter_mono; [assumption | apply absb_zitv3_monotone; assumption].
      * destruct (xnzb ix) eqn:EX.
        -- eapply leq_zitv_transitivity; [apply inter_leq_zitv_l | assumption].
        -- assumption.
Qed.

(* --- every step preserves emptiness (refines one component, keeps others) --- *)
Lemma empty_inter_l : forall i j, is_not_bot_zitv i = false -> is_not_bot_zitv (meet_zitv i j) = false.
Proof.
  intros i j H. destruct (is_not_bot_zitv (meet_zitv i j)) eqn:E; [ apply ne_inter3 in E; congruence | reflexivity ].
Qed.

Lemma step_mul_empty : forall s, is_not_bot_zitv3 s = false -> is_not_bot_zitv3 (step_mul s) = false.
Proof.
  intros s H. unfold is_not_bot_zitv3, step_mul in *; cbn [x y z] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; apply empty_inter_l; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right; exact H.
  - apply andb_false_iff; right; exact H.
Qed.

Lemma step_zbz_empty : forall s, is_not_bot_zitv3 s = false -> is_not_bot_zitv3 (step_zbz s) = false.
Proof.
  intros s H. unfold is_not_bot_zitv3, step_zbz in *; cbn [x y z] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right; exact H.
  - apply andb_false_iff; right.
    destruct (xnzb (x s)); [ apply neqz3_empty; exact H | exact H ].
Qed.

Lemma step_ybnz_empty : forall s, is_not_bot_zitv3 s = false -> is_not_bot_zitv3 (step_ybnz s) = false.
Proof.
  intros s H. unfold is_not_bot_zitv3, step_ybnz in *; cbn [x y z] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right.
      destruct (sgndefb (z s)); [ apply empty_inter_l; exact H | ].
      destruct (xnzb (x s)); [ apply empty_inter_l; exact H | exact H ].
  - apply andb_false_iff; right; exact H.
Qed.

Lemma step_ybz_empty : forall s, is_not_bot_zitv3 s = false -> is_not_bot_zitv3 (step_ybz s) = false.
Proof.
  intros s H. unfold is_not_bot_zitv3, step_ybz in *; cbn [x y z] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right.
      destruct (xnzb (x s)); [ apply neqz3_empty; exact H | exact H ].
  - apply andb_false_iff; right; exact H.
Qed.

Lemma step_zbnz_empty : forall s, is_not_bot_zitv3 s = false -> is_not_bot_zitv3 (step_zbnz s) = false.
Proof.
  intros s H. unfold is_not_bot_zitv3, step_zbnz in *; cbn [x y z] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right; exact H.
  - apply andb_false_iff; right.
    destruct (sgndefb (y s)); [ apply empty_inter_l; exact H | ].
    destruct (xnzb (x s)); [ apply empty_inter_l; exact H | exact H ].
Qed.

(* --- monotonicity of each step (empty source -> bottom; else raw) --- *)

Lemma step_mul_monotone : Monotone step_mul.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (is_not_bot_zitv3 s) eqn:Es; [ | apply bot_is_leq_all_zitv3; apply step_mul_empty; exact Es ].
  apply (leq_zitv3_nobot_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (not_bot_zitv3_distributes_cw s Es) as (Ex & Ey & Ez).
  unfold step_mul; apply leq_zitv3_intro; cbn [x y z].
  - apply inter_mono; [ exact HX | apply mul_zitv3_monotone_not_bot; [exact Ey | exact Ez | exact HY | exact HZ] ].
  - exact HY.
  - exact HZ.
Qed.

Lemma step_zbz_monotone : Monotone step_zbz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (is_not_bot_zitv3 s) eqn:Es; [ | apply bot_is_leq_all_zitv3; apply step_zbz_empty; exact Es ].
  apply (leq_zitv3_nobot_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (not_bot_zitv3_distributes_cw s Es) as (Ex & Ey & Ez).
  unfold step_zbz; apply leq_zitv3_intro; cbn [x y z].
  - exact HX.
  - exact HY.
  - apply zshave_zitv3_monotone; [ exact HZ | unfold xnzb; exact (sgndefb_dn (x s) (x t) HX Ex) ].
Qed.

Lemma step_ybnz_monotone : Monotone step_ybnz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (is_not_bot_zitv3 s) eqn:Es; [ | apply bot_is_leq_all_zitv3; apply step_ybnz_empty; exact Es ].
  apply (leq_zitv3_nobot_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (not_bot_zitv3_distributes_cw s Es) as (Ex & Ey & Ez).
  unfold step_ybnz; apply leq_zitv3_intro; cbn [x y z].
  - exact HX.
  - apply mulback_monotone; [ exact HY | exact HX | exact HZ | exact Ex | exact Ez ].
  - exact HZ.
Qed.

Lemma step_ybz_monotone : Monotone step_ybz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (is_not_bot_zitv3 s) eqn:Es; [ | apply bot_is_leq_all_zitv3; apply step_ybz_empty; exact Es ].
  apply (leq_zitv3_nobot_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (not_bot_zitv3_distributes_cw s Es) as (Ex & Ey & Ez).
  unfold step_ybz; apply leq_zitv3_intro; cbn [x y z].
  - exact HX.
  - apply zshave_zitv3_monotone; [ exact HY | unfold xnzb; exact (sgndefb_dn (x s) (x t) HX Ex) ].
  - exact HZ.
Qed.

Lemma step_zbnz_monotone : Monotone step_zbnz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (is_not_bot_zitv3 s) eqn:Es; [ | apply bot_is_leq_all_zitv3; apply step_zbnz_empty; exact Es ].
  apply (leq_zitv3_nobot_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (not_bot_zitv3_distributes_cw s Es) as (Ex & Ey & Ez).
  unfold step_zbnz; apply leq_zitv3_intro; cbn [x y z].
  - exact HX.
  - exact HY.
  - apply mulback_monotone; [ exact HZ | exact HX | exact HY | exact Ex | exact Ey ].
Qed.

Lemma mul_zitv3_pipe_monotone : Monotone mul_zitv3_pipe.
Proof.
  unfold mul_zitv3_pipe.
  apply Monotone_comp; [ | apply step_mul_monotone ].
  apply Monotone_comp; [ | apply step_zbnz_monotone ].
  apply Monotone_comp; [ | apply step_ybz_monotone ].
  apply Monotone_comp; [ | apply step_ybnz_monotone ].
  apply Monotone_comp; [ apply step_mul_monotone | apply step_zbz_monotone ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem mul_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> vx = vy * vz ->
  in_zitv3 (mul_zitv3 s) vx vy vz.
Proof. intros s vx vy vz Hin Heq. rewrite mul_zitv3_is_pipe. exact (mul_zitv3_pipe_soundness s vx vy vz Hin Heq). Qed.

Theorem mul_zitv3_reductive : forall s, leq_zitv3 (mul_zitv3 s) s.
Proof. intro s. rewrite mul_zitv3_is_pipe. apply mul_zitv3_pipe_reductive. Qed.

(* UNCONDITIONAL under the quotient order: an empty output is bottom, and
   the composition of the per-step monotone maps handles the rest. *)
Theorem mul_zitv3_monotone : forall s t, leq_zitv3 s t -> leq_zitv3 (mul_zitv3 s) (mul_zitv3 t).
Proof. intros s t Hst. rewrite !mul_zitv3_is_pipe. apply mul_zitv3_pipe_monotone; exact Hst. Qed.

Theorem mul_zitv3_singleton_complete : forall s vx vy vz,
  x s = ZItv (Fin vx) (Fin vx) ->
  y s = ZItv (Fin vy) (Fin vy) ->
  z s = ZItv (Fin vz) (Fin vz) ->
  is_not_bot_zitv3 (mul_zitv3 s) = true ->
  vx = vy * vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold mul_zitv3 in Hne; cbv zeta in Hne.
  rewrite Hx, Hy, Hz in Hne.
  unfold is_not_bot_zitv3 in Hne.
  apply Bool.andb_true_iff in Hne as [Hne _].
  apply Bool.andb_true_iff in Hne as [Hnex _].
  (* the x-component is nested inter3s of the singleton hull *)
  apply ne_inter3 in Hnex.
  cbn in Hnex. apply Z.leb_le in Hnex. lia.
Qed.
