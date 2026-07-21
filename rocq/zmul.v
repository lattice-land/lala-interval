(** * zmul3: the multiplication propagator with INFINITE bounds

    Rocq model of the C++ [zmul3] (zinterval.hpp): x = y * z over Zinf
    intervals.  Constant-time structure: 4-corner product hull, zero-shaving
    of the factors when 0 is not in x, division-back by the cdiv/fdiv corner
    hull when the co-factor is sign-definite (on solutions y = x / z exactly),
    and the absolute-value bound |factor| <= |x| when it straddles zero.

    [zmul3] is NOT a best transformer (no completeness), so its properties
    are proved DIRECTLY and COMPOSITIONALLY: the propagator is a functional
    composition of six narrowing steps of three kinds ([mul], [mul_back_zero],
    [mul_back_nz]); soundness, reductivity and monotonicity each compose, so
    they are proved once per step and assembled.  Properties:
      - soundness              : [zmul3_soundness]   (compositional)
      - reductivity            : [zmul3_reductive]   (compositional, unconditional)
      - monotonicity           : [zmul3_monotone]    (compositional, unconditional)
      - completeness/singleton : [zmul3_singleton_complete] *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import inf Lemmas itv zadd.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Auxiliary operations (mirror the C++)                           *)
(* ------------------------------------------------------------------ *)

Definition zneg3 (a : Zinf) : Zinf :=
  match a with Fin v => Fin (- v) | Pinf => Ninf | Ninf => Pinf end.

(* neq_zero: shave a zero bound *)
Definition neqz3 (i : itv3) : itv3 :=
  Itv3 (if ziszero (lo3 i) then Fin 1 else lo3 i)
       (if ziszero (hi3 i) then Fin (-1) else hi3 i).

(* 4-corner product hull *)
Definition mul_hull3 (iy iz : itv3) : itv3 :=
  Itv3 (zmin (zmin (imul3 (lo3 iy) (lo3 iz)) (imul3 (lo3 iy) (hi3 iz)))
             (zmin (imul3 (hi3 iy) (lo3 iz)) (imul3 (hi3 iy) (hi3 iz))))
       (zmax (zmax (imul3 (lo3 iy) (lo3 iz)) (imul3 (lo3 iy) (hi3 iz)))
             (zmax (imul3 (hi3 iy) (lo3 iz)) (imul3 (hi3 iy) (hi3 iz)))).

(* division-back corner hull (sound for EXACT quotients: y = x / z on
   solutions); only used on sign-definite ib *)
Definition div_back3 (ix ib : itv3) : itv3 :=
  Itv3 (zmin (zmin (idivc3 (lo3 ix) (lo3 ib)) (idivc3 (lo3 ix) (hi3 ib)))
             (zmin (idivc3 (hi3 ix) (lo3 ib)) (idivc3 (hi3 ix) (hi3 ib))))
       (zmax (zmax (idivf3 (lo3 ix) (lo3 ib)) (idivf3 (lo3 ix) (hi3 ib)))
             (zmax (idivf3 (hi3 ix) (lo3 ib)) (idivf3 (hi3 ix) (hi3 ib)))).

(* |target| <= |x| window (used when the co-factor straddles 0 but 0 notin x,
   so the co-factor is a non-zero integer: |b| >= 1) *)
Definition absb3 (ix : itv3) : itv3 :=
  Itv3 (zmin (lo3 ix) (zneg3 (hi3 ix))) (zmax (zneg3 (lo3 ix)) (hi3 ix)).

Definition sgndefb (i : itv3) : bool := (zpos (lo3 i) || zneg (hi3 i))%bool.
Definition xnzb (i : itv3) : bool := sgndefb i.

(* ------------------------------------------------------------------ *)
(** ** The propagator (mirrors zmul3)                                  *)
(* ------------------------------------------------------------------ *)

Definition zmul3 (s : store3) : store3 :=
  (* MUL *)
  let x := inter3 (sx3 s) (mul_hull3 (sy3 s) (sz3 s)) in
  let xnz := xnzb x in
  (* z.mul_back_zero(x) *)
  let z0 := if xnz then neqz3 (sz3 s) else sz3 s in
  (* y.mul_back_nz(x, z) *)
  let y0 := if sgndefb z0 then inter3 (sy3 s) (div_back3 x z0)
            else if xnz then inter3 (sy3 s) (absb3 x)
            else sy3 s in
  (* y.mul_back_zero(x) *)
  let y1 := if xnz then neqz3 y0 else y0 in
  (* z.mul_back_nz(x, y) *)
  let z1 := if sgndefb y1 then inter3 z0 (div_back3 x y1)
            else if xnz then inter3 z0 (absb3 x)
            else z0 in
  (* MUL *)
  let x2 := inter3 x (mul_hull3 y1 z1) in
  St3 x2 y1 z1.

(* ================================================================== *)
(** ** Compositional structure

    [zmul3] is not a best transformer (no completeness), so the closure
    machinery does not apply.  Instead it is a functional COMPOSITION of
    six narrowing steps of three kinds -- [mul] (forward), [mul_back_zero]
    and [mul_back_nz].  Soundness, reductivity and monotonicity each
    compose under functional composition, so we prove them once per step
    and assemble the global result. *)
(* ================================================================== *)

(* the multiplication constraint *)
Definition msol (vx vy vz : Z) : Prop := vx = vy * vz.

(* --- the six steps.  Each reads the (already refined) x-component from
       its input store, so the sequential data-flow is just composition. --- *)

Definition step_mul (s : store3) : store3 :=          (* MUL: refine x by the y*z hull *)
  St3 (inter3 (sx3 s) (mul_hull3 (sy3 s) (sz3 s))) (sy3 s) (sz3 s).

Definition step_zbz (s : store3) : store3 :=          (* z.mul_back_zero(x) *)
  St3 (sx3 s) (sy3 s) (if xnzb (sx3 s) then neqz3 (sz3 s) else sz3 s).

Definition step_ybnz (s : store3) : store3 :=         (* y.mul_back_nz(x, z) *)
  St3 (sx3 s)
      (if sgndefb (sz3 s) then inter3 (sy3 s) (div_back3 (sx3 s) (sz3 s))
       else if xnzb (sx3 s) then inter3 (sy3 s) (absb3 (sx3 s))
       else sy3 s)
      (sz3 s).

Definition step_ybz (s : store3) : store3 :=          (* y.mul_back_zero(x) *)
  St3 (sx3 s) (if xnzb (sx3 s) then neqz3 (sy3 s) else sy3 s) (sz3 s).

Definition step_zbnz (s : store3) : store3 :=         (* z.mul_back_nz(x, y) *)
  St3 (sx3 s) (sy3 s)
      (if sgndefb (sy3 s) then inter3 (sz3 s) (div_back3 (sx3 s) (sy3 s))
       else if xnzb (sx3 s) then inter3 (sz3 s) (absb3 (sx3 s))
       else sz3 s).

(* the propagator as the six-fold composition *)
Definition zmul3_pipe (s : store3) : store3 :=
  step_mul (step_zbnz (step_ybz (step_ybnz (step_zbz (step_mul s))))).

Lemma zmul3_is_pipe : forall s, zmul3 s = zmul3_pipe s.
Proof. reflexivity. Qed.

(* --- the three properties as predicates on store transformers --- *)
Definition Sound (f : store3 -> store3) : Prop :=
  forall s vx vy vz, in_store3 s vx vy vz -> msol vx vy vz -> in_store3 (f s) vx vy vz.
Definition Reductive (f : store3 -> store3) : Prop := forall s, sle3 (f s) s.
Definition Monotone (f : store3 -> store3) : Prop :=
  forall s t, sle3 s t -> sle3 (f s) (f t).

(* each property is closed under functional composition *)
Lemma Sound_comp : forall f g, Sound f -> Sound g -> Sound (fun s => g (f s)).
Proof. intros f g Hf Hg s vx vy vz Hin Hm. apply Hg; [ apply Hf | ]; assumption. Qed.
Lemma Reductive_comp : forall f g, Reductive f -> Reductive g -> Reductive (fun s => g (f s)).
Proof. intros f g Hf Hg s. eapply sle3_trans; [ apply Hg | apply Hf ]. Qed.
Lemma Monotone_comp : forall f g, Monotone f -> Monotone g -> Monotone (fun s => g (f s)).
Proof. intros f g Hf Hg s t Hst. apply Hg, Hf, Hst. Qed.

(* the zero-shave only moves bounds inward *)
Lemma neqz3_ile3 : forall i, ile3 (neqz3 i) i.
Proof.
  intros [l u]; apply ile3_intro; cbn [lo3 hi3].
  - destruct l as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
  - destruct u as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reductivity of each step, composed                              *)
(* ------------------------------------------------------------------ *)

(* every step refines exactly one component (via [inter3]/[neqz3], both
   below the original) and leaves the others fixed *)
Ltac prove_reductive :=
  intro s; apply sle3_intro; cbn [sx3 sy3 sz3];
  repeat (match goal with |- context[if ?b then _ else _] => destruct b end);
  first [ apply ile3_refl | apply neqz3_ile3 | apply inter3_ile3_l ].

Lemma step_mul_reductive  : Reductive step_mul.  Proof. unfold Reductive, step_mul;  prove_reductive. Qed.
Lemma step_zbz_reductive  : Reductive step_zbz.  Proof. unfold Reductive, step_zbz;  prove_reductive. Qed.
Lemma step_ybnz_reductive : Reductive step_ybnz. Proof. unfold Reductive, step_ybnz; prove_reductive. Qed.
Lemma step_ybz_reductive  : Reductive step_ybz.  Proof. unfold Reductive, step_ybz;  prove_reductive. Qed.
Lemma step_zbnz_reductive : Reductive step_zbnz. Proof. unfold Reductive, step_zbnz; prove_reductive. Qed.

Lemma zmul3_pipe_reductive : Reductive zmul3_pipe.
Proof.
  unfold zmul3_pipe.
  apply Reductive_comp; [ | apply step_mul_reductive ].
  apply Reductive_comp; [ | apply step_zbnz_reductive ].
  apply Reductive_comp; [ | apply step_ybz_reductive ].
  apply Reductive_comp; [ | apply step_ybnz_reductive ].
  apply Reductive_comp; [ apply step_mul_reductive | apply step_zbz_reductive ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Soundness: corner lemmas, then each step, composed              *)
(* ------------------------------------------------------------------ *)

Lemma zmin_zle_r3 : forall a b, zle (zmin a b) b.
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma zmax_zle_r3 : forall a b, zle b (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

(* the 4-corner min is below any element that one corner is below *)
Lemma zle_zmin4 : forall m1 m2 m3 m4 t,
  zle m1 t \/ zle m2 t \/ zle m3 t \/ zle m4 t ->
  zle (zmin (zmin m1 m2) (zmin m3 m4)) t.
Proof.
  intros m1 m2 m3 m4 t [H|[H|[H|H]]].
  - eapply zle_trans; [apply zle_zmin_l|]. eapply zle_trans; [apply zle_zmin_l|]. exact H.
  - eapply zle_trans; [apply zle_zmin_l|]. eapply zle_trans; [apply zmin_zle_r3|]. exact H.
  - eapply zle_trans; [apply zmin_zle_r3|]. eapply zle_trans; [apply zle_zmin_l|]. exact H.
  - eapply zle_trans; [apply zmin_zle_r3|]. eapply zle_trans; [apply zmin_zle_r3|]. exact H.
Qed.

Lemma zle_zmax4 : forall m1 m2 m3 m4 t,
  zle t m1 \/ zle t m2 \/ zle t m3 \/ zle t m4 ->
  zle t (zmax (zmax m1 m2) (zmax m3 m4)).
Proof.
  intros m1 m2 m3 m4 t [H|[H|[H|H]]].
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zle_zmax_l|]. apply zle_zmax_l.
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zmax_zle_r3|]. apply zle_zmax_l.
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zle_zmax_l|]. apply zmax_zle_r3.
  - eapply zle_trans; [exact H|]. eapply zle_trans; [apply zmax_zle_r3|]. apply zmax_zle_r3.
Qed.

(* stage 1: collapse the second factor's interval onto the point vz *)
Lemma imul3_z_lb : forall A lz hz vz,
  zle lz (Fin vz) -> zle (Fin vz) hz ->
  zle (zmin (imul3 A lz) (imul3 A hz)) (imul3 A (Fin vz)).
Proof.
  intros [a| |] [c| |] [d| |] vz Hc Hd; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 a); nia).
Qed.

Lemma imul3_z_ub : forall A lz hz vz,
  zle lz (Fin vz) -> zle (Fin vz) hz ->
  zle (imul3 A (Fin vz)) (zmax (imul3 A lz) (imul3 A hz)).
Proof.
  intros [a| |] [c| |] [d| |] vz Hc Hd; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 a); nia).
Qed.

(* stage 2: collapse the first factor's interval onto the point vy *)
Lemma imul3_point_lb : forall ly hy vy vz,
  zle ly (Fin vy) -> zle (Fin vy) hy ->
  zle (zmin (imul3 ly (Fin vz)) (imul3 hy (Fin vz))) (Fin (vy * vz)).
Proof.
  intros [a| |] [b| |] vy vz Ha Hb; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 vz); nia).
Qed.

Lemma imul3_point_ub : forall ly hy vy vz,
  zle ly (Fin vy) -> zle (Fin vy) hy ->
  zle (Fin (vy * vz)) (zmax (imul3 ly (Fin vz)) (imul3 hy (Fin vz))).
Proof.
  intros [a| |] [b| |] vy vz Ha Hb; cbn in *; try easy;
  repeat (match goal with
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y); subst
    | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
    end; cbn); try easy; try lia;
  try (destruct (Z.le_gt_cases 0 vz); nia).
Qed.

Lemma mul_hull3_sound : forall iy iz vy vz,
  mem3 iy vy -> mem3 iz vz -> mem3 (mul_hull3 iy iz) (vy * vz).
Proof.
  intros [ly hy] [lz hz] vy vz [Hy1 Hy2] [Hz1 Hz2]; cbn [lo3 hi3] in *.
  unfold mul_hull3, mem3; cbn [lo3 hi3].
  split.
  - apply zle_trans with (b := zmin (imul3 ly (Fin vz)) (imul3 hy (Fin vz))).
    + apply zmin_mono; apply imul3_z_lb; assumption.
    + apply imul3_point_lb; assumption.
  - apply zle_trans with (b := zmax (imul3 ly (Fin vz)) (imul3 hy (Fin vz))).
    + apply imul3_point_ub; assumption.
    + apply zmax_mono; apply imul3_z_ub; assumption.
Qed.

Lemma neqz3_sound : forall i v, mem3 i v -> v <> 0 -> mem3 (neqz3 i) v.
Proof.
  intros [l u] v [H1 H2] Hv; unfold neqz3, mem3 in *; cbn [lo3 hi3] in *; split.
  - destruct l as [a| |]; cbn in *; try easy.
    destruct (Z.eqb_spec a 0); cbn; lia.
  - destruct u as [b| |]; cbn in *; try easy.
    destruct (Z.eqb_spec b 0); cbn; lia.
Qed.

(* a sign-definite interval contains only strictly-signed values *)
Lemma sgndefb_sign : forall i v, sgndefb i = true -> mem3 i v -> v < 0 \/ 0 < v.
Proof.
  intros [l u] v Hs [H1 H2]; unfold sgndefb in Hs; cbn [lo3 hi3] in *.
  apply Bool.orb_true_iff in Hs; destruct Hs as [Hs|Hs].
  - destruct l as [a| |]; cbn in *; try easy.
    apply Z.ltb_lt in Hs; lia.
  - destruct u as [b| |]; cbn in *; try easy.
    apply Z.ltb_lt in Hs; lia.
Qed.

(* division-back soundness on exact quotients, sign-definite divisor *)
Lemma div_back3_sound : forall ix ib vx vb vq,
  mem3 ix vx -> mem3 ib vb -> sgndefb ib = true -> vx = vq * vb ->
  mem3 (div_back3 ix ib) vq.
Proof.
  intros [lx hx] [lb hb] vx vb vq [Hx1 Hx2] [Hb1 Hb2] Hsgn Heq.
  unfold sgndefb in Hsgn; cbn [lo3 hi3] in *.
  apply Bool.orb_true_iff in Hsgn.
  unfold div_back3, mem3; cbn [lo3 hi3].
  destruct Hsgn as [Hp|Hn].
  - destruct lb as [l| |]; cbn in Hb1, Hp; [|destruct Hb1|discriminate].
    apply Z.ltb_lt in Hp.
    split.
    + apply zle_zmin4.
      destruct lx as [a| |]; cbn in Hx1;
        [|destruct Hx1
         |left; cbn; destruct (Z.ltb_spec 0 l); [exact I|lia]].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * right; left.
        destruct hb as [u| |]; cbn in Hb2; [|cbn|destruct Hb2].
        -- cbn. apply cdiv_ub; nia.
        -- destruct (Z.ltb_spec 0 a); cbn; nia.
      * left. cbn. apply cdiv_ub; nia.
    + apply zle_zmax4.
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
    + apply zle_zmin4.
      destruct hx as [B| |]; cbn in Hx2;
        [|right; right; right; cbn; destruct (Z.ltb_spec 0 u); [lia|exact I]
         |destruct Hx2].
      destruct (Z.le_gt_cases vq 0) as [Hq|Hq].
      * right; right; right. cbn. apply cdiv_ub_neg; nia.
      * right; right; left.
        destruct lb as [l| |]; cbn in Hb1; [|destruct Hb1|cbn].
        -- cbn. apply cdiv_ub_neg; nia.
        -- destruct (Z.ltb_spec B 0); cbn; lia.
    + apply zle_zmax4.
      destruct lx as [a| |]; cbn in Hx1;
        [|destruct Hx1
         |right; left; cbn; destruct (Z.ltb_spec 0 u); [lia|exact I]].
      destruct (Z.le_gt_cases 0 vq) as [Hq|Hq].
      * right; left. cbn. apply fdiv_lb_neg; nia.
      * left.
        destruct lb as [l| |]; cbn in Hb1; [|destruct Hb1|cbn].
        -- cbn. apply fdiv_lb_neg; nia.
        -- destruct (Z.ltb_spec 0 a); cbn; lia.
Qed.

(* |vq| <= |vx| window: vx = vq * vb with a non-zero integer vb *)
Lemma absb3_sound : forall ix vx vb vq,
  mem3 ix vx -> vx = vq * vb -> vb <> 0 -> mem3 (absb3 ix) vq.
Proof.
  intros [lx hx] vx vb vq [H1 H2] Heq Hb; cbn [lo3 hi3] in *.
  unfold absb3, mem3, zneg3; cbn [lo3 hi3].
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
  unfold Sound, msol. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_mul, in_store3; cbn [sx3 sy3 sz3].
  split; [ | split; [exact Hy | exact Hz] ].
  apply mem3_inter; [exact Hx | rewrite Heq; apply mul_hull3_sound; assumption].
Qed.

Lemma step_zbz_sound : Sound step_zbz.
Proof.
  unfold Sound, msol. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_zbz, in_store3; cbn [sx3 sy3 sz3]. split; [exact Hx | split; [exact Hy | ]].
  destruct (xnzb (sx3 s)) eqn:E; [ | exact Hz ].
  unfold xnzb in E.
  assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx E Hx); lia).
  assert (Hvz : vz <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
  apply neqz3_sound; [ exact Hz | exact Hvz ].
Qed.

Lemma step_ybnz_sound : Sound step_ybnz.
Proof.
  unfold Sound, msol. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_ybnz, in_store3; cbn [sx3 sy3 sz3]. split; [exact Hx | split; [ | exact Hz]].
  destruct (sgndefb (sz3 s)) eqn:Ez.
  - apply mem3_inter; [exact Hy | eapply div_back3_sound; [exact Hx | exact Hz | exact Ez | exact Heq]].
  - destruct (xnzb (sx3 s)) eqn:Ex; [ | exact Hy].
    unfold xnzb in Ex.
    assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx Ex Hx); lia).
    assert (Hvz : vz <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
    apply mem3_inter; [exact Hy | eapply absb3_sound; [exact Hx | exact Heq | exact Hvz]].
Qed.

Lemma step_ybz_sound : Sound step_ybz.
Proof.
  unfold Sound, msol. intros s vx vy vz (Hx & Hy & Hz) Heq.
  unfold step_ybz, in_store3; cbn [sx3 sy3 sz3]. split; [exact Hx | split; [ | exact Hz]].
  destruct (xnzb (sx3 s)) eqn:E; [ | exact Hy].
  unfold xnzb in E.
  assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx E Hx); lia).
  assert (Hvy : vy <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
  apply neqz3_sound; [ exact Hy | exact Hvy ].
Qed.

Lemma step_zbnz_sound : Sound step_zbnz.
Proof.
  unfold Sound, msol. intros s vx vy vz (Hx & Hy & Hz) Heq.
  assert (Heq' : vx = vz * vy) by (rewrite Heq; ring).
  unfold step_zbnz, in_store3; cbn [sx3 sy3 sz3]. split; [exact Hx | split; [exact Hy | ]].
  destruct (sgndefb (sy3 s)) eqn:Ey.
  - apply mem3_inter; [exact Hz | eapply div_back3_sound; [exact Hx | exact Hy | exact Ey | exact Heq']].
  - destruct (xnzb (sx3 s)) eqn:Ex; [ | exact Hz].
    unfold xnzb in Ex.
    assert (Hx0 : vx <> 0) by (destruct (sgndefb_sign _ vx Ex Hx); lia).
    assert (Hvy : vy <> 0) by (intro Hc; apply Hx0; rewrite Heq, Hc; ring).
    apply mem3_inter; [exact Hz | eapply absb3_sound; [exact Hx | exact Heq' | exact Hvy]].
Qed.

Lemma zmul3_pipe_sound : Sound zmul3_pipe.
Proof.
  unfold zmul3_pipe.
  apply Sound_comp; [ | apply step_mul_sound ].
  apply Sound_comp; [ | apply step_zbnz_sound ].
  apply Sound_comp; [ | apply step_ybz_sound ].
  apply Sound_comp; [ | apply step_ybnz_sound ].
  apply Sound_comp; [ apply step_mul_sound | apply step_zbz_sound ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Monotonicity: corner lemmas, then each step, composed           *)
(* ------------------------------------------------------------------ *)

(* --- Finite arithmetic cores --- *)
Lemma zmul_min_lb : forall x c v d, c <= v -> v <= d -> Z.min (x*c) (x*d) <= x*v.
Proof.
  intros; destruct (Z.le_ge_cases 0 x);
  [ assert (x*c <= x*v) by nia | assert (x*d <= x*v) by nia ]; lia.
Qed.

Lemma zmul_max_ub : forall x c v d, c <= v -> v <= d -> x*v <= Z.max (x*c) (x*d).
Proof.
  intros; destruct (Z.le_ge_cases 0 x);
  [ assert (x*v <= x*d) by nia | assert (x*v <= x*c) by nia ]; lia.
Qed.

Ltac dfacts n m :=
  pose proof (Z.div_mod n m ltac:(lia));
  first [ pose proof (Z.mod_pos_bound n m ltac:(lia))
        | pose proof (Z.mod_neg_bound n m ltac:(lia)) ].

Lemma fdiv_num_max : forall a u b m, m <> 0 -> a <= u -> u <= b -> u / m <= Z.max (a / m) (b / m).
Proof.
  intros a u b m Hm Hau Hub.
  destruct (Z.lt_ge_cases m 0) as [HM|HM]; dfacts a m; dfacts u m; dfacts b m; nia.
Qed.

Lemma cdiv_num_min : forall a u b m, m <> 0 -> a <= u -> u <= b -> Z.min (cdiv a m) (cdiv b m) <= cdiv u m.
Proof.
  intros a u b m Hm Hau Hub. unfold cdiv.
  destruct (Z.lt_ge_cases m 0) as [HM|HM]; dfacts (-a) m; dfacts (-u) m; dfacts (-b) m; nia.
Qed.

Lemma fdiv_den_max_pos : forall n mc m md, 0 < mc -> mc <= m -> m <= md -> n / m <= Z.max (n / mc) (n / md).
Proof.
  intros. destruct (Z.le_ge_cases 0 n) as [Hn|Hn];
  [ assert (n/m <= n/mc) by (apply Z.div_le_compat_l; lia)
  | assert (n/m <= n/md) by (apply div_le_compat_l_neg; lia) ]; lia.
Qed.

Lemma fdiv_den_max_neg : forall n mc m md, md < 0 -> mc <= m -> m <= md -> n / m <= Z.max (n / mc) (n / md).
Proof.
  intros.
  pose proof (fdiv_den_max_pos (-n) (-md) (-m) (-mc) ltac:(lia) ltac:(lia) ltac:(lia)) as H2.
  rewrite (Z.div_opp_opp n md) in H2 by lia.
  rewrite (Z.div_opp_opp n m) in H2 by lia.
  rewrite (Z.div_opp_opp n mc) in H2 by lia. lia.
Qed.

Lemma cdiv_den_min_pos : forall n mc m md, 0 < mc -> mc <= m -> m <= md -> Z.min (cdiv n mc) (cdiv n md) <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_den_max_pos (-n) mc m md ltac:(lia) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma cdiv_den_min_neg : forall n mc m md, md < 0 -> mc <= m -> m <= md -> Z.min (cdiv n mc) (cdiv n md) <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_den_max_neg (-n) mc m md ltac:(lia) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fdiv_mono_pos : forall a b m, 0 < m -> a <= b -> a / m <= b / m.
Proof. intros; apply Z.div_le_mono; lia. Qed.

Lemma fdiv_anti_neg : forall a b m, m < 0 -> a <= b -> b / m <= a / m.
Proof. intros; apply div_le_mono_num_neg; lia. Qed.

Lemma cdiv_mono_pos : forall a b m, 0 < m -> a <= b -> cdiv a m <= cdiv b m.
Proof. intros. unfold cdiv. pose proof (fdiv_mono_pos (-b) (-a) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma cdiv_anti_neg : forall a b m, m < 0 -> a <= b -> cdiv b m <= cdiv a m.
Proof. intros. unfold cdiv. pose proof (fdiv_anti_neg (-b) (-a) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fdiv_neg_pos : forall n m, n < 0 -> 0 < m -> n / m <= -1.
Proof. intros. assert (n / m < 0) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

Lemma fdiv_pos_neg : forall n m, 0 < n -> m < 0 -> n / m <= -1.
Proof. intros. assert (n / m < 0) by (apply fdiv_lt_neg; lia). lia. Qed.

Lemma cdiv_pos_pos : forall n m, 0 < n -> 0 < m -> 1 <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_neg_pos (-n) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma cdiv_neg_neg : forall n m, n < 0 -> m < 0 -> 1 <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_pos_neg (-n) m ltac:(lia) ltac:(lia)). lia. Qed.

Lemma fdiv_den_pinf_pos : forall n mc m, 0 < mc -> mc <= m -> n / m <= Z.max (n / mc) (if n <? 0 then -1 else 0).
Proof.
  intros. destruct (Z.ltb_spec n 0) as [HN|HN].
  - pose proof (fdiv_neg_pos n m ltac:(lia) ltac:(lia)). lia.
  - assert (n/m <= n/mc) by (apply Z.div_le_compat_l; lia). lia.
Qed.

Lemma fdiv_den_ninf_neg : forall n m md, md < 0 -> m <= md -> n / m <= Z.max (if 0 <? n then -1 else 0) (n / md).
Proof.
  intros. destruct (Z.ltb_spec 0 n) as [HN|HN].
  - pose proof (fdiv_pos_neg n m ltac:(lia) ltac:(lia)). lia.
  - assert (n/m <= n/md).
    { rewrite <- (Z.div_opp_opp n m) by lia. rewrite <- (Z.div_opp_opp n md) by lia.
      apply Z.div_le_compat_l; lia. } lia.
Qed.

Lemma cdiv_den_pinf_pos : forall n mc m, 0 < mc -> mc <= m -> Z.min (cdiv n mc) (if 0 <? n then 1 else 0) <= cdiv n m.
Proof.
  intros. destruct (Z.ltb_spec 0 n) as [HN|HN].
  - pose proof (cdiv_pos_pos n m ltac:(lia) ltac:(lia)). lia.
  - unfold cdiv. assert ((-n)/m <= (-n)/mc) by (apply Z.div_le_compat_l; lia). lia.
Qed.

Lemma cdiv_den_ninf_neg : forall n m md, md < 0 -> m <= md -> Z.min (if n <? 0 then 1 else 0) (cdiv n md) <= cdiv n m.
Proof.
  intros. destruct (Z.ltb_spec n 0) as [HN|HN].
  - pose proof (cdiv_neg_neg n m ltac:(lia) ltac:(lia)). lia.
  - unfold cdiv. assert ((-n)/m <= (-n)/md).
    { rewrite <- (Z.div_opp_opp (-n) m) by lia. rewrite <- (Z.div_opp_opp (-n) md) by lia.
      rewrite Z.opp_involutive. apply Z.div_le_compat_l; lia. } lia.
Qed.

Lemma fdiv_abs_ub : forall n m, m <> 0 -> n / m <= Z.max (- n) n.
Proof.
  intros. destruct (Z.lt_ge_cases m 0) as [HM|HM]; destruct (Z.le_ge_cases 0 n) as [HN|HN].
  - assert (n/m <= 0) by (apply fdiv_ub_neg; lia). lia.
  - assert (n/m <= -n) by (apply fdiv_ub_neg; nia). lia.
  - assert (n/m <= n) by (apply Z.div_le_upper_bound; nia). lia.
  - assert (n/m <= 0) by (dfacts n m; nia). lia.
Qed.

Lemma cdiv_abs_lb : forall n m, m <> 0 -> Z.min n (- n) <= cdiv n m.
Proof. intros. unfold cdiv. pose proof (fdiv_abs_ub (-n) m H). lia. Qed.

(* --- Zinf order / sign utilities --- *)
Lemma ne_lo_le_hi : forall i, nonempty3b i = true -> zle (lo3 i) (hi3 i).
Proof. intros [[a| |] [b| |]]; cbn; try easy. intro H; apply Z.leb_le in H; lia. Qed.

Lemma ne_ile3 : forall i j, ile3 i j -> nonempty3b i = true -> nonempty3b j = true.
Proof.
  intros i j Hij Hne. apply (ile3_ne_inv i j Hne) in Hij as [Hl Hh].
  exact (raw_ile_ne i j Hne Hl Hh).
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

Lemma sgndefb_dn : forall i j, ile3 i j -> nonempty3b i = true -> sgndefb j = true -> sgndefb i = true.
Proof.
  intros i j Hij Hne Hs. apply (ile3_ne_inv i j Hne) in Hij as [Hl Hh].
  destruct i as [[a| |] [b| |]], j as [[c| |] [d| |]]; unfold sgndefb in *; cbn in *;
  try easy; bsolve.
Qed.

Lemma sgn_mem : forall i w, sgndefb i = true -> zle (lo3 i) w -> zle w (hi3 i) ->
  (zpos w || zneg w)%bool = true.
Proof.
  intros [[c| |] [d| |]] [w| |] Hs Hl Hh; unfold sgndefb in *; cbn in *; try easy; bsolve.
Qed.

(* the zero-shave preserves emptiness (0-bounds only widen the gap) *)
Lemma neqz3_empty : forall i, nonempty3b i = false -> nonempty3b (neqz3 i) = false.
Proof.
  intros [[a| |] [b| |]] H; unfold neqz3, nonempty3b in *; cbn in *;
    repeat (match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end);
    subst; cbn in *; try discriminate; try reflexivity;
    apply Z.leb_gt in H; apply Z.leb_gt; lia.
Qed.

Lemma neqz3_mono : forall i j, ile3 i j -> ile3 (neqz3 i) (neqz3 j).
Proof.
  intros i j Hij. destruct (nonempty3b i) eqn:Ei;
    [ | apply ile3_bot; apply neqz3_empty; exact Ei ].
  apply (ile3_ne_inv i j Ei) in Hij as [Hl Hh].
  destruct i as [li ui], j as [lj uj]; unfold neqz3; apply ile3_intro; cbn [lo3 hi3] in *.
  - destruct lj as [x| |], li as [y| |]; cbn in *; try easy;
    repeat match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end; cbn; try easy; lia.
  - destruct ui as [x| |], uj as [y| |]; cbn in *; try easy;
    repeat match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end; cbn; try easy; lia.
Qed.

Lemma zshave_mono : forall i j (b b' : bool), ile3 i j -> (b' = true -> b = true) ->
  ile3 (if b then neqz3 i else i) (if b' then neqz3 j else j).
Proof.
  intros i j b b' Hij Himp. destruct b' eqn:E.
  - rewrite (Himp eq_refl). apply neqz3_mono; assumption.
  - destruct b.
    + eapply ile3_trans; [apply neqz3_ile3|assumption].
    + assumption.
Qed.

Lemma zneg3_anti : forall a b, zle a b -> zle (zneg3 b) (zneg3 a).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

(* absb3 does NOT preserve emptiness, so monotonicity is guarded by ne on the source *)
Lemma absb3_mono : forall i j, nonempty3b i = true -> ile3 i j -> ile3 (absb3 i) (absb3 j).
Proof.
  intros i j Hne Hij. apply (ile3_ne_inv i j Hne) in Hij as [Hl Hh].
  apply ile3_intro; cbn [lo3 hi3].
  - apply zmin_mono; [assumption|apply zneg3_anti; assumption].
  - apply zmax_mono; [apply zneg3_anti; assumption|assumption].
Qed.

Lemma imul3_comm : forall a b, imul3 a b = imul3 b a.
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

Lemma imul3_min_lb : forall a c v d, zle c v -> zle v d ->
  zle (zmin (imul3 a c) (imul3 a d)) (imul3 a v).
Proof.
  intros [x| |] [cc| |] [vv| |] [dd| |] H1 H2; cbn in *; try easy; zif;
  try easy; try (apply zmul_min_lb; lia); try lia; try nia.
Qed.

Lemma imul3_max_ub : forall a c v d, zle c v -> zle v d ->
  zle (imul3 a v) (zmax (imul3 a c) (imul3 a d)).
Proof.
  intros [x| |] [cc| |] [vv| |] [dd| |] H1 H2; cbn in *; try easy; zif;
  try easy; try (apply zmul_max_ub; lia); try lia; try nia.
Qed.

Lemma mul_hull3_lb : forall i j u v,
  zle (lo3 i) u -> zle u (hi3 i) -> zle (lo3 j) v -> zle v (hi3 j) ->
  zle (zmin (zmin (imul3 (lo3 i) (lo3 j)) (imul3 (lo3 i) (hi3 j)))
            (zmin (imul3 (hi3 i) (lo3 j)) (imul3 (hi3 i) (hi3 j))))
      (imul3 u v).
Proof.
  intros i j u v Hu1 Hu2 Hv1 Hv2.
  apply zle_trans with (zmin (imul3 (lo3 i) v) (imul3 (hi3 i) v)).
  - apply zle_zmin_glb.
    + eapply zle_trans; [apply zmin_zle_l | apply imul3_min_lb; assumption].
    + eapply zle_trans; [apply zmin_zle_r | apply imul3_min_lb; assumption].
  - rewrite (imul3_comm (lo3 i) v), (imul3_comm (hi3 i) v), (imul3_comm u v).
    apply imul3_min_lb; assumption.
Qed.

Lemma mul_hull3_ub : forall i j u v,
  zle (lo3 i) u -> zle u (hi3 i) -> zle (lo3 j) v -> zle v (hi3 j) ->
  zle (imul3 u v)
      (zmax (zmax (imul3 (lo3 i) (lo3 j)) (imul3 (lo3 i) (hi3 j)))
            (zmax (imul3 (hi3 i) (lo3 j)) (imul3 (hi3 i) (hi3 j)))).
Proof.
  intros i j u v Hu1 Hu2 Hv1 Hv2.
  apply zle_trans with (zmax (imul3 (lo3 i) v) (imul3 (hi3 i) v)).
  - rewrite (imul3_comm (lo3 i) v), (imul3_comm (hi3 i) v), (imul3_comm u v).
    apply imul3_max_ub; assumption.
  - apply zmax_lub.
    + apply zle_trans with (zmax (imul3 (lo3 i) (lo3 j)) (imul3 (lo3 i) (hi3 j)));
        [ apply imul3_max_ub; assumption | apply zle_zmax_l ].
    + apply zle_trans with (zmax (imul3 (hi3 i) (lo3 j)) (imul3 (hi3 i) (hi3 j)));
        [ apply imul3_max_ub; assumption | apply zle_zmax_r ].
Qed.

Lemma mul_hull3_mono_ne : forall i i' j j',
  nonempty3b i = true -> nonempty3b j = true -> ile3 i i' -> ile3 j j' ->
  ile3 (mul_hull3 i j) (mul_hull3 i' j').
Proof.
  intros i i' j j' Hnei Hnej Hii' Hjj'.
  apply (ile3_ne_inv i i' Hnei) in Hii' as [Hli Hhi].
  apply (ile3_ne_inv j j' Hnej) in Hjj' as [Hlj Hhj].
  pose proof (ne_lo_le_hi _ Hnei) as Hilh. pose proof (ne_lo_le_hi _ Hnej) as Hjlh.
  assert (Ma2 : zle (lo3 i) (hi3 i')) by (eapply zle_trans; eassumption).
  assert (Mb1 : zle (lo3 i') (hi3 i)) by (eapply zle_trans; eassumption).
  assert (Mc2 : zle (lo3 j) (hi3 j')) by (eapply zle_trans; eassumption).
  assert (Md1 : zle (lo3 j') (hi3 j)) by (eapply zle_trans; eassumption).
  apply ile3_intro; unfold mul_hull3; cbn [lo3 hi3].
  - apply zle_zmin_glb; apply zle_zmin_glb; apply mul_hull3_lb; assumption.
  - apply zmax_lub; apply zmax_lub; apply mul_hull3_ub; assumption.
Qed.

(* --- Division corner lemmas --- *)
Lemma idivc3_num_lb : forall a u b w, (zpos w || zneg w)%bool = true ->
  zle a u -> zle u b -> zle (zmin (idivc3 a w) (idivc3 b w)) (idivc3 u w).
Proof.
  intros [av| |] [uv| |] [bv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (apply cdiv_num_min; lia); try (apply cdiv_mono_pos; lia); try (apply cdiv_anti_neg; lia).
Qed.

Lemma idivf3_num_ub : forall a u b w, (zpos w || zneg w)%bool = true ->
  zle a u -> zle u b -> zle (idivf3 u w) (zmax (idivf3 a w) (idivf3 b w)).
Proof.
  intros [av| |] [uv| |] [bv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (apply fdiv_num_max; lia); try (apply fdiv_mono_pos; lia); try (apply fdiv_anti_neg; lia).
Qed.

Lemma idivc3_den_lb : forall n c w d, (zpos c || zneg d)%bool = true ->
  zle c w -> zle w d -> zle (zmin (idivc3 n c) (idivc3 n d)) (idivc3 n w).
Proof.
  intros [nv| |] [cv| |] [wv| |] [dv| |] Hs H1 H2; cbn in *; try easy; bconv;
  try (apply cdiv_den_min_pos; lia); try (apply cdiv_den_min_neg; lia);
  try (apply cdiv_den_pinf_pos; lia); try (apply cdiv_den_ninf_neg; lia); zif; try easy; try lia.
Qed.

Lemma idivf3_den_ub : forall n c w d, (zpos c || zneg d)%bool = true ->
  zle c w -> zle w d -> zle (idivf3 n w) (zmax (idivf3 n c) (idivf3 n d)).
Proof.
  intros [nv| |] [cv| |] [wv| |] [dv| |] Hs H1 H2; cbn in *; try easy; bconv;
  try (apply fdiv_den_max_pos; lia); try (apply fdiv_den_max_neg; lia);
  try (apply fdiv_den_pinf_pos; lia); try (apply fdiv_den_ninf_neg; lia); zif; try easy; try lia.
Qed.

Lemma idivc3_abs_lb : forall xl xu u w, (zpos w || zneg w)%bool = true ->
  zle xl u -> zle u xu -> zle (zmin xl (zneg3 xu)) (idivc3 u w).
Proof.
  intros [lv| |] [rv| |] [uv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (match goal with |- context[cdiv ?v ?mm] => pose proof (cdiv_abs_lb v mm ltac:(lia)) end; lia).
Qed.

Lemma idivf3_abs_ub : forall xl xu u w, (zpos w || zneg w)%bool = true ->
  zle xl u -> zle u xu -> zle (idivf3 u w) (zmax (zneg3 xl) xu).
Proof.
  intros [lv| |] [rv| |] [uv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia; try (match goal with |- context[?v / ?mm] => pose proof (fdiv_abs_ub v mm ltac:(lia)) end; lia).
Qed.

(* --- div_back3 hull bounds and monotonicity --- *)
Lemma div_back3_lb : forall ix' ib' u w,
  (zpos (lo3 ib') || zneg (hi3 ib'))%bool = true ->
  zle (lo3 ix') u -> zle u (hi3 ix') -> zle (lo3 ib') w -> zle w (hi3 ib') ->
  zle (zmin (zmin (idivc3 (lo3 ix') (lo3 ib')) (idivc3 (lo3 ix') (hi3 ib')))
            (zmin (idivc3 (hi3 ix') (lo3 ib')) (idivc3 (hi3 ix') (hi3 ib'))))
      (idivc3 u w).
Proof.
  intros ix' ib' u w Hs Hu1 Hu2 Hw1 Hw2.
  apply zle_trans with (zmin (idivc3 (lo3 ix') w) (idivc3 (hi3 ix') w)).
  - apply zle_zmin_glb.
    + eapply zle_trans; [apply zmin_zle_l | apply idivc3_den_lb; assumption].
    + eapply zle_trans; [apply zmin_zle_r | apply idivc3_den_lb; assumption].
  - apply idivc3_num_lb; try assumption. exact (sgn_mem ib' w Hs Hw1 Hw2).
Qed.

Lemma div_back3_ub : forall ix' ib' u w,
  (zpos (lo3 ib') || zneg (hi3 ib'))%bool = true ->
  zle (lo3 ix') u -> zle u (hi3 ix') -> zle (lo3 ib') w -> zle w (hi3 ib') ->
  zle (idivf3 u w)
      (zmax (zmax (idivf3 (lo3 ix') (lo3 ib')) (idivf3 (lo3 ix') (hi3 ib')))
            (zmax (idivf3 (hi3 ix') (lo3 ib')) (idivf3 (hi3 ix') (hi3 ib')))).
Proof.
  intros ix' ib' u w Hs Hu1 Hu2 Hw1 Hw2.
  apply zle_trans with (zmax (idivf3 (lo3 ix') w) (idivf3 (hi3 ix') w)).
  - apply idivf3_num_ub; try assumption. exact (sgn_mem ib' w Hs Hw1 Hw2).
  - apply zmax_lub.
    + apply zle_trans with (zmax (idivf3 (lo3 ix') (lo3 ib')) (idivf3 (lo3 ix') (hi3 ib')));
        [ apply idivf3_den_ub; assumption | apply zle_zmax_l ].
    + apply zle_trans with (zmax (idivf3 (hi3 ix') (lo3 ib')) (idivf3 (hi3 ix') (hi3 ib')));
        [ apply idivf3_den_ub; assumption | apply zle_zmax_r ].
Qed.

Lemma div_back3_mono_ne : forall ix ix' ib ib',
  nonempty3b ix = true -> nonempty3b ib = true ->
  ile3 ix ix' -> ile3 ib ib' -> sgndefb ib' = true ->
  ile3 (div_back3 ix ib) (div_back3 ix' ib').
Proof.
  intros ix ix' ib ib' Hnex Hneb Hxx' Hbb' Hs.
  apply (ile3_ne_inv ix ix' Hnex) in Hxx' as [Hxl Hxh].
  apply (ile3_ne_inv ib ib' Hneb) in Hbb' as [Hbl Hbh].
  unfold sgndefb in Hs.
  pose proof (ne_lo_le_hi _ Hnex) as Hxlh. pose proof (ne_lo_le_hi _ Hneb) as Hblh.
  assert (Ma2 : zle (lo3 ix) (hi3 ix')) by (eapply zle_trans; eassumption).
  assert (Mb1 : zle (lo3 ix') (hi3 ix)) by (eapply zle_trans; eassumption).
  assert (Mc2 : zle (lo3 ib) (hi3 ib')) by (eapply zle_trans; eassumption).
  assert (Md1 : zle (lo3 ib') (hi3 ib)) by (eapply zle_trans; eassumption).
  apply ile3_intro; unfold div_back3; cbn [lo3 hi3].
  - apply zle_zmin_glb; apply zle_zmin_glb; apply div_back3_lb; assumption.
  - apply zmax_lub; apply zmax_lub; apply div_back3_ub; assumption.
Qed.

Lemma db_sub_absb : forall ix ix' ib,
  nonempty3b ix = true -> nonempty3b ib = true -> sgndefb ib = true ->
  ile3 ix ix' -> ile3 (div_back3 ix ib) (absb3 ix').
Proof.
  intros ix ix' ib Hnex Hneb Hs Hxx'.
  apply (ile3_ne_inv ix ix' Hnex) in Hxx' as [Hxl Hxh].
  pose proof (ne_lo_le_hi _ Hnex) as Hxlh. pose proof (ne_lo_le_hi _ Hneb) as Hblh.
  assert (Ma2 : zle (lo3 ix) (hi3 ix')) by (eapply zle_trans; eassumption).
  assert (Mb1 : zle (lo3 ix') (hi3 ix)) by (eapply zle_trans; eassumption).
  assert (W1 : (zpos (lo3 ib) || zneg (lo3 ib))%bool = true)
    by (apply (sgn_mem ib); [assumption | apply zle_refl | assumption]).
  assert (W2 : (zpos (hi3 ib) || zneg (hi3 ib))%bool = true)
    by (apply (sgn_mem ib); [assumption | assumption | apply zle_refl]).
  apply ile3_intro; unfold div_back3, absb3; cbn [lo3 hi3].
  - apply zle_zmin_glb; apply zle_zmin_glb; apply idivc3_abs_lb; assumption.
  - apply zmax_lub; apply zmax_lub; apply idivf3_abs_ub; assumption.
Qed.

(* --- the guarded back-propagation step is monotone (source non-empty) --- *)
Lemma zshave_ile3 : forall i (b : bool), ile3 (if b then neqz3 i else i) i.
Proof. intros i [|]; [apply neqz3_ile3 | apply ile3_refl]. Qed.

Lemma mulback_ile3 : forall iy ix ib,
  ile3 (if sgndefb ib then inter3 iy (div_back3 ix ib)
        else if xnzb ix then inter3 iy (absb3 ix) else iy) iy.
Proof.
  intros. destruct (sgndefb ib); [apply inter3_ile3_l|].
  destruct (xnzb ix); [apply inter3_ile3_l | apply ile3_refl].
Qed.

Lemma mulback_mono : forall iy iy' ix ix' ib ib',
  ile3 iy iy' -> ile3 ix ix' -> ile3 ib ib' ->
  nonempty3b ix = true -> nonempty3b ib = true ->
  ile3 (if sgndefb ib then inter3 iy (div_back3 ix ib)
        else if xnzb ix then inter3 iy (absb3 ix) else iy)
       (if sgndefb ib' then inter3 iy' (div_back3 ix' ib')
        else if xnzb ix' then inter3 iy' (absb3 ix') else iy').
Proof.
  intros iy iy' ix ix' ib ib' Hy Hx Hb Hnex Hneb.
  destruct (sgndefb ib') eqn:EB'.
  - rewrite (sgndefb_dn _ _ Hb Hneb EB').
    apply inter3_mono; [assumption | apply div_back3_mono_ne; assumption].
  - destruct (sgndefb ib) eqn:EB.
    + destruct (xnzb ix') eqn:EX'.
      * apply inter3_mono; [assumption | apply db_sub_absb; assumption].
      * eapply ile3_trans; [apply inter3_ile3_l | assumption].
    + destruct (xnzb ix') eqn:EX'.
      * assert (EX : xnzb ix = true) by (unfold xnzb in *; exact (sgndefb_dn _ _ Hx Hnex EX')).
        rewrite EX.
        apply inter3_mono; [assumption | apply absb3_mono; assumption].
      * destruct (xnzb ix) eqn:EX.
        -- eapply ile3_trans; [apply inter3_ile3_l | assumption].
        -- assumption.
Qed.

(* --- every step preserves emptiness (refines one component, keeps others) --- *)
Lemma empty_inter_l : forall i j, nonempty3b i = false -> nonempty3b (inter3 i j) = false.
Proof.
  intros i j H. destruct (nonempty3b (inter3 i j)) eqn:E; [ apply ne_inter3 in E; congruence | reflexivity ].
Qed.

Lemma step_mul_empty : forall s, ne_store3 s = false -> ne_store3 (step_mul s) = false.
Proof.
  intros s H. unfold ne_store3, step_mul in *; cbn [sx3 sy3 sz3] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; apply empty_inter_l; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right; exact H.
  - apply andb_false_iff; right; exact H.
Qed.

Lemma step_zbz_empty : forall s, ne_store3 s = false -> ne_store3 (step_zbz s) = false.
Proof.
  intros s H. unfold ne_store3, step_zbz in *; cbn [sx3 sy3 sz3] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right; exact H.
  - apply andb_false_iff; right.
    destruct (xnzb (sx3 s)); [ apply neqz3_empty; exact H | exact H ].
Qed.

Lemma step_ybnz_empty : forall s, ne_store3 s = false -> ne_store3 (step_ybnz s) = false.
Proof.
  intros s H. unfold ne_store3, step_ybnz in *; cbn [sx3 sy3 sz3] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right.
      destruct (sgndefb (sz3 s)); [ apply empty_inter_l; exact H | ].
      destruct (xnzb (sx3 s)); [ apply empty_inter_l; exact H | exact H ].
  - apply andb_false_iff; right; exact H.
Qed.

Lemma step_ybz_empty : forall s, ne_store3 s = false -> ne_store3 (step_ybz s) = false.
Proof.
  intros s H. unfold ne_store3, step_ybz in *; cbn [sx3 sy3 sz3] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right.
      destruct (xnzb (sx3 s)); [ apply neqz3_empty; exact H | exact H ].
  - apply andb_false_iff; right; exact H.
Qed.

Lemma step_zbnz_empty : forall s, ne_store3 s = false -> ne_store3 (step_zbnz s) = false.
Proof.
  intros s H. unfold ne_store3, step_zbnz in *; cbn [sx3 sy3 sz3] in *.
  apply andb_false_iff in H as [H | H].
  - apply andb_false_iff in H as [H | H].
    + apply andb_false_iff; left; apply andb_false_iff; left; exact H.
    + apply andb_false_iff; left; apply andb_false_iff; right; exact H.
  - apply andb_false_iff; right.
    destruct (sgndefb (sy3 s)); [ apply empty_inter_l; exact H | ].
    destruct (xnzb (sx3 s)); [ apply empty_inter_l; exact H | exact H ].
Qed.

(* --- monotonicity of each step (empty source -> bottom; else raw) --- *)

Lemma step_mul_monotone : Monotone step_mul.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (ne_store3 s) eqn:Es; [ | apply sle3_bot; apply step_mul_empty; exact Es ].
  apply (sle3_ne_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (ne_store3_parts s Es) as (Ex & Ey & Ez).
  unfold step_mul; apply sle3_intro; cbn [sx3 sy3 sz3].
  - apply inter3_mono; [ exact HX | apply mul_hull3_mono_ne; [exact Ey | exact Ez | exact HY | exact HZ] ].
  - exact HY.
  - exact HZ.
Qed.

Lemma step_zbz_monotone : Monotone step_zbz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (ne_store3 s) eqn:Es; [ | apply sle3_bot; apply step_zbz_empty; exact Es ].
  apply (sle3_ne_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (ne_store3_parts s Es) as (Ex & Ey & Ez).
  unfold step_zbz; apply sle3_intro; cbn [sx3 sy3 sz3].
  - exact HX.
  - exact HY.
  - apply zshave_mono; [ exact HZ | unfold xnzb; exact (sgndefb_dn (sx3 s) (sx3 t) HX Ex) ].
Qed.

Lemma step_ybnz_monotone : Monotone step_ybnz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (ne_store3 s) eqn:Es; [ | apply sle3_bot; apply step_ybnz_empty; exact Es ].
  apply (sle3_ne_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (ne_store3_parts s Es) as (Ex & Ey & Ez).
  unfold step_ybnz; apply sle3_intro; cbn [sx3 sy3 sz3].
  - exact HX.
  - apply mulback_mono; [ exact HY | exact HX | exact HZ | exact Ex | exact Ez ].
  - exact HZ.
Qed.

Lemma step_ybz_monotone : Monotone step_ybz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (ne_store3 s) eqn:Es; [ | apply sle3_bot; apply step_ybz_empty; exact Es ].
  apply (sle3_ne_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (ne_store3_parts s Es) as (Ex & Ey & Ez).
  unfold step_ybz; apply sle3_intro; cbn [sx3 sy3 sz3].
  - exact HX.
  - apply zshave_mono; [ exact HY | unfold xnzb; exact (sgndefb_dn (sx3 s) (sx3 t) HX Ex) ].
  - exact HZ.
Qed.

Lemma step_zbnz_monotone : Monotone step_zbnz.
Proof.
  unfold Monotone. intros s t Hst.
  destruct (ne_store3 s) eqn:Es; [ | apply sle3_bot; apply step_zbnz_empty; exact Es ].
  apply (sle3_ne_inv s t Es) in Hst as (HX & HY & HZ).
  destruct (ne_store3_parts s Es) as (Ex & Ey & Ez).
  unfold step_zbnz; apply sle3_intro; cbn [sx3 sy3 sz3].
  - exact HX.
  - exact HY.
  - apply mulback_mono; [ exact HZ | exact HX | exact HY | exact Ex | exact Ey ].
Qed.

Lemma zmul3_pipe_monotone : Monotone zmul3_pipe.
Proof.
  unfold zmul3_pipe.
  apply Monotone_comp; [ | apply step_mul_monotone ].
  apply Monotone_comp; [ | apply step_zbnz_monotone ].
  apply Monotone_comp; [ | apply step_ybz_monotone ].
  apply Monotone_comp; [ | apply step_ybnz_monotone ].
  apply Monotone_comp; [ apply step_mul_monotone | apply step_zbz_monotone ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem zmul3_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> vx = vy * vz ->
  in_store3 (zmul3 s) vx vy vz.
Proof. intros s vx vy vz Hin Heq. rewrite zmul3_is_pipe. exact (zmul3_pipe_sound s vx vy vz Hin Heq). Qed.

Theorem zmul3_reductive : forall s, sle3 (zmul3 s) s.
Proof. intro s. rewrite zmul3_is_pipe. apply zmul3_pipe_reductive. Qed.

(* UNCONDITIONAL under the quotient order: an empty output is bottom, and
   the composition of the per-step monotone maps handles the rest. *)
Theorem zmul3_monotone : forall s t, sle3 s t -> sle3 (zmul3 s) (zmul3 t).
Proof. intros s t Hst. rewrite !zmul3_is_pipe. apply zmul3_pipe_monotone; exact Hst. Qed.

Theorem zmul3_singleton_complete : forall s vx vy vz,
  sx3 s = Itv3 (Fin vx) (Fin vx) ->
  sy3 s = Itv3 (Fin vy) (Fin vy) ->
  sz3 s = Itv3 (Fin vz) (Fin vz) ->
  ne_store3 (zmul3 s) = true ->
  vx = vy * vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold zmul3 in Hne; cbv zeta in Hne.
  rewrite Hx, Hy, Hz in Hne.
  unfold ne_store3 in Hne.
  apply Bool.andb_true_iff in Hne as [Hne _].
  apply Bool.andb_true_iff in Hne as [Hnex _].
  (* the x-component is nested inter3s of the singleton hull *)
  apply ne_inter3 in Hnex.
  cbn in Hnex. apply Z.leb_le in Hnex. lia.
Qed.
