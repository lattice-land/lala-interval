(** * zmul3: the multiplication propagator with INFINITE bounds

    Rocq model of the C++ [zmul3] (zinterval.hpp): x = y * z over Zinf
    intervals.  Constant-time structure: 4-corner product hull, zero-shaving
    of the factors when 0 is not in x, division-back by the cdiv/fdiv corner
    hull when the co-factor is sign-definite (on solutions y = x / z exactly),
    and the absolute-value bound |factor| <= |x| when it straddles zero.

    The four defining propagator properties:
      - soundness              : [zmul3_soundness]
      - reductivity            : [zmul3_reductive]
      - monotonicity           : [zmul3_monotone]  (up to bottom)
      - completeness/singleton : [zmul3_singleton_complete] *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv3 zadd3.
From LalaInterval Require fdiv2.
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

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem zmul3_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> vx = vy * vz ->
  in_store3 (zmul3 s) vx vy vz.
Proof. Admitted.

(* the zero-shave only moves bounds inward *)
Lemma neqz3_ile3 : forall i, ile3 (neqz3 i) i.
Proof.
  intros [l u]; split; cbn [lo3 hi3].
  - destruct l as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
  - destruct u as [v| |]; cbn; try easy.
    destruct (v =? 0) eqn:E; cbn; [apply Z.eqb_eq in E|]; lia.
Qed.

Theorem zmul3_reductive : forall s, sle3 (zmul3 s) s.
Proof.
  intro s. unfold zmul3; cbv zeta. unfold sle3; cbn [sx3 sy3 sz3].
  repeat (match goal with |- context[if ?b then _ else _] => destruct b end).
  all: split; [|split].
  all: repeat (first [ apply ile3_refl
                | apply neqz3_ile3
                | apply inter3_ile3_l
                | eapply ile3_trans; [apply neqz3_ile3|]
                | eapply ile3_trans; [apply inter3_ile3_l|] ]).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Helper lemmas for monotonicity                                   *)
(* ------------------------------------------------------------------ *)

(* --- Finite arithmetic cores ---------------------------------------- *)

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

Lemma fdiv_num_max : forall a u b m, m <> 0 -> a <= u -> u <= b ->
  u / m <= Z.max (a / m) (b / m).
Proof.
  intros a u b m Hm Hau Hub.
  destruct (Z.lt_ge_cases m 0) as [HM|HM];
  dfacts a m; dfacts u m; dfacts b m; nia.
Qed.

Lemma cdiv_num_min : forall a u b m, m <> 0 -> a <= u -> u <= b ->
  Z.min (fdiv2.cdiv a m) (fdiv2.cdiv b m) <= fdiv2.cdiv u m.
Proof.
  intros a u b m Hm Hau Hub. unfold fdiv2.cdiv.
  destruct (Z.lt_ge_cases m 0) as [HM|HM];
  dfacts (-a) m; dfacts (-u) m; dfacts (-b) m; nia.
Qed.

Lemma fdiv_den_max_pos : forall n mc m md, 0 < mc -> mc <= m -> m <= md ->
  n / m <= Z.max (n / mc) (n / md).
Proof.
  intros. destruct (Z.le_ge_cases 0 n) as [Hn|Hn];
  [ assert (n/m <= n/mc) by (apply Z.div_le_compat_l; lia)
  | assert (n/m <= n/md) by (apply fdiv2.div_le_compat_l_neg; lia) ]; lia.
Qed.

Lemma fdiv_den_max_neg : forall n mc m md, md < 0 -> mc <= m -> m <= md ->
  n / m <= Z.max (n / mc) (n / md).
Proof.
  intros.
  pose proof (fdiv_den_max_pos (-n) (-md) (-m) (-mc) ltac:(lia) ltac:(lia) ltac:(lia)) as H2.
  rewrite (Z.div_opp_opp n md) in H2 by lia.
  rewrite (Z.div_opp_opp n m) in H2 by lia.
  rewrite (Z.div_opp_opp n mc) in H2 by lia.
  lia.
Qed.

Lemma cdiv_den_min_pos : forall n mc m md, 0 < mc -> mc <= m -> m <= md ->
  Z.min (fdiv2.cdiv n mc) (fdiv2.cdiv n md) <= fdiv2.cdiv n m.
Proof.
  intros. unfold fdiv2.cdiv.
  pose proof (fdiv_den_max_pos (-n) mc m md ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma cdiv_den_min_neg : forall n mc m md, md < 0 -> mc <= m -> m <= md ->
  Z.min (fdiv2.cdiv n mc) (fdiv2.cdiv n md) <= fdiv2.cdiv n m.
Proof.
  intros. unfold fdiv2.cdiv.
  pose proof (fdiv_den_max_neg (-n) mc m md ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fdiv_mono_pos : forall a b m, 0 < m -> a <= b -> a / m <= b / m.
Proof. intros; apply Z.div_le_mono; lia. Qed.

Lemma fdiv_anti_neg : forall a b m, m < 0 -> a <= b -> b / m <= a / m.
Proof. intros; apply fdiv2.div_le_mono_num_neg; lia. Qed.

Lemma cdiv_mono_pos : forall a b m, 0 < m -> a <= b -> fdiv2.cdiv a m <= fdiv2.cdiv b m.
Proof.
  intros. unfold fdiv2.cdiv.
  pose proof (fdiv_mono_pos (-b) (-a) m ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma cdiv_anti_neg : forall a b m, m < 0 -> a <= b -> fdiv2.cdiv b m <= fdiv2.cdiv a m.
Proof.
  intros. unfold fdiv2.cdiv.
  pose proof (fdiv_anti_neg (-b) (-a) m ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fdiv_neg_pos : forall n m, n < 0 -> 0 < m -> n / m <= -1.
Proof. intros. assert (n / m < 0) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

Lemma fdiv_pos_neg : forall n m, 0 < n -> m < 0 -> n / m <= -1.
Proof. intros. assert (n / m < 0) by (apply fdiv2.fdiv_lt_neg; lia). lia. Qed.

Lemma cdiv_pos_pos : forall n m, 0 < n -> 0 < m -> 1 <= fdiv2.cdiv n m.
Proof.
  intros. unfold fdiv2.cdiv.
  pose proof (fdiv_neg_pos (-n) m ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma cdiv_neg_neg : forall n m, n < 0 -> m < 0 -> 1 <= fdiv2.cdiv n m.
Proof.
  intros. unfold fdiv2.cdiv.
  pose proof (fdiv_pos_neg (-n) m ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fdiv_den_pinf_pos : forall n mc m, 0 < mc -> mc <= m ->
  n / m <= Z.max (n / mc) (if n <? 0 then -1 else 0).
Proof.
  intros. destruct (Z.ltb_spec n 0) as [HN|HN].
  - pose proof (fdiv_neg_pos n m ltac:(lia) ltac:(lia)). lia.
  - assert (n/m <= n/mc) by (apply Z.div_le_compat_l; lia). lia.
Qed.

Lemma fdiv_den_ninf_neg : forall n m md, md < 0 -> m <= md ->
  n / m <= Z.max (if 0 <? n then -1 else 0) (n / md).
Proof.
  intros. destruct (Z.ltb_spec 0 n) as [HN|HN].
  - pose proof (fdiv_pos_neg n m ltac:(lia) ltac:(lia)). lia.
  - assert (n/m <= n/md).
    { rewrite <- (Z.div_opp_opp n m) by lia. rewrite <- (Z.div_opp_opp n md) by lia.
      apply Z.div_le_compat_l; lia. }
    lia.
Qed.

Lemma cdiv_den_pinf_pos : forall n mc m, 0 < mc -> mc <= m ->
  Z.min (fdiv2.cdiv n mc) (if 0 <? n then 1 else 0) <= fdiv2.cdiv n m.
Proof.
  intros. destruct (Z.ltb_spec 0 n) as [HN|HN].
  - pose proof (cdiv_pos_pos n m ltac:(lia) ltac:(lia)). lia.
  - unfold fdiv2.cdiv.
    assert ((-n)/m <= (-n)/mc) by (apply Z.div_le_compat_l; lia). lia.
Qed.

Lemma cdiv_den_ninf_neg : forall n m md, md < 0 -> m <= md ->
  Z.min (if n <? 0 then 1 else 0) (fdiv2.cdiv n md) <= fdiv2.cdiv n m.
Proof.
  intros. destruct (Z.ltb_spec n 0) as [HN|HN].
  - pose proof (cdiv_neg_neg n m ltac:(lia) ltac:(lia)). lia.
  - unfold fdiv2.cdiv.
    assert ((-n)/m <= (-n)/md).
    { rewrite <- (Z.div_opp_opp (-n) m) by lia. rewrite <- (Z.div_opp_opp (-n) md) by lia.
      rewrite Z.opp_involutive. apply Z.div_le_compat_l; lia. }
    lia.
Qed.

Lemma fdiv_abs_ub : forall n m, m <> 0 -> n / m <= Z.max (- n) n.
Proof.
  intros. destruct (Z.lt_ge_cases m 0) as [HM|HM]; destruct (Z.le_ge_cases 0 n) as [HN|HN].
  - assert (n/m <= 0) by (apply fdiv2.fdiv_ub_neg; lia). lia.
  - assert (n/m <= -n) by (apply fdiv2.fdiv_ub_neg; nia). lia.
  - assert (n/m <= n) by (apply Z.div_le_upper_bound; nia). lia.
  - assert (n/m <= 0) by (dfacts n m; nia). lia.
Qed.

Lemma cdiv_abs_lb : forall n m, m <> 0 -> Z.min n (- n) <= fdiv2.cdiv n m.
Proof.
  intros. unfold fdiv2.cdiv. pose proof (fdiv_abs_ub (-n) m H). lia.
Qed.

(* --- Zinf order utilities ------------------------------------------- *)

Lemma zmin_zle_r : forall a b, zle (zmin a b) b.
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma zle_zmax_r : forall a b, zle b (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma ne_lo_le_hi : forall i, nonempty3b i = true -> zle (lo3 i) (hi3 i).
Proof.
  intros [[a| |] [b| |]]; cbn; try easy. intro H; apply Z.leb_le in H; lia.
Qed.

Lemma ne_ile3 : forall i j, ile3 i j -> nonempty3b i = true -> nonempty3b j = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]] [Hl Hh]; cbn in *; try easy;
  intro H; apply Z.leb_le in H; apply Z.leb_le; lia.
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
  intros [[a| |] [b| |]] [[c| |] [d| |]] [Hl Hh] Hne Hs; unfold sgndefb in *; cbn in *;
  try easy; bsolve.
Qed.

Lemma sgn_mem : forall i w, sgndefb i = true -> zle (lo3 i) w -> zle w (hi3 i) ->
  (zpos w || zneg w)%bool = true.
Proof.
  intros [[c| |] [d| |]] [w| |] Hs Hl Hh; unfold sgndefb in *; cbn in *; try easy; bsolve.
Qed.

Lemma neqz3_mono : forall i j, ile3 i j -> ile3 (neqz3 i) (neqz3 j).
Proof.
  intros [li ui] [lj uj] [Hl Hh]; unfold neqz3; split; cbn [lo3 hi3] in *.
  - destruct lj as [x| |], li as [y| |]; cbn in *; try easy;
    repeat match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end;
    cbn; try easy; lia.
  - destruct ui as [x| |], uj as [y| |]; cbn in *; try easy;
    repeat match goal with |- context[?v =? 0] => destruct (Z.eqb_spec v 0) end;
    cbn; try easy; lia.
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

Lemma absb3_mono : forall i j, ile3 i j -> ile3 (absb3 i) (absb3 j).
Proof.
  intros i j [Hl Hh]; split; cbn [lo3 hi3].
  - apply zmin_mono; [assumption|apply zneg3_anti; assumption].
  - apply zmax_mono; [apply zneg3_anti; assumption|assumption].
Qed.

Lemma imul3_comm : forall a b, imul3 a b = imul3 b a.
Proof. intros [x| |] [y| |]; cbn; try reflexivity. f_equal; ring. Qed.

(* --- Corner lemmas: a member of a box is dominated by the corner hull  *)

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
    + eapply zle_trans; [apply imul3_max_ub; assumption | apply zle_zmax_l].
    + eapply zle_trans; [apply imul3_max_ub; assumption | apply zle_zmax_r].
Qed.

Lemma mul_hull3_mono_ne : forall i i' j j',
  nonempty3b i = true -> nonempty3b j = true -> ile3 i i' -> ile3 j j' ->
  ile3 (mul_hull3 i j) (mul_hull3 i' j').
Proof.
  intros i i' j j' Hnei Hnej [Hli Hhi] [Hlj Hhj].
  pose proof (ne_lo_le_hi _ Hnei) as Hilh.
  pose proof (ne_lo_le_hi _ Hnej) as Hjlh.
  assert (Ma2 : zle (lo3 i) (hi3 i')) by (eapply zle_trans; eassumption).
  assert (Mb1 : zle (lo3 i') (hi3 i)) by (eapply zle_trans; eassumption).
  assert (Mc2 : zle (lo3 j) (hi3 j')) by (eapply zle_trans; eassumption).
  assert (Md1 : zle (lo3 j') (hi3 j)) by (eapply zle_trans; eassumption).
  split; unfold mul_hull3; cbn [lo3 hi3].
  - apply zle_zmin_glb; apply zle_zmin_glb; apply mul_hull3_lb; assumption.
  - apply zmax_lub; apply zmax_lub; apply mul_hull3_ub; assumption.
Qed.

(* --- Division corner lemmas ----------------------------------------- *)

Lemma idivc3_num_lb : forall a u b w, (zpos w || zneg w)%bool = true ->
  zle a u -> zle u b -> zle (zmin (idivc3 a w) (idivc3 b w)) (idivc3 u w).
Proof.
  intros [av| |] [uv| |] [bv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia;
  try (apply cdiv_num_min; lia);
  try (apply cdiv_mono_pos; lia);
  try (apply cdiv_anti_neg; lia).
Qed.

Lemma idivf3_num_ub : forall a u b w, (zpos w || zneg w)%bool = true ->
  zle a u -> zle u b -> zle (idivf3 u w) (zmax (idivf3 a w) (idivf3 b w)).
Proof.
  intros [av| |] [uv| |] [bv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia;
  try (apply fdiv_num_max; lia);
  try (apply fdiv_mono_pos; lia);
  try (apply fdiv_anti_neg; lia).
Qed.

Lemma idivc3_den_lb : forall n c w d, (zpos c || zneg d)%bool = true ->
  zle c w -> zle w d -> zle (zmin (idivc3 n c) (idivc3 n d)) (idivc3 n w).
Proof.
  intros [nv| |] [cv| |] [wv| |] [dv| |] Hs H1 H2; cbn in *; try easy; bconv;
  try (apply cdiv_den_min_pos; lia);
  try (apply cdiv_den_min_neg; lia);
  try (apply cdiv_den_pinf_pos; lia);
  try (apply cdiv_den_ninf_neg; lia);
  zif; try easy; try lia.
Qed.

Lemma idivf3_den_ub : forall n c w d, (zpos c || zneg d)%bool = true ->
  zle c w -> zle w d -> zle (idivf3 n w) (zmax (idivf3 n c) (idivf3 n d)).
Proof.
  intros [nv| |] [cv| |] [wv| |] [dv| |] Hs H1 H2; cbn in *; try easy; bconv;
  try (apply fdiv_den_max_pos; lia);
  try (apply fdiv_den_max_neg; lia);
  try (apply fdiv_den_pinf_pos; lia);
  try (apply fdiv_den_ninf_neg; lia);
  zif; try easy; try lia.
Qed.

Lemma idivc3_abs_lb : forall xl xu u w, (zpos w || zneg w)%bool = true ->
  zle xl u -> zle u xu -> zle (zmin xl (zneg3 xu)) (idivc3 u w).
Proof.
  intros [lv| |] [rv| |] [uv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia;
  try (match goal with |- context[fdiv2.cdiv ?v ?mm] =>
         pose proof (cdiv_abs_lb v mm ltac:(lia)) end; lia).
Qed.

Lemma idivf3_abs_ub : forall xl xu u w, (zpos w || zneg w)%bool = true ->
  zle xl u -> zle u xu -> zle (idivf3 u w) (zmax (zneg3 xl) xu).
Proof.
  intros [lv| |] [rv| |] [uv| |] [m| |] Hw H1 H2; cbn in *; try easy; bconv; zif;
  try easy; try lia;
  try (match goal with |- context[?v / ?mm] =>
         pose proof (fdiv_abs_ub v mm ltac:(lia)) end; lia).
Qed.

(* --- div_back3 hull bounds and monotonicity ------------------------- *)

Lemma div_back3_lb : forall ix' ib' u w,
  (zpos (lo3 ib') || zneg (hi3 ib'))%bool = true ->
  zle (lo3 ix') u -> zle u (hi3 ix') ->
  zle (lo3 ib') w -> zle w (hi3 ib') ->
  zle (zmin (zmin (idivc3 (lo3 ix') (lo3 ib')) (idivc3 (lo3 ix') (hi3 ib')))
            (zmin (idivc3 (hi3 ix') (lo3 ib')) (idivc3 (hi3 ix') (hi3 ib'))))
      (idivc3 u w).
Proof.
  intros ix' ib' u w Hs Hu1 Hu2 Hw1 Hw2.
  apply zle_trans with (zmin (idivc3 (lo3 ix') w) (idivc3 (hi3 ix') w)).
  - apply zle_zmin_glb.
    + eapply zle_trans; [apply zmin_zle_l | apply idivc3_den_lb; assumption].
    + eapply zle_trans; [apply zmin_zle_r | apply idivc3_den_lb; assumption].
  - apply idivc3_num_lb; try assumption.
    exact (sgn_mem ib' w Hs Hw1 Hw2).
Qed.

Lemma div_back3_ub : forall ix' ib' u w,
  (zpos (lo3 ib') || zneg (hi3 ib'))%bool = true ->
  zle (lo3 ix') u -> zle u (hi3 ix') ->
  zle (lo3 ib') w -> zle w (hi3 ib') ->
  zle (idivf3 u w)
      (zmax (zmax (idivf3 (lo3 ix') (lo3 ib')) (idivf3 (lo3 ix') (hi3 ib')))
            (zmax (idivf3 (hi3 ix') (lo3 ib')) (idivf3 (hi3 ix') (hi3 ib')))).
Proof.
  intros ix' ib' u w Hs Hu1 Hu2 Hw1 Hw2.
  apply zle_trans with (zmax (idivf3 (lo3 ix') w) (idivf3 (hi3 ix') w)).
  - apply idivf3_num_ub; try assumption.
    exact (sgn_mem ib' w Hs Hw1 Hw2).
  - apply zmax_lub.
    + eapply zle_trans; [apply idivf3_den_ub; assumption | apply zle_zmax_l].
    + eapply zle_trans; [apply idivf3_den_ub; assumption | apply zle_zmax_r].
Qed.

Lemma div_back3_mono_ne : forall ix ix' ib ib',
  nonempty3b ix = true -> nonempty3b ib = true ->
  ile3 ix ix' -> ile3 ib ib' -> sgndefb ib' = true ->
  ile3 (div_back3 ix ib) (div_back3 ix' ib').
Proof.
  intros ix ix' ib ib' Hnex Hneb [Hxl Hxh] [Hbl Hbh] Hs.
  unfold sgndefb in Hs.
  pose proof (ne_lo_le_hi _ Hnex) as Hxlh.
  pose proof (ne_lo_le_hi _ Hneb) as Hblh.
  assert (Ma2 : zle (lo3 ix) (hi3 ix')) by (eapply zle_trans; eassumption).
  assert (Mb1 : zle (lo3 ix') (hi3 ix)) by (eapply zle_trans; eassumption).
  assert (Mc2 : zle (lo3 ib) (hi3 ib')) by (eapply zle_trans; eassumption).
  assert (Md1 : zle (lo3 ib') (hi3 ib)) by (eapply zle_trans; eassumption).
  split; unfold div_back3; cbn [lo3 hi3].
  - apply zle_zmin_glb; apply zle_zmin_glb; apply div_back3_lb; assumption.
  - apply zmax_lub; apply zmax_lub; apply div_back3_ub; assumption.
Qed.

Lemma db_sub_absb : forall ix ix' ib,
  nonempty3b ix = true -> nonempty3b ib = true -> sgndefb ib = true ->
  ile3 ix ix' -> ile3 (div_back3 ix ib) (absb3 ix').
Proof.
  intros ix ix' ib Hnex Hneb Hs [Hxl Hxh].
  pose proof (ne_lo_le_hi _ Hnex) as Hxlh.
  pose proof (ne_lo_le_hi _ Hneb) as Hblh.
  assert (Ma2 : zle (lo3 ix) (hi3 ix')) by (eapply zle_trans; eassumption).
  assert (Mb1 : zle (lo3 ix') (hi3 ix)) by (eapply zle_trans; eassumption).
  assert (W1 : (zpos (lo3 ib) || zneg (lo3 ib))%bool = true)
    by (apply (sgn_mem ib); [assumption | apply zle_refl | assumption]).
  assert (W2 : (zpos (hi3 ib) || zneg (hi3 ib))%bool = true)
    by (apply (sgn_mem ib); [assumption | assumption | apply zle_refl]).
  split; unfold div_back3, absb3; cbn [lo3 hi3].
  - apply zle_zmin_glb; apply zle_zmin_glb; apply idivc3_abs_lb; assumption.
  - apply zmax_lub; apply zmax_lub; apply idivf3_abs_ub; assumption.
Qed.

(* --- The guarded back-propagation step, monotone under s-side ne ----- *)

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

Theorem zmul3_monotone : forall s t,
  sle3 s t ->
  ne_store3 (zmul3 s) = true ->
  sle3 (zmul3 s) (zmul3 t).
Proof.
  intros s t (HX & HY & HZ) Hne.
  unfold zmul3 in *; cbv zeta in *.
  unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne.
  apply andb_true_iff in Hne; destruct Hne as [Hne Hnez1].
  apply andb_true_iff in Hne; destruct Hne as [Hnex2 Hney1].
  unfold sle3; cbn [sx3 sy3 sz3].
  set (xs := inter3 (sx3 s) (mul_hull3 (sy3 s) (sz3 s))) in *.
  set (xt := inter3 (sx3 t) (mul_hull3 (sy3 t) (sz3 t))) in *.
  set (z0s := if xnzb xs then neqz3 (sz3 s) else sz3 s) in *.
  set (z0t := if xnzb xt then neqz3 (sz3 t) else sz3 t) in *.
  set (y0s := if sgndefb z0s then inter3 (sy3 s) (div_back3 xs z0s)
              else if xnzb xs then inter3 (sy3 s) (absb3 xs) else sy3 s) in *.
  set (y0t := if sgndefb z0t then inter3 (sy3 t) (div_back3 xt z0t)
              else if xnzb xt then inter3 (sy3 t) (absb3 xt) else sy3 t) in *.
  set (y1s := if xnzb xs then neqz3 y0s else y0s) in *.
  set (y1t := if xnzb xt then neqz3 y0t else y0t) in *.
  set (z1s := if sgndefb y1s then inter3 z0s (div_back3 xs y1s)
              else if xnzb xs then inter3 z0s (absb3 xs) else z0s) in *.
  set (z1t := if sgndefb y1t then inter3 z0t (div_back3 xt y1t)
              else if xnzb xt then inter3 z0t (absb3 xt) else z0t) in *.
  (* non-emptiness of the s-side pipeline stages *)
  pose proof (ne_inter3 _ _ Hnex2) as Hnexs.
  assert (Hy1y0 : ile3 y1s y0s) by (unfold y1s; apply zshave_ile3).
  pose proof (ne_ile3 _ _ Hy1y0 Hney1) as Hney0.
  assert (Hy0sy : ile3 y0s (sy3 s)) by (unfold y0s; apply mulback_ile3).
  pose proof (ne_ile3 _ _ Hy0sy Hney0) as Hnesy.
  assert (Hz1z0 : ile3 z1s z0s) by (unfold z1s; apply mulback_ile3).
  pose proof (ne_ile3 _ _ Hz1z0 Hnez1) as Hnez0.
  assert (Hz0sz : ile3 z0s (sz3 s)) by (unfold z0s; apply zshave_ile3).
  pose proof (ne_ile3 _ _ Hz0sz Hnez0) as Hnesz.
  (* the pipeline is monotone stage by stage *)
  assert (Hxx : ile3 xs xt)
    by (unfold xs, xt; apply inter3_mono;
        [assumption | apply mul_hull3_mono_ne; assumption]).
  assert (Himp : xnzb xt = true -> xnzb xs = true)
    by (intro E; unfold xnzb in *; exact (sgndefb_dn _ _ Hxx Hnexs E)).
  assert (Hz0 : ile3 z0s z0t)
    by (unfold z0s, z0t; apply zshave_mono; assumption).
  assert (Hy0 : ile3 y0s y0t)
    by (unfold y0s, y0t; apply mulback_mono; assumption).
  assert (Hy1 : ile3 y1s y1t)
    by (unfold y1s, y1t; apply zshave_mono; assumption).
  assert (Hz1 : ile3 z1s z1t)
    by (unfold z1s, z1t; apply mulback_mono; assumption).
  split; [|split].
  - apply inter3_mono; [assumption | apply mul_hull3_mono_ne; assumption].
  - exact Hy1.
  - exact Hz1.
Qed.

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
