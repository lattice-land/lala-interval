(** * zadd3: the addition propagator with INFINITE bounds

    Rocq model of the C++ [zadd3] (zinterval.hpp): x = y + z over Zinf
    intervals, refining x by the sum hull, then y and z by difference hulls
    (each using the already-refined companions), with no finiteness guard.

    The full propagator property suite is proved (mirroring div4.v):
      - soundness              : [zadd3_soundness]
      - best transformer       : [zadd3_complete]    (completeness)
      - ne-feasibility         : [zadd3_ne_feasible]
      - reductivity            : [zadd3_reductive]    (unconditional)
      - monotonicity           : [zadd3_monotone]     (unconditional)
      - idempotence            : [zadd3_idempotent]   (unconditional, up to ~)
      - completeness/singleton : [zadd3_singleton_complete]

    Order is the QUOTIENTED lattice one (itv.ile3/sle3): empties = bottom. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Infinity-aware addition/subtraction (mirrors the C++ iadd/isub) *)
(* ------------------------------------------------------------------ *)

Definition iadd3 (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x + y)
  | Pinf, _ => Pinf
  | Ninf, _ => Ninf
  | _, Pinf => Pinf
  | _, Ninf => Ninf
  end.

Definition isub3 (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x - y)
  | Pinf, _ => Pinf
  | Ninf, _ => Ninf
  | _, Pinf => Ninf
  | _, Ninf => Pinf
  end.

(* ------------------------------------------------------------------ *)
(** ** The propagator (mirrors zadd3)                                  *)
(* ------------------------------------------------------------------ *)

Definition zadd3 (s : store3) : store3 :=
  let x := inter3 (sx3 s) (Itv3 (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))
                                (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s)))) in
  let y := inter3 (sy3 s) (Itv3 (isub3 (lo3 x) (hi3 (sz3 s)))
                                (isub3 (hi3 x) (lo3 (sz3 s)))) in
  let z := inter3 (sz3 s) (Itv3 (isub3 (lo3 x) (hi3 y))
                                (isub3 (hi3 x) (lo3 y))) in
  St3 x y z.

(* ------------------------------------------------------------------ *)
(** ** Order and arithmetic lemmas                                     *)
(* ------------------------------------------------------------------ *)

Lemma iadd3_ub : forall a b u v,
  zle a (Fin u) -> zle b (Fin v) -> zle (iadd3 a b) (Fin (u + v)).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma iadd3_lb : forall a b u v,
  zle (Fin u) a -> zle (Fin v) b -> zle (Fin (u + v)) (iadd3 a b).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma isub3_ub : forall a b u v,
  zle a (Fin u) -> zle (Fin v) b -> zle (isub3 a b) (Fin (u - v)).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma isub3_lb : forall a b u v,
  zle (Fin u) a -> zle b (Fin v) -> zle (Fin (u - v)) (isub3 a b).
Proof. intros [x| |] [y| |] u v Ha Hb; cbn in *; try easy; lia. Qed.

Lemma zle_refl3 : forall a, zle a a.
Proof. intros [x| |]; cbn; try easy; lia. Qed.

Lemma zle_zmax_l : forall a b, zle a (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma zle_zmin_l : forall a b, zle (zmin a b) a.
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

(* [inter3_ile3_l] is now provided by itv3 (quotient order). *)

Lemma mem3_inter : forall i j v, mem3 i v -> mem3 j v -> mem3 (inter3 i j) v.
Proof.
  intros [li ui] [lj uj] v [H1 H2] [H3 H4]; cbn in *; split; cbn.
  - destruct li as [x| |], lj as [y| |]; cbn in *; try easy; lia.
  - destruct ui as [x| |], uj as [y| |]; cbn in *; try easy; lia.
Qed.

Lemma zmax_mono : forall a b c d, zle a b -> zle c d -> zle (zmax a c) (zmax b d).
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma zmin_mono : forall a b c d, zle a b -> zle c d -> zle (zmin a c) (zmin b d).
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma ne_inter3_r : forall i j, nonempty3b (inter3 i j) = true -> nonempty3b j = true.
Proof.
  intros [[a| |] [b| |]] [[c| |] [d| |]]; cbn; intros H; try reflexivity; try discriminate;
    apply Z.leb_le; apply Z.leb_le in H; lia.
Qed.

(* Meet is monotone in BOTH arguments, unconditionally under the quotient
   order: if the meet is empty it is bottom, otherwise both inputs are
   non-empty and the raw bounds move monotonically. *)
Lemma inter3_mono : forall i i' j j',
  ile3 i i' -> ile3 j j' -> ile3 (inter3 i j) (inter3 i' j').
Proof.
  intros i i' j j' Hii Hjj.
  destruct (nonempty3b (inter3 i j)) eqn:E; [ | apply ile3_bot; exact E ].
  pose proof (ne_inter3 _ _ E) as Ei. pose proof (ne_inter3_r _ _ E) as Ej.
  apply (ile3_ne_inv i i' Ei) in Hii as [Hli Hhi].
  apply (ile3_ne_inv j j' Ej) in Hjj as [Hlj Hhj].
  apply ile3_intro; unfold inter3; cbn [lo3 hi3].
  - apply zmax_mono; assumption.
  - apply zmin_mono; assumption.
Qed.

Lemma iadd3_mono : forall a a' b b',
  zle a a' -> zle b b' -> zle (iadd3 a b) (iadd3 a' b').
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

Lemma isub3_mono : forall a a' b b',
  zle a a' -> zle b' b -> zle (isub3 a b) (isub3 a' b').
Proof. intros [x| |] [y| |] [z| |] [w| |] H1 H2; cbn in *; try easy; lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem zadd3_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> vx = vy + vz ->
  in_store3 (zadd3 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Heq.
  destruct Hx as [Hx1 Hx2], Hy as [Hy1 Hy2], Hz as [Hz1 Hz2].
  unfold zadd3; cbv zeta.
  (* refined x contains vx *)
  assert (HXr : mem3 (inter3 (sx3 s) (Itv3 (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))
                                           (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s))))) vx).
  { apply mem3_inter; [split; assumption|]. split; cbn [lo3 hi3].
    - replace vx with (vy + vz) by lia. apply iadd3_ub; assumption.
    - replace vx with (vy + vz) by lia. apply iadd3_lb; assumption. }
  destruct HXr as [HX1 HX2].
  (* refined y contains vy *)
  assert (HYr : mem3 (inter3 (sy3 s)
     (Itv3 (isub3 (zmax (lo3 (sx3 s)) (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))) (hi3 (sz3 s)))
           (isub3 (zmin (hi3 (sx3 s)) (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s)))) (lo3 (sz3 s))))) vy).
  { apply mem3_inter; [split; assumption|]. split; cbn [lo3 hi3].
    - replace vy with (vx - vz) by lia. apply isub3_ub; assumption.
    - replace vy with (vx - vz) by lia. apply isub3_lb; assumption. }
  split; [|split].
  - split; assumption.
  - exact HYr.
  - destruct HYr as [HY1 HY2].
    apply mem3_inter; [split; assumption|]. split; cbn [lo3 hi3].
    + replace vz with (vx - vy) by lia. apply isub3_ub; assumption.
    + replace vz with (vx - vy) by lia. apply isub3_lb; assumption.
Qed.

(* [zadd3_reductive], [zadd3_monotone], [zadd3_idempotent] are derived
   UNCONDITIONALLY from the generic [closure_laws] at the end of the file,
   since under the quotient order best-transformer + soundness + ne-feasibility
   already give a lower closure operator. *)

Theorem zadd3_singleton_complete : forall s vx vy vz,
  sx3 s = Itv3 (Fin vx) (Fin vx) ->
  sy3 s = Itv3 (Fin vy) (Fin vy) ->
  sz3 s = Itv3 (Fin vz) (Fin vz) ->
  ne_store3 (zadd3 s) = true ->
  vx = vy + vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold zadd3 in Hne; cbv zeta in Hne.
  rewrite Hx, Hy, Hz in Hne.
  unfold ne_store3 in Hne.
  apply Bool.andb_true_iff in Hne as [Hne _].
  apply Bool.andb_true_iff in Hne as [Hnex _].
  cbn in Hnex.
  apply Z.leb_le in Hnex. lia.
Qed.

(* ================================================================== *)
(** ** Best abstract transformer (completeness), ne-feasibility,
       and idempotence — the full closure-operator suite, mirroring
       the division propagators in div4.v.                            *)
(* ================================================================== *)

(* The addition constraint as a ternary relation.  [contains3] and
   [feasible3] are provided generically by itv3. *)
Definition asol (vx vy vz : Z) : Prop := vx = vy + vz.

(* ---- non-emptiness / bound extraction ---- *)
Lemma nonempty_bounds3 : forall i, nonempty3b i = true -> lo3 i <> Pinf /\ hi3 i <> Ninf.
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; split; discriminate.
Qed.

Lemma zmax_not_Pinf : forall a b, a <> Pinf -> b <> Pinf -> zmax a b <> Pinf.
Proof. intros [a| |] [b| |] Ha Hb; cbn; congruence. Qed.

Lemma zmin_not_Ninf : forall a b, a <> Ninf -> b <> Ninf -> zmin a b <> Ninf.
Proof. intros [a| |] [b| |] Ha Hb; cbn; congruence. Qed.

(* pick a finite witness inside a nonempty, top-not-Pinf/bot-not-Ninf range *)
Definition pickf (L U : Zinf) : Z :=
  match L with Fin a => a | _ => match U with Fin b => b | _ => 0 end end.

Lemma pickf_mem : forall L U, zle L U -> L <> Pinf -> U <> Ninf ->
  zle L (Fin (pickf L U)) /\ zle (Fin (pickf L U)) U.
Proof.
  intros [a| |] [b| |] Hle HLp HUn; cbn in *; try congruence;
    split; solve [ exact I | lia ].
Qed.

Lemma zmin_zle_r : forall a b, zle (zmin a b) b.
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma zle_zmax_r : forall a b, zle b (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma ne_zle3 : forall i, nonempty3b i = true -> zle (lo3 i) (hi3 i).
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; try exact I;
  apply Z.leb_le; exact H.
Qed.

(* ---- arithmetic bridges between [iadd3]/[isub3] and [zle] ---- *)
Lemma add_sub_lb : forall a b x, zle (iadd3 a b) (Fin x) -> zle a (isub3 (Fin x) b).
Proof. intros [p| |] [q| |] x H; cbn in *; try easy; lia. Qed.

Lemma add_sub_ub : forall a b x, zle (Fin x) (iadd3 a b) -> zle (isub3 (Fin x) b) a.
Proof. intros [p| |] [q| |] x H; cbn in *; try easy; lia. Qed.

Lemma sub_lb : forall c x y, zle (Fin y) (isub3 (Fin x) c) -> zle c (Fin (x - y)).
Proof. intros [d| |] x y H; cbn in *; try easy; lia. Qed.

Lemma sub_ub : forall c x y, zle (isub3 (Fin x) c) (Fin y) -> zle (Fin (x - y)) c.
Proof. intros [d| |] x y H; cbn in *; try easy; lia. Qed.

Lemma isub3_not_Pinf : forall x c, c <> Ninf -> isub3 (Fin x) c <> Pinf.
Proof. intros x [d| |] Hc; cbn; congruence. Qed.

Lemma isub3_not_Ninf : forall x c, c <> Pinf -> isub3 (Fin x) c <> Ninf.
Proof. intros x [d| |] Hc; cbn; congruence. Qed.

(* Minkowski decomposition: any [x] in the sum-hull of two nonempty
   intervals splits as [x = y + z] with [y], [z] members. *)
Lemma add_decomp : forall iy iz x,
  nonempty3b iy = true -> nonempty3b iz = true ->
  zle (iadd3 (lo3 iy) (lo3 iz)) (Fin x) -> zle (Fin x) (iadd3 (hi3 iy) (hi3 iz)) ->
  exists y z, mem3 iy y /\ mem3 iz z /\ x = y + z.
Proof.
  intros iy iz x Hney Hnez H1 H2.
  destruct (nonempty_bounds3 iy Hney) as [Hyl Hyh].
  destruct (nonempty_bounds3 iz Hnez) as [Hzl Hzh].
  pose proof (ne_zle3 iy Hney) as Hyle.
  pose proof (ne_zle3 iz Hnez) as Hzle.
  set (yL := zmax (lo3 iy) (isub3 (Fin x) (hi3 iz))).
  set (yU := zmin (hi3 iy) (isub3 (Fin x) (lo3 iz))).
  assert (HLU : zle yL yU).
  { unfold yL, yU. apply zle_zmin_glb.
    - apply zmax_lub; [ exact Hyle | apply (add_sub_ub _ _ _ H2) ].
    - apply zmax_lub.
      + apply (add_sub_lb _ _ _ H1).
      + apply isub3_mono; [ apply zle_refl | exact Hzle ]. }
  assert (HLp : yL <> Pinf)
    by (unfold yL; apply zmax_not_Pinf; [exact Hyl | apply isub3_not_Pinf; exact Hzh]).
  assert (HUn : yU <> Ninf)
    by (unfold yU; apply zmin_not_Ninf; [exact Hyh | apply isub3_not_Ninf; exact Hzl]).
  destruct (pickf_mem yL yU HLU HLp HUn) as [HyLv HyUv].
  set (y := pickf yL yU) in *.
  exists y, (x - y). split; [ | split ].
  - split.
    + eapply zle_trans; [ apply zle_zmax_l | exact HyLv ].
    + eapply zle_trans; [ exact HyUv | apply zle_zmin_l ].
  - split.
    + apply sub_lb. eapply zle_trans; [ exact HyUv | apply zmin_zle_r ].
    + apply sub_ub. eapply zle_trans; [ apply zle_zmax_r | exact HyLv ].
  - lia.
Qed.

(* ---- membership / bound projection helpers ---- *)
(* [mem3_nonempty] is provided by itv3. *)

Lemma mem_lo_le : forall i v, mem3 i v -> zle (lo3 i) (Fin v).
Proof. intros i v [H1 H2]; exact H1. Qed.

Lemma mem_le_hi : forall i v, mem3 i v -> zle (Fin v) (hi3 i).
Proof. intros i v [H1 H2]; exact H2. Qed.

Lemma bound_mem_hi : forall i H, nonempty3b i = true -> hi3 i = Fin H -> mem3 i H.
Proof.
  intros i H Hne EH. pose proof (ne_zle3 i Hne) as Hle.
  unfold mem3. rewrite EH in *. split; [ exact Hle | apply zle_refl ].
Qed.

Lemma bound_mem_lo : forall i L, nonempty3b i = true -> lo3 i = Fin L -> mem3 i L.
Proof.
  intros i L Hne EL. pose proof (ne_zle3 i Hne) as Hle.
  unfold mem3. rewrite EL in *. split; [ apply zle_refl | exact Hle ].
Qed.

(* The workhorses that reduce an [ile3] bound to "every member of the
   refined interval lands in [t]", handling infinite bounds uniformly. *)
Lemma le_hi_via_witness : forall (J : itv3) (b : Zinf),
  nonempty3b J = true ->
  (forall v, mem3 J v -> zle (Fin v) b) ->
  zle (hi3 J) b.
Proof.
  intros J b Hne Hmem.
  destruct (hi3 J) as [H| |] eqn:EH.
  - apply Hmem. apply (bound_mem_hi J H Hne EH).
  - destruct b as [M| |].
    + exfalso. destruct (lo3 J) as [l| |] eqn:EL.
      * assert (mem3 J (Z.max l (M+1))) as Hm.
        { unfold mem3. rewrite EH, EL. cbn. split; [ lia | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
      * unfold nonempty3b in Hne. rewrite EL in Hne. discriminate.
      * assert (mem3 J (M+1)) as Hm.
        { unfold mem3. rewrite EH, EL. cbn. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
    + exact I.
    + exfalso. destruct (lo3 J) as [l| |] eqn:EL.
      * pose proof (Hmem l (bound_mem_lo J l Hne EL)) as HH. cbn in HH. exact HH.
      * unfold nonempty3b in Hne. rewrite EL in Hne. discriminate.
      * assert (mem3 J 0) as Hm.
        { unfold mem3. rewrite EH, EL. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. exact HH.
  - exfalso. unfold nonempty3b in Hne. rewrite EH in Hne.
    destruct (lo3 J); discriminate.
Qed.

Lemma ge_lo_via_witness : forall (J : itv3) (b : Zinf),
  nonempty3b J = true ->
  (forall v, mem3 J v -> zle b (Fin v)) ->
  zle b (lo3 J).
Proof.
  intros J b Hne Hmem.
  destruct (lo3 J) as [L| |] eqn:EL.
  - apply Hmem. apply (bound_mem_lo J L Hne EL).
  - exfalso. unfold nonempty3b in Hne. rewrite EL in Hne. discriminate.
  - destruct b as [M| |].
    + exfalso. destruct (hi3 J) as [h| |] eqn:EH.
      * assert (mem3 J (Z.min h (M-1))) as Hm.
        { unfold mem3. rewrite EH, EL. cbn. split; [ exact I | lia ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
      * assert (mem3 J (M-1)) as Hm.
        { unfold mem3. rewrite EH, EL. cbn. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
      * unfold nonempty3b in Hne. rewrite EL, EH in Hne. discriminate.
    + exfalso. destruct (hi3 J) as [h| |] eqn:EH.
      * pose proof (Hmem h (bound_mem_hi J h Hne EH)) as HH. cbn in HH. exact HH.
      * assert (mem3 J 0) as Hm.
        { unfold mem3. rewrite EH, EL. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. exact HH.
      * unfold nonempty3b in Hne. rewrite EL, EH in Hne. discriminate.
    + exact I.
Qed.

(* ---- intersection membership inversion + sum/difference attainment ---- *)
Lemma zmax_le_split : forall a b c, zle (zmax a b) c -> zle a c /\ zle b c.
Proof. intros [a| |] [b| |] [c| |] H; cbn in *; split; try easy; lia. Qed.

Lemma zle_zmin_split : forall a b c, zle c (zmin a b) -> zle c a /\ zle c b.
Proof. intros [a| |] [b| |] [c| |] H; cbn in *; split; try easy; lia. Qed.

Lemma mem3_inter_inv : forall i j v, mem3 (inter3 i j) v -> mem3 i v /\ mem3 j v.
Proof.
  intros i j v [H1 H2]. unfold inter3 in *. cbn [lo3 hi3] in H1, H2.
  apply zmax_le_split in H1 as [Ha Hb]. apply zle_zmin_split in H2 as [Hc Hd].
  split; split; assumption.
Qed.

(* Any member of the refined-x interval is the x of a full solution. *)
Lemma attain_x : forall sx sy sz v,
  nonempty3b sy = true -> nonempty3b sz = true ->
  mem3 (inter3 sx (Itv3 (iadd3 (lo3 sy) (lo3 sz)) (iadd3 (hi3 sy) (hi3 sz)))) v ->
  exists vy vz, mem3 sx v /\ mem3 sy vy /\ mem3 sz vz /\ v = vy + vz.
Proof.
  intros sx sy sz v Hney Hnez Hmem.
  apply mem3_inter_inv in Hmem as [Hsx Hhull].
  destruct Hhull as [Hl Hh]. cbn [lo3 hi3] in Hl, Hh.
  destruct (add_decomp sy sz v Hney Hnez Hl Hh) as (vy & vz & Hy & Hz & Heq).
  exists vy, vz. split; [ exact Hsx | split; [ exact Hy | split; [ exact Hz | exact Heq ] ] ].
Qed.

Lemma isub3_fin_not_Pinf : forall a v, a <> Pinf -> isub3 a (Fin v) <> Pinf.
Proof. intros [x| |] v Ha; cbn; congruence. Qed.

Lemma isub3_fin_not_Ninf : forall a v, a <> Ninf -> isub3 a (Fin v) <> Ninf.
Proof. intros [x| |] v Ha; cbn; congruence. Qed.

Lemma sub_lo_bridge : forall c v z, zle (isub3 c (Fin v)) (Fin z) -> zle c (Fin (v + z)).
Proof. intros [x| |] v z H; cbn in *; try easy; lia. Qed.

Lemma sub_hi_bridge : forall c v z, zle (Fin z) (isub3 c (Fin v)) -> zle (Fin (v + z)) c.
Proof. intros [x| |] v z H; cbn in *; try easy; lia. Qed.

Lemma sub_rearr_b : forall hx lz v, zle (Fin v) (isub3 hx lz) -> zle lz (isub3 hx (Fin v)).
Proof. intros [x| |] [z| |] v H; cbn in *; try easy; lia. Qed.

Lemma sub_rearr_c : forall lx hz v, zle (isub3 lx hz) (Fin v) -> zle (isub3 lx (Fin v)) hz.
Proof. intros [x| |] [z| |] v H; cbn in *; try easy; lia. Qed.

(* Difference decomposition: any [v] in the diff-hull [isx - isz] yields
   [x] in [isx] and [z] in [isz] with [x = v + z]. *)
Lemma sub_decomp : forall isx isz v,
  nonempty3b isx = true -> nonempty3b isz = true ->
  zle (isub3 (lo3 isx) (hi3 isz)) (Fin v) ->
  zle (Fin v) (isub3 (hi3 isx) (lo3 isz)) ->
  exists x z, mem3 isx x /\ mem3 isz z /\ x = v + z.
Proof.
  intros isx isz v Hnex Hnez H1 H2.
  destruct (nonempty_bounds3 isx Hnex) as [Hxl Hxh].
  destruct (nonempty_bounds3 isz Hnez) as [Hzl Hzh].
  pose proof (ne_zle3 isx Hnex) as Hxle.
  pose proof (ne_zle3 isz Hnez) as Hzle.
  set (zL := zmax (lo3 isz) (isub3 (lo3 isx) (Fin v))).
  set (zU := zmin (hi3 isz) (isub3 (hi3 isx) (Fin v))).
  assert (HLU : zle zL zU).
  { unfold zL, zU. apply zle_zmin_glb.
    - apply zmax_lub; [ exact Hzle | apply sub_rearr_c; exact H1 ].
    - apply zmax_lub.
      + apply sub_rearr_b; exact H2.
      + apply isub3_mono; [ exact Hxle | apply zle_refl ]. }
  assert (HLp : zL <> Pinf)
    by (unfold zL; apply zmax_not_Pinf; [ exact Hzl | apply isub3_fin_not_Pinf; exact Hxl ]).
  assert (HUn : zU <> Ninf)
    by (unfold zU; apply zmin_not_Ninf; [ exact Hzh | apply isub3_fin_not_Ninf; exact Hxh ]).
  destruct (pickf_mem zL zU HLU HLp HUn) as [HzLv HzUv].
  set (z := pickf zL zU) in *.
  exists (v + z), z. split; [ | split ].
  - split.
    + apply sub_lo_bridge. eapply zle_trans; [ apply zle_zmax_r | exact HzLv ].
    + apply sub_hi_bridge. eapply zle_trans; [ exact HzUv | apply zmin_zle_r ].
  - split.
    + eapply zle_trans; [ apply zle_zmax_l | exact HzLv ].
    + eapply zle_trans; [ exact HzUv | apply zle_zmin_l ].
  - reflexivity.
Qed.

(* ---- best abstract transformer: [zadd3 s] is the tightest sound box.
       Stated first with an explicit feasibility witness; [zadd3_complete]
       below drops it (an empty output is bottom, a non-empty one is feasible). *)
Lemma zadd3_best_feasible : forall s,
  feasible3 asol s ->
  forall t, contains3 asol s t -> sle3 (zadd3 s) t.
Proof.
  intros s (fx & fy & fz & Hin & Hasol) t Hct.
  destruct Hin as (Hfx & Hfy & Hfz).
  pose proof (mem3_nonempty _ _ Hfy) as Hney0.
  pose proof (mem3_nonempty _ _ Hfz) as Hnez0.
  pose proof (zadd3_soundness s fx fy fz (conj Hfx (conj Hfy Hfz)) Hasol) as Hsol.
  unfold zadd3 in *; cbv zeta in *.
  set (X := inter3 (sx3 s) (Itv3 (iadd3 (lo3 (sy3 s)) (lo3 (sz3 s)))
                                 (iadd3 (hi3 (sy3 s)) (hi3 (sz3 s))))) in *.
  set (Y := inter3 (sy3 s) (Itv3 (isub3 (lo3 X) (hi3 (sz3 s)))
                                 (isub3 (hi3 X) (lo3 (sz3 s))))) in *.
  set (Z := inter3 (sz3 s) (Itv3 (isub3 (lo3 X) (hi3 Y))
                                 (isub3 (hi3 X) (lo3 Y)))) in *.
  destruct Hsol as (HmX & HmY & HmZ). cbn [sx3 sy3 sz3] in HmX, HmY, HmZ.
  pose proof (mem3_nonempty _ _ HmX) as HneX.
  pose proof (mem3_nonempty _ _ HmY) as HneY.
  pose proof (mem3_nonempty _ _ HmZ) as HneZ.
  apply sle3_intro; cbn [sx3 sy3 sz3].
  - apply ile3_intro.
    + apply ge_lo_via_witness; [ exact HneX |].
      intros v Hv.
      destruct (attain_x (sx3 s) (sy3 s) (sz3 s) v Hney0 Hnez0 Hv)
        as (vy & vz & Hsxv & Hsyv & Hszv & Heqv).
      destruct (Hct v vy vz (conj Hsxv (conj Hsyv Hszv)) Heqv) as (Htx & _ & _).
      apply (mem_lo_le _ _ Htx).
    + apply le_hi_via_witness; [ exact HneX |].
      intros v Hv.
      destruct (attain_x (sx3 s) (sy3 s) (sz3 s) v Hney0 Hnez0 Hv)
        as (vy & vz & Hsxv & Hsyv & Hszv & Heqv).
      destruct (Hct v vy vz (conj Hsxv (conj Hsyv Hszv)) Heqv) as (Htx & _ & _).
      apply (mem_le_hi _ _ Htx).
  - apply ile3_intro.
    + apply ge_lo_via_witness; [ exact HneY |].
      intros v Hv.
      apply mem3_inter_inv in Hv as [Hsyv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lo3 hi3] in Hd1, Hd2.
      destruct (sub_decomp X (sz3 s) v HneX Hnez0 Hd1 Hd2) as (x & z & HmXx & Hszz & Hxeq).
      apply mem3_inter_inv in HmXx as [Hsxx _].
      destruct (Hct x v z (conj Hsxx (conj Hsyv Hszz)) Hxeq) as (_ & Hty & _).
      apply (mem_lo_le _ _ Hty).
    + apply le_hi_via_witness; [ exact HneY |].
      intros v Hv.
      apply mem3_inter_inv in Hv as [Hsyv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lo3 hi3] in Hd1, Hd2.
      destruct (sub_decomp X (sz3 s) v HneX Hnez0 Hd1 Hd2) as (x & z & HmXx & Hszz & Hxeq).
      apply mem3_inter_inv in HmXx as [Hsxx _].
      destruct (Hct x v z (conj Hsxx (conj Hsyv Hszz)) Hxeq) as (_ & Hty & _).
      apply (mem_le_hi _ _ Hty).
  - apply ile3_intro.
    + apply ge_lo_via_witness; [ exact HneZ |].
      intros v Hv.
      apply mem3_inter_inv in Hv as [Hszv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lo3 hi3] in Hd1, Hd2.
      destruct (sub_decomp X Y v HneX HneY Hd1 Hd2) as (x & y & HmXx & HmYy & Hxeq).
      apply mem3_inter_inv in HmXx as [Hsxx _].
      apply mem3_inter_inv in HmYy as [Hsyy _].
      assert (Hasz : x = y + v) by lia.
      destruct (Hct x y v (conj Hsxx (conj Hsyy Hszv)) Hasz) as (_ & _ & Htz).
      apply (mem_lo_le _ _ Htz).
    + apply le_hi_via_witness; [ exact HneZ |].
      intros v Hv.
      apply mem3_inter_inv in Hv as [Hszv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lo3 hi3] in Hd1, Hd2.
      destruct (sub_decomp X Y v HneX HneY Hd1 Hd2) as (x & y & HmXx & HmYy & Hxeq).
      apply mem3_inter_inv in HmXx as [Hsxx _].
      apply mem3_inter_inv in HmYy as [Hsyy _].
      assert (Hasz : x = y + v) by lia.
      destruct (Hct x y v (conj Hsxx (conj Hsyy Hszv)) Hasz) as (_ & _ & Htz).
      apply (mem_le_hi _ _ Htz).
Qed.

(* ---- ne-feasibility: a nonempty result means the input was feasible ---- *)
Lemma nonempty_witness : forall i, nonempty3b i = true -> exists v, mem3 i v.
Proof.
  intros [[a| |] [b| |]] H; cbn in H; try discriminate.
  - apply Z.leb_le in H. exists a. unfold mem3; cbn. split; lia.
  - exists a. unfold mem3; cbn. split; [ lia | exact I ].
  - exists b. unfold mem3; cbn. split; [ exact I | lia ].
  - exists 0. unfold mem3; cbn. split; exact I.
Qed.

Theorem zadd3_ne_feasible : forall s,
  ne_store3 (zadd3 s) = true -> feasible3 asol s.
Proof.
  intros s Hne.
  unfold zadd3 in Hne; cbv zeta in Hne.
  unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne.
  apply andb_true_iff in Hne as [Hne HneZ].
  apply andb_true_iff in Hne as [HneX HneY].
  pose proof (ne_inter3 _ _ HneY) as Hney.
  pose proof (ne_inter3 _ _ HneZ) as Hnez.
  destruct (nonempty_witness _ HneX) as [vx HmX].
  destruct (attain_x (sx3 s) (sy3 s) (sz3 s) vx Hney Hnez HmX)
    as (vy & vz & Hsxv & Hsyv & Hszv & Heqv).
  exists vx, vy, vz.
  split; [ split; [ exact Hsxv | split; [ exact Hsyv | exact Hszv ] ] | exact Heqv ].
Qed.

(* ---- best abstract transformer, UNCONDITIONAL: under the quotient order an
        empty [zadd3 s] is bottom (below every [t]); a non-empty one is feasible
        (via [zadd3_ne_feasible]), so [zadd3_best_feasible] applies. *)
Theorem zadd3_complete : forall s t,
  contains3 asol s t -> sle3 (zadd3 s) t.
Proof.
  intros s t Hct. destruct (ne_store3 (zadd3 s)) eqn:E.
  - exact (zadd3_best_feasible s (zadd3_ne_feasible s E) t Hct).
  - apply sle3_bot; exact E.
Qed.

(* ---- [zadd3] is a lower closure operator over the QUOTIENT order:
        reductive, monotone, and idempotent (up to the bottom equivalence
        ~, i.e. mutual [sle3]) — all UNCONDITIONAL, obtained from the
        generic [closure_laws] via soundness + best-transformer + ne-feasibility. *)
Definition zadd3_closure :=
  closure_laws asol zadd3 zadd3_soundness
    (fun s (_ : feasible3 asol s) => zadd3_complete s) zadd3_ne_feasible.

Theorem zadd3_reductive : forall s, sle3 (zadd3 s) s.
Proof. apply (proj1 zadd3_closure). Qed.

Theorem zadd3_monotone : forall s t, sle3 s t -> sle3 (zadd3 s) (zadd3 t).
Proof. apply (proj1 (proj2 zadd3_closure)). Qed.

Theorem zadd3_idempotent : forall s,
  sle3 (zadd3 (zadd3 s)) (zadd3 s) /\ sle3 (zadd3 s) (zadd3 (zadd3 s)).
Proof. apply (proj2 (proj2 zadd3_closure)). Qed.
