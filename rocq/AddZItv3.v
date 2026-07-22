(** * add_zitv3: the addition propagator with INFINITE bounds

    Rocq model of the C++ [add_zitv3] (zinterval.hpp): x = y + z over zinf
    intervals, refining x by the sum hull, then y and z by difference hulls
    (each using the already-refined companions), with no finiteness guard.

    The full propagator property suite is proved (mirroring div4.v):
      - soundness              : [add_zitv3_soundness]
      - best transformer       : [zadd3_complete]    (completeness)
      - ne-feasibility         : [zadd3_ne_feasible]
      - reductivity            : [zadd3_reductive]    (unconditional)
      - monotonicity           : [zadd3_monotone]     (unconditional)
      - idempotence            : [zadd3_idempotent]   (unconditional, up to ~)
      - completeness/singleton : [zadd3_singleton_complete]

    Order is the QUOTIENTED lattice one (zitv.leq_zitv/sle3): empties = bottom. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import ZItv3.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** The propagator for the addition constraint x = y + z              *)
(* ------------------------------------------------------------------ *)

Definition add_zitv3 (s : zitv3) : zitv3 :=
  let x := meet_zitv (x s) (ZItv (add_zinf (lb (sy3 s)) (lb (sz3 s)))
                                (add_zinf (ub (sy3 s)) (ub (sz3 s)))) in
  let y := meet_zitv (sy3 s) (ZItv (sub_zinf (lb x) (ub (sz3 s)))
                                (sub_zinf (ub x) (lb (sz3 s)))) in
  let z := meet_zitv (sz3 s) (ZItv (sub_zinf (lb x) (ub y))
                                (sub_zinf (ub x) (lb y))) in
  ZItv3 x y z.

(* ------------------------------------------------------------------ *)
(** ** The four propagator properties                                  *)
(* ------------------------------------------------------------------ *)

Theorem add_zitv3_soundness : forall s vx vy vz,
  in_zitv3 s vx vy vz -> vx = vy + vz ->
  in_zitv3 (add_zitv3 s) vx vy vz.
Proof.
  intros s vx vy vz (Hx & Hy & Hz) Heq.
  destruct Hx as [Hx1 Hx2], Hy as [Hy1 Hy2], Hz as [Hz1 Hz2].
  unfold add_zitv3; cbv zeta.
  (* refined x contains vx *)
  assert (HXr : contains (meet_zitv (x s) (ZItv (add_zinf (lb (sy3 s)) (lb (sz3 s)))
                                           (add_zinf (ub (sy3 s)) (ub (sz3 s))))) vx).
  { apply contains_inter; [split; assumption|]. split; cbn [lb ub].
    - replace vx with (vy + vz) by lia. apply add_zinf_ub; assumption.
    - replace vx with (vy + vz) by lia. apply add_zinf_lb; assumption. }
  destruct HXr as [HX1 HX2].
  (* refined y contains vy *)
  assert (HYr : contains (meet_zitv (sy3 s)
     (ZItv (sub_zinf (max_zinf (lb (x s)) (add_zinf (lb (sy3 s)) (lb (sz3 s)))) (ub (sz3 s)))
           (sub_zinf (min_zinf (ub (x s)) (add_zinf (ub (sy3 s)) (ub (sz3 s)))) (lb (sz3 s))))) vy).
  { apply contains_inter; [split; assumption|]. split; cbn [lb ub].
    - replace vy with (vx - vz) by lia. apply sub_zinf_ub; assumption.
    - replace vy with (vx - vz) by lia. apply sub_zinf_lb; assumption. }
  split; [|split].
  - split; assumption.
  - exact HYr.
  - destruct HYr as [HY1 HY2].
    apply contains_inter; [split; assumption|]. split; cbn [lb ub].
    + replace vz with (vx - vy) by lia. apply sub_zinf_ub; assumption.
    + replace vz with (vx - vy) by lia. apply sub_zinf_lb; assumption.
Qed.

(* [zadd3_reductive], [zadd3_monotone], [zadd3_idempotent] are derived
   UNCONDITIONALLY from the generic [closure_laws] at the end of the file,
   since under the quotient order best-transformer + soundness + ne-feasibility
   already give a lower closure operator. *)

Theorem zadd3_singleton_complete : forall s vx vy vz,
  x s = ZItv (Fin vx) (Fin vx) ->
  sy3 s = ZItv (Fin vy) (Fin vy) ->
  sz3 s = ZItv (Fin vz) (Fin vz) ->
  ne_zitv3 (add_zitv3 s) = true ->
  vx = vy + vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  unfold add_zitv3 in Hne; cbv zeta in Hne.
  rewrite Hx, Hy, Hz in Hne.
  unfold ne_zitv3 in Hne.
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
   [feasible3] are provided generically by zitv. *)
Definition asol (vx vy vz : Z) : Prop := vx = vy + vz.

(* ---- non-emptiness / bound extraction ---- *)
Lemma nonempty_bounds3 : forall i, is_not_bot_zitv i = true -> lb i <> Pinf /\ ub i <> Ninf.
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; split; discriminate.
Qed.

Lemma max_zinf_not_Pinf : forall a b, a <> Pinf -> b <> Pinf -> max_zinf a b <> Pinf.
Proof. intros [a| |] [b| |] Ha Hb; cbn; congruence. Qed.

Lemma min_zinf_not_Ninf : forall a b, a <> Ninf -> b <> Ninf -> min_zinf a b <> Ninf.
Proof. intros [a| |] [b| |] Ha Hb; cbn; congruence. Qed.

(* pick a finite witness inside a nonempty, top-not-Pinf/bot-not-Ninf range *)
Definition pickf (L U : zinf) : Z :=
  match L with Fin a => a | _ => match U with Fin b => b | _ => 0 end end.

Lemma pickf_mem : forall L U, leq_zinf L U -> L <> Pinf -> U <> Ninf ->
  leq_zinf L (Fin (pickf L U)) /\ leq_zinf (Fin (pickf L U)) U.
Proof.
  intros [a| |] [b| |] Hle HLp HUn; cbn in *; try congruence;
    split; solve [ exact I | lia ].
Qed.

Lemma min_zinf_leq_zinf_r : forall a b, leq_zinf (min_zinf a b) b.
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma leq_zinf_max_zinf_r : forall a b, leq_zinf b (max_zinf a b).
Proof. intros [x| |] [y| |]; cbn; try easy; lia. Qed.

Lemma ne_leq_zinf3 : forall i, is_not_bot_zitv i = true -> leq_zinf (lb i) (ub i).
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; try exact I;
  apply Z.leb_le; exact H.
Qed.

(* ---- arithmetic bridges between [add_zinf]/[sub_zinf] and [leq_zinf] ---- *)
Lemma add_sub_lb : forall a b x, leq_zinf (add_zinf a b) (Fin x) -> leq_zinf a (sub_zinf (Fin x) b).
Proof. intros [p| |] [q| |] x H; cbn in *; try easy; lia. Qed.

Lemma add_sub_ub : forall a b x, leq_zinf (Fin x) (add_zinf a b) -> leq_zinf (sub_zinf (Fin x) b) a.
Proof. intros [p| |] [q| |] x H; cbn in *; try easy; lia. Qed.

Lemma sub_lb : forall c x y, leq_zinf (Fin y) (sub_zinf (Fin x) c) -> leq_zinf c (Fin (x - y)).
Proof. intros [d| |] x y H; cbn in *; try easy; lia. Qed.

Lemma sub_ub : forall c x y, leq_zinf (sub_zinf (Fin x) c) (Fin y) -> leq_zinf (Fin (x - y)) c.
Proof. intros [d| |] x y H; cbn in *; try easy; lia. Qed.

Lemma isub3_not_Pinf : forall x c, c <> Ninf -> sub_zinf (Fin x) c <> Pinf.
Proof. intros x [d| |] Hc; cbn; congruence. Qed.

Lemma isub3_not_Ninf : forall x c, c <> Pinf -> sub_zinf (Fin x) c <> Ninf.
Proof. intros x [d| |] Hc; cbn; congruence. Qed.

(* Minkowski decomposition: any [x] in the sum-hull of two nonempty
   intervals splits as [x = y + z] with [y], [z] members. *)
Lemma add_decomp : forall iy iz x,
  is_not_bot_zitv iy = true -> is_not_bot_zitv iz = true ->
  leq_zinf (add_zinf (lb iy) (lb iz)) (Fin x) -> leq_zinf (Fin x) (add_zinf (ub iy) (ub iz)) ->
  exists y z, contains iy y /\ contains iz z /\ x = y + z.
Proof.
  intros iy iz x Hney Hnez H1 H2.
  destruct (nonempty_bounds3 iy Hney) as [Hyl Hyh].
  destruct (nonempty_bounds3 iz Hnez) as [Hzl Hzh].
  pose proof (ne_leq_zinf3 iy Hney) as Hyle.
  pose proof (ne_leq_zinf3 iz Hnez) as Hleq_zinf.
  set (yL := max_zinf (lb iy) (sub_zinf (Fin x) (ub iz))).
  set (yU := min_zinf (ub iy) (sub_zinf (Fin x) (lb iz))).
  assert (HLU : leq_zinf yL yU).
  { unfold yL, yU. apply leq_zinf_min_zinf_glb.
    - apply max_zinf_lub; [ exact Hyle | apply (add_sub_ub _ _ _ H2) ].
    - apply max_zinf_lub.
      + apply (add_sub_lb _ _ _ H1).
      + apply sub_zinf_monotone; [ apply leq_zinf_refl | exact Hleq_zinf ]. }
  assert (HLp : yL <> Pinf)
    by (unfold yL; apply max_zinf_not_Pinf; [exact Hyl | apply isub3_not_Pinf; exact Hzh]).
  assert (HUn : yU <> Ninf)
    by (unfold yU; apply min_zinf_not_Ninf; [exact Hyh | apply isub3_not_Ninf; exact Hzl]).
  destruct (pickf_mem yL yU HLU HLp HUn) as [HyLv HyUv].
  set (y := pickf yL yU) in *.
  exists y, (x - y). split; [ | split ].
  - split.
    + eapply leq_zinf_trans; [ apply leq_zinf_max_zinf_l | exact HyLv ].
    + eapply leq_zinf_trans; [ exact HyUv | apply leq_zinf_min_zinf_l ].
  - split.
    + apply sub_lb. eapply leq_zinf_trans; [ exact HyUv | apply min_zinf_leq_zinf_r ].
    + apply sub_ub. eapply leq_zinf_trans; [ apply leq_zinf_max_zinf_r | exact HyLv ].
  - lia.
Qed.

(* ---- membership / bound projection helpers ---- *)
(* [contains_nonempty] is provided by zitv. *)

Lemma mem_lo_le : forall i v, contains i v -> leq_zinf (lb i) (Fin v).
Proof. intros i v [H1 H2]; exact H1. Qed.

Lemma mem_le_hi : forall i v, contains i v -> leq_zinf (Fin v) (ub i).
Proof. intros i v [H1 H2]; exact H2. Qed.

Lemma bound_mem_hi : forall i H, is_not_bot_zitv i = true -> ub i = Fin H -> contains i H.
Proof.
  intros i H Hne EH. pose proof (ne_leq_zinf3 i Hne) as Hle.
  unfold contains. rewrite EH in *. split; [ exact Hle | apply leq_zinf_refl ].
Qed.

Lemma bound_mem_lo : forall i L, is_not_bot_zitv i = true -> lb i = Fin L -> contains i L.
Proof.
  intros i L Hne EL. pose proof (ne_leq_zinf3 i Hne) as Hle.
  unfold contains. rewrite EL in *. split; [ apply leq_zinf_refl | exact Hle ].
Qed.

(* The workhorses that reduce an [leq_zitv] bound to "every member of the
   refined interval lands in [t]", handling infinite bounds uniformly. *)
Lemma le_hi_via_witness : forall (J : zitv) (b : zinf),
  is_not_bot_zitv J = true ->
  (forall v, contains J v -> leq_zinf (Fin v) b) ->
  leq_zinf (ub J) b.
Proof.
  intros J b Hne Hmem.
  destruct (ub J) as [H| |] eqn:EH.
  - apply Hmem. apply (bound_mem_hi J H Hne EH).
  - destruct b as [M| |].
    + exfalso. destruct (lb J) as [l| |] eqn:EL.
      * assert (contains J (Z.max l (M+1))) as Hm.
        { unfold contains. rewrite EH, EL. cbn. split; [ lia | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
      * unfold is_not_bot_zitv in Hne. rewrite EL in Hne. discriminate.
      * assert (contains J (M+1)) as Hm.
        { unfold contains. rewrite EH, EL. cbn. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
    + exact I.
    + exfalso. destruct (lb J) as [l| |] eqn:EL.
      * pose proof (Hmem l (bound_mem_lo J l Hne EL)) as HH. cbn in HH. exact HH.
      * unfold is_not_bot_zitv in Hne. rewrite EL in Hne. discriminate.
      * assert (contains J 0) as Hm.
        { unfold contains. rewrite EH, EL. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. exact HH.
  - exfalso. unfold is_not_bot_zitv in Hne. rewrite EH in Hne.
    destruct (lb J); discriminate.
Qed.

Lemma ge_lo_via_witness : forall (J : zitv) (b : zinf),
  is_not_bot_zitv J = true ->
  (forall v, contains J v -> leq_zinf b (Fin v)) ->
  leq_zinf b (lb J).
Proof.
  intros J b Hne Hmem.
  destruct (lb J) as [L| |] eqn:EL.
  - apply Hmem. apply (bound_mem_lo J L Hne EL).
  - exfalso. unfold is_not_bot_zitv in Hne. rewrite EL in Hne. discriminate.
  - destruct b as [M| |].
    + exfalso. destruct (ub J) as [h| |] eqn:EH.
      * assert (contains J (Z.min h (M-1))) as Hm.
        { unfold contains. rewrite EH, EL. cbn. split; [ exact I | lia ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
      * assert (contains J (M-1)) as Hm.
        { unfold contains. rewrite EH, EL. cbn. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. lia.
      * unfold is_not_bot_zitv in Hne. rewrite EL, EH in Hne. discriminate.
    + exfalso. destruct (ub J) as [h| |] eqn:EH.
      * pose proof (Hmem h (bound_mem_hi J h Hne EH)) as HH. cbn in HH. exact HH.
      * assert (contains J 0) as Hm.
        { unfold contains. rewrite EH, EL. split; [ exact I | exact I ]. }
        pose proof (Hmem _ Hm) as HH. cbn in HH. exact HH.
      * unfold is_not_bot_zitv in Hne. rewrite EL, EH in Hne. discriminate.
    + exact I.
Qed.

(* ---- intersection membership inversion + sum/difference attainment ---- *)
Lemma max_zinf_le_split : forall a b c, leq_zinf (max_zinf a b) c -> leq_zinf a c /\ leq_zinf b c.
Proof. intros [a| |] [b| |] [c| |] H; cbn in *; split; try easy; lia. Qed.

Lemma leq_zinf_min_zinf_split : forall a b c, leq_zinf c (min_zinf a b) -> leq_zinf c a /\ leq_zinf c b.
Proof. intros [a| |] [b| |] [c| |] H; cbn in *; split; try easy; lia. Qed.

Lemma contains_inter_inv : forall i j v, contains (meet_zitv i j) v -> contains i v /\ contains j v.
Proof.
  intros i j v [H1 H2]. unfold meet_zitv in *. cbn [lb ub] in H1, H2.
  apply max_zinf_le_split in H1 as [Ha Hb]. apply leq_zinf_min_zinf_split in H2 as [Hc Hd].
  split; split; assumption.
Qed.

(* Any member of the refined-x interval is the x of a full solution. *)
Lemma attain_x : forall sx sy sz v,
  is_not_bot_zitv sy = true -> is_not_bot_zitv sz = true ->
  contains (meet_zitv sx (ZItv (add_zinf (lb sy) (lb sz)) (add_zinf (ub sy) (ub sz)))) v ->
  exists vy vz, contains sx v /\ contains sy vy /\ contains sz vz /\ v = vy + vz.
Proof.
  intros sx sy sz v Hney Hnez Hmem.
  apply contains_inter_inv in Hmem as [Hsx Hhull].
  destruct Hhull as [Hl Hh]. cbn [lb ub] in Hl, Hh.
  destruct (add_decomp sy sz v Hney Hnez Hl Hh) as (vy & vz & Hy & Hz & Heq).
  exists vy, vz. split; [ exact Hsx | split; [ exact Hy | split; [ exact Hz | exact Heq ] ] ].
Qed.

Lemma isub3_fin_not_Pinf : forall a v, a <> Pinf -> sub_zinf a (Fin v) <> Pinf.
Proof. intros [x| |] v Ha; cbn; congruence. Qed.

Lemma isub3_fin_not_Ninf : forall a v, a <> Ninf -> sub_zinf a (Fin v) <> Ninf.
Proof. intros [x| |] v Ha; cbn; congruence. Qed.

Lemma sub_lo_bridge : forall c v z, leq_zinf (sub_zinf c (Fin v)) (Fin z) -> leq_zinf c (Fin (v + z)).
Proof. intros [x| |] v z H; cbn in *; try easy; lia. Qed.

Lemma sub_hi_bridge : forall c v z, leq_zinf (Fin z) (sub_zinf c (Fin v)) -> leq_zinf (Fin (v + z)) c.
Proof. intros [x| |] v z H; cbn in *; try easy; lia. Qed.

Lemma sub_rearr_b : forall hx lz v, leq_zinf (Fin v) (sub_zinf hx lz) -> leq_zinf lz (sub_zinf hx (Fin v)).
Proof. intros [x| |] [z| |] v H; cbn in *; try easy; lia. Qed.

Lemma sub_rearr_c : forall lx hz v, leq_zinf (sub_zinf lx hz) (Fin v) -> leq_zinf (sub_zinf lx (Fin v)) hz.
Proof. intros [x| |] [z| |] v H; cbn in *; try easy; lia. Qed.

(* Difference decomposition: any [v] in the diff-hull [isx - isz] yields
   [x] in [isx] and [z] in [isz] with [x = v + z]. *)
Lemma sub_decomp : forall isx isz v,
  is_not_bot_zitv isx = true -> is_not_bot_zitv isz = true ->
  leq_zinf (sub_zinf (lb isx) (ub isz)) (Fin v) ->
  leq_zinf (Fin v) (sub_zinf (ub isx) (lb isz)) ->
  exists x z, contains isx x /\ contains isz z /\ x = v + z.
Proof.
  intros isx isz v Hnex Hnez H1 H2.
  destruct (nonempty_bounds3 isx Hnex) as [Hxl Hxh].
  destruct (nonempty_bounds3 isz Hnez) as [Hzl Hzh].
  pose proof (ne_leq_zinf3 isx Hnex) as Hxle.
  pose proof (ne_leq_zinf3 isz Hnez) as Hleq_zinf.
  set (zL := max_zinf (lb isz) (sub_zinf (lb isx) (Fin v))).
  set (zU := min_zinf (ub isz) (sub_zinf (ub isx) (Fin v))).
  assert (HLU : leq_zinf zL zU).
  { unfold zL, zU. apply leq_zinf_min_zinf_glb.
    - apply max_zinf_lub; [ exact Hleq_zinf | apply sub_rearr_c; exact H1 ].
    - apply max_zinf_lub.
      + apply sub_rearr_b; exact H2.
      + apply sub_zinf_monotone; [ exact Hxle | apply leq_zinf_refl ]. }
  assert (HLp : zL <> Pinf)
    by (unfold zL; apply max_zinf_not_Pinf; [ exact Hzl | apply isub3_fin_not_Pinf; exact Hxl ]).
  assert (HUn : zU <> Ninf)
    by (unfold zU; apply min_zinf_not_Ninf; [ exact Hzh | apply isub3_fin_not_Ninf; exact Hxh ]).
  destruct (pickf_mem zL zU HLU HLp HUn) as [HzLv HzUv].
  set (z := pickf zL zU) in *.
  exists (v + z), z. split; [ | split ].
  - split.
    + apply sub_lo_bridge. eapply leq_zinf_trans; [ apply leq_zinf_max_zinf_r | exact HzLv ].
    + apply sub_hi_bridge. eapply leq_zinf_trans; [ exact HzUv | apply min_zinf_leq_zinf_r ].
  - split.
    + eapply leq_zinf_trans; [ apply leq_zinf_max_zinf_l | exact HzLv ].
    + eapply leq_zinf_trans; [ exact HzUv | apply leq_zinf_min_zinf_l ].
  - reflexivity.
Qed.

(* ---- best abstract transformer: [add_zitv3 s] is the tightest sound box.
       Stated first with an explicit feasibility witness; [zadd3_complete]
       below drops it (an empty output is bottom, a non-empty one is feasible). *)
Lemma zadd3_best_feasible : forall s,
  feasible3 asol s ->
  forall t, contains3 asol s t -> sle3 (add_zitv3 s) t.
Proof.
  intros s (fx & fy & fz & Hin & Hasol) t Hct.
  destruct Hin as (Hfx & Hfy & Hfz).
  pose proof (contains_nonempty _ _ Hfy) as Hney0.
  pose proof (contains_nonempty _ _ Hfz) as Hnez0.
  pose proof (add_zitv3_soundness s fx fy fz (conj Hfx (conj Hfy Hfz)) Hasol) as Hsol.
  unfold add_zitv3 in *; cbv zeta in *.
  set (X := meet_zitv (x s) (ZItv (add_zinf (lb (sy3 s)) (lb (sz3 s)))
                                 (add_zinf (ub (sy3 s)) (ub (sz3 s))))) in *.
  set (Y := meet_zitv (sy3 s) (ZItv (sub_zinf (lb X) (ub (sz3 s)))
                                 (sub_zinf (ub X) (lb (sz3 s))))) in *.
  set (Z := meet_zitv (sz3 s) (ZItv (sub_zinf (lb X) (ub Y))
                                 (sub_zinf (ub X) (lb Y)))) in *.
  destruct Hsol as (HmX & HmY & HmZ). cbn [x sy3 sz3] in HmX, HmY, HmZ.
  pose proof (contains_nonempty _ _ HmX) as HneX.
  pose proof (contains_nonempty _ _ HmY) as HneY.
  pose proof (contains_nonempty _ _ HmZ) as HneZ.
  apply sle3_intro; cbn [x sy3 sz3].
  - apply leq_zitv_intro.
    + apply ge_lo_via_witness; [ exact HneX |].
      intros v Hv.
      destruct (attain_x (x s) (sy3 s) (sz3 s) v Hney0 Hnez0 Hv)
        as (vy & vz & Hsxv & Hsyv & Hszv & Heqv).
      destruct (Hct v vy vz (conj Hsxv (conj Hsyv Hszv)) Heqv) as (Htx & _ & _).
      apply (mem_lo_le _ _ Htx).
    + apply le_hi_via_witness; [ exact HneX |].
      intros v Hv.
      destruct (attain_x (x s) (sy3 s) (sz3 s) v Hney0 Hnez0 Hv)
        as (vy & vz & Hsxv & Hsyv & Hszv & Heqv).
      destruct (Hct v vy vz (conj Hsxv (conj Hsyv Hszv)) Heqv) as (Htx & _ & _).
      apply (mem_le_hi _ _ Htx).
  - apply leq_zitv_intro.
    + apply ge_lo_via_witness; [ exact HneY |].
      intros v Hv.
      apply contains_inter_inv in Hv as [Hsyv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lb ub] in Hd1, Hd2.
      destruct (sub_decomp X (sz3 s) v HneX Hnez0 Hd1 Hd2) as (x & z & HmXx & Hszz & Hxeq).
      apply contains_inter_inv in HmXx as [Hsxx _].
      destruct (Hct x v z (conj Hsxx (conj Hsyv Hszz)) Hxeq) as (_ & Hty & _).
      apply (mem_lo_le _ _ Hty).
    + apply le_hi_via_witness; [ exact HneY |].
      intros v Hv.
      apply contains_inter_inv in Hv as [Hsyv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lb ub] in Hd1, Hd2.
      destruct (sub_decomp X (sz3 s) v HneX Hnez0 Hd1 Hd2) as (x & z & HmXx & Hszz & Hxeq).
      apply contains_inter_inv in HmXx as [Hsxx _].
      destruct (Hct x v z (conj Hsxx (conj Hsyv Hszz)) Hxeq) as (_ & Hty & _).
      apply (mem_le_hi _ _ Hty).
  - apply leq_zitv_intro.
    + apply ge_lo_via_witness; [ exact HneZ |].
      intros v Hv.
      apply contains_inter_inv in Hv as [Hszv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lb ub] in Hd1, Hd2.
      destruct (sub_decomp X Y v HneX HneY Hd1 Hd2) as (x & y & HmXx & HmYy & Hxeq).
      apply contains_inter_inv in HmXx as [Hsxx _].
      apply contains_inter_inv in HmYy as [Hsyy _].
      assert (Hasz : x = y + v) by lia.
      destruct (Hct x y v (conj Hsxx (conj Hsyy Hszv)) Hasz) as (_ & _ & Htz).
      apply (mem_lo_le _ _ Htz).
    + apply le_hi_via_witness; [ exact HneZ |].
      intros v Hv.
      apply contains_inter_inv in Hv as [Hszv Hdiff].
      destruct Hdiff as [Hd1 Hd2]. cbn [lb ub] in Hd1, Hd2.
      destruct (sub_decomp X Y v HneX HneY Hd1 Hd2) as (x & y & HmXx & HmYy & Hxeq).
      apply contains_inter_inv in HmXx as [Hsxx _].
      apply contains_inter_inv in HmYy as [Hsyy _].
      assert (Hasz : x = y + v) by lia.
      destruct (Hct x y v (conj Hsxx (conj Hsyy Hszv)) Hasz) as (_ & _ & Htz).
      apply (mem_le_hi _ _ Htz).
Qed.

(* ---- ne-feasibility: a nonempty result means the input was feasible ---- *)
Lemma nonempty_witness : forall i, is_not_bot_zitv i = true -> exists v, contains i v.
Proof.
  intros [[a| |] [b| |]] H; cbn in H; try discriminate.
  - apply Z.leb_le in H. exists a. unfold contains; cbn. split; lia.
  - exists a. unfold contains; cbn. split; [ lia | exact I ].
  - exists b. unfold contains; cbn. split; [ exact I | lia ].
  - exists 0. unfold contains; cbn. split; exact I.
Qed.

Theorem zadd3_ne_feasible : forall s,
  ne_zitv3 (add_zitv3 s) = true -> feasible3 asol s.
Proof.
  intros s Hne.
  unfold add_zitv3 in Hne; cbv zeta in Hne.
  unfold ne_zitv3 in Hne; cbn [x sy3 sz3] in Hne.
  apply andb_true_iff in Hne as [Hne HneZ].
  apply andb_true_iff in Hne as [HneX HneY].
  pose proof (ne_inter3 _ _ HneY) as Hney.
  pose proof (ne_inter3 _ _ HneZ) as Hnez.
  destruct (nonempty_witness _ HneX) as [vx HmX].
  destruct (attain_x (x s) (sy3 s) (sz3 s) vx Hney Hnez HmX)
    as (vy & vz & Hsxv & Hsyv & Hszv & Heqv).
  exists vx, vy, vz.
  split; [ split; [ exact Hsxv | split; [ exact Hsyv | exact Hszv ] ] | exact Heqv ].
Qed.

(* ---- best abstract transformer, UNCONDITIONAL: under the quotient order an
        empty [add_zitv3 s] is bottom (below every [t]); a non-empty one is feasible
        (via [zadd3_ne_feasible]), so [zadd3_best_feasible] applies. *)
Theorem zadd3_complete : forall s t,
  contains3 asol s t -> sle3 (add_zitv3 s) t.
Proof.
  intros s t Hct. destruct (ne_zitv3 (add_zitv3 s)) eqn:E.
  - exact (zadd3_best_feasible s (zadd3_ne_feasible s E) t Hct).
  - apply sle3_bot; exact E.
Qed.

(* ---- [add_zitv3] is a lower closure operator over the QUOTIENT order:
        reductive, monotone, and idempotent (up to the bottom equivalence
        ~, i.e. mutual [sle3]) — all UNCONDITIONAL, obtained from the
        generic [closure_laws] via soundness + best-transformer + ne-feasibility. *)
Definition zadd3_closure :=
  closure_laws asol add_zitv3 add_zitv3_soundness
    (fun s (_ : feasible3 asol s) => zadd3_complete s) zadd3_ne_feasible.

Theorem zadd3_reductive : forall s, sle3 (add_zitv3 s) s.
Proof. apply (proj1 zadd3_closure). Qed.

Theorem zadd3_monotone : forall s t, sle3 s t -> sle3 (add_zitv3 s) (add_zitv3 t).
Proof. apply (proj1 (proj2 zadd3_closure)). Qed.

Theorem zadd3_idempotent : forall s,
  sle3 (add_zitv3 (add_zitv3 s)) (add_zitv3 s) /\ sle3 (add_zitv3 s) (add_zitv3 (add_zitv3 s)).
Proof. apply (proj2 (proj2 zadd3_closure)). Qed.
