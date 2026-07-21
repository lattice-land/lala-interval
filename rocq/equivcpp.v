(** * equivcpp.v : C++-faithful rendering of the infinity-aware helpers.

    The lala C++ code defines extended-integer multiplication compactly as
      imul(a, b) :=
        if a,b both finite         : a * b
        else if a = 0 or b = 0     : 0
        else                       : same_sign(a, b) ? +oo : -oo
      same_sign(x, y) := (x < 0) == (y < 0)
    over a machine type where +oo/-oo are sentinel values.

    [itv.v]'s [imul3] instead spells out all nine constructor pairs, which
    reduces cleanly under [cbn] in the propagator proofs.  Here we give the
    compact rendering [imul3'] (matching the C++ line for line, using the
    [zneg] "< 0" test since [Zinf] is not a single numeric type) and prove it
    is extensionally the SAME function as [imul3]. *)

From Stdlib Require Import ZArith Bool Lia.
From LalaInterval Require Import inf Lemmas itv zdiv.
Open Scope Z_scope.

(* ================================================================== *)
(** ** Inlined from the former old_tdiv.v : the OLD direct truncated-
       division proof (tymin/tymax band solver [ztdiv_pos3] -> [ztdiv4]),
       with its soundness/completeness/closure.  Kept here because the
       equivalence [ztdiv_simpl_equiv_ztdivq] below needs [ztdiv4]s
       verified soundness+completeness.  (old_tdiv.v has been deleted;
       its [tsol] shadows zdiv.vs identical one -- the equivalence proof
       bridges them.) *)
(* ================================================================== *)

Definition idivt3 (n m : Zinf) : Zinf :=
  match m with
  | Pinf | Ninf => Fin 0
  | Fin w => match n with
             | Fin v => Fin (Z.quot v w)
             | Pinf => if 0 <? w then Pinf else Ninf
             | Ninf => if 0 <? w then Ninf else Pinf
             end
  end.

(* negation on Zinf; mirrors the C++ [ineg]. *)
Definition ztdiv_pos3 (s : store3) : store3 :=
  let x := sx3 s in let y := sy3 s in
  let z := Itv3 (zmax (lo3 (sz3 s)) (Fin 1)) (hi3 (sz3 s)) in
  if negb (nonempty3b z) then St3 x y z else
  (* Z: tymin(x.lb, z) <= y.ub *)
  let z :=
    if zpos (lo3 x) then Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (hi3 y) (lo3 x)))
    else Itv3 (zmax (lo3 z) (idivc3 (sadd3 (hi3 y) (-1)) (sadd3 (lo3 x) (-1)))) (hi3 z) in
  (* Z: tymax(x.ub, z) >= y.lb *)
  let z :=
    if zge0 (hi3 x) then
      Itv3 (zmax (lo3 z) (idivc3 (sadd3 (lo3 y) 1) (sadd3 (hi3 x) 1))) (hi3 z)
    else Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (lo3 y) (hi3 x))) in
  if negb (nonempty3b z) then St3 x y z else
  (* Y: hull of [tymin(x.lb, z), tymax(x.ub, z)] over the narrowed z *)
  let y := Itv3
    (zmax (lo3 y)
          (if zpos (lo3 x)
           then zmin (imul3 (lo3 x) (lo3 z)) (imul3 (lo3 x) (hi3 z))
           else zmin (sadd3 (imul3 (sadd3 (lo3 x) (-1)) (lo3 z)) 1)
                     (sadd3 (imul3 (sadd3 (lo3 x) (-1)) (hi3 z)) 1)))
    (zmin (hi3 y)
          (if zge0 (hi3 x)
           then zmax (sadd3 (imul3 (sadd3 (hi3 x) 1) (lo3 z)) (-1))
                     (sadd3 (imul3 (sadd3 (hi3 x) 1) (hi3 z)) (-1))
           else zmax (imul3 (hi3 x) (lo3 z)) (imul3 (hi3 x) (hi3 z)))) in
  if negb (nonempty3b y) then St3 x y z else
  (* X: 4-corner hull of tdiv(y, z) *)
  let x := Itv3
    (zmax (lo3 x) (zmin (zmin (idivt3 (lo3 y) (lo3 z)) (idivt3 (lo3 y) (hi3 z)))
                        (zmin (idivt3 (hi3 y) (lo3 z)) (idivt3 (hi3 y) (hi3 z)))))
    (zmin (hi3 x) (zmax (zmax (idivt3 (lo3 y) (lo3 z)) (idivt3 (lo3 y) (hi3 z)))
                        (zmax (idivt3 (hi3 y) (lo3 z)) (idivt3 (hi3 y) (hi3 z))))) in
  St3 x y z.

(* ------------------------------------------------------------------ *)
(** ** The four propagators (slice decomposition + join)               *)
(* ------------------------------------------------------------------ *)

(* the C++ join block: a failed positive slice is replaced wholesale by the
   negative one; a failed negative slice is dropped; otherwise hull. *)
Definition ztdiv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (ztdiv_pos3 s) (mir_xz (ztdiv_pos3 (mir_xz s))).

(* ------------------------------------------------------------------ *)
(** ** Solutions of the four divisions                                 *)
(* ------------------------------------------------------------------ *)

(* floor: sol = z <> 0 /\ x = y / z (Z.div is the floor division) *)
Definition tsol (x y z : Z) : Prop := z <> 0 /\ x = Z.quot y z.
Lemma quot_neg_eq : forall y z, y < 0 -> 0 < z -> Z.quot y z = - ((- y) / z).
Proof.
  intros y z Hy Hz.
  replace y with (- (- y)) at 1 by lia.
  rewrite Z.quot_opp_l by lia.
  rewrite Z.quot_div_nonneg by lia. reflexivity.
Qed.

Lemma tymin_lb : forall v y z, 0 < z ->
  v <= Z.quot y z -> (if 0 <? v then v*z else (v-1)*z+1) <= y.
Proof.
  intros v y z Hz Hv.
  destruct (Z.ltb_spec 0 v) as [Hvpos|Hvle].
  - (* v>0 : need v*z<=y ; quot>0 => y>0 => quot=y/z *)
    assert (Hy : 0 < y).
    { destruct (Z.le_gt_cases y 0) as [Hyle|Hygt]; [|lia].
      exfalso. destruct (Z.eq_dec y 0) as [->|Hyn].
      - rewrite Z.quot_0_l in Hv; lia.
      - assert (y < 0) by lia.
        rewrite quot_neg_eq in Hv by lia.
        assert (0 <= (- y)/z) by (apply Z.div_pos; lia). lia. }
    rewrite Z.quot_div_nonneg in Hv by lia.
    pose proof (Z.mul_div_le y z ltac:(lia)) as Hmd.
    nia.
  - (* v<=0 : need (v-1)*z+1<=y *)
    destruct (Z.le_gt_cases 0 y) as [Hy|Hy].
    + nia.
    + rewrite quot_neg_eq in Hv by lia.
      pose proof (Z.div_mod (- y) z ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound (- y) z ltac:(lia)) as Hmb.
      nia.
Qed.

Lemma tymax_ub : forall v y z, 0 < z ->
  Z.quot y z <= v -> y <= (if 0 <=? v then (v+1)*z-1 else v*z).
Proof.
  intros v y z Hz Hv.
  destruct (Z.leb_spec 0 v) as [Hvpos|Hvneg].
  - (* v>=0 : need y<=(v+1)*z-1 *)
    destruct (Z.le_gt_cases 0 y) as [Hy|Hy].
    + rewrite Z.quot_div_nonneg in Hv by lia.
      pose proof (Z.div_mod y z ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound y z ltac:(lia)) as Hmb.
      nia.
    + nia.
  - (* v<0 : need y<=v*z ; quot<0 => y<0 *)
    assert (Hy : y < 0).
    { destruct (Z.le_gt_cases y 0) as [Hyle|Hygt].
      - destruct (Z.eq_dec y 0) as [->|Hyn]; [rewrite Z.quot_0_l in Hv; lia| lia].
      - exfalso. rewrite Z.quot_div_nonneg in Hv by lia.
        assert (0 <= y / z) by (apply Z.div_pos; lia). lia. }
    rewrite quot_neg_eq in Hv by lia.
    pose proof (Z.div_mod (- y) z ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (- y) z ltac:(lia)) as Hmb.
    nia.
Qed.

(* ===== truncated-division monotonicity (z>=1) ===== *)
Lemma q_nonpos : forall y z, y <= 0 -> 0 < z -> Z.quot y z <= 0.
Proof.
  intros y z Hy Hz.
  replace y with (- (- y)) by lia. rewrite Z.quot_opp_l by lia.
  pose proof (Z.quot_pos (- y) z ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma q_mono_z_ge0 : forall y z1 z2, 0 <= y -> 0 < z1 -> z1 <= z2 ->
  Z.quot y z2 <= Z.quot y z1.
Proof. intros; apply Z.quot_le_compat_l; lia. Qed.
Lemma q_mono_z_le0 : forall y z1 z2, y <= 0 -> 0 < z1 -> z1 <= z2 ->
  Z.quot y z1 <= Z.quot y z2.
Proof.
  intros y z1 z2 Hy Hz1 Hz2.
  assert (E1: Z.quot y z1 = - Z.quot (-y) z1).
  { replace y with (- - y) at 1 by lia. rewrite Z.quot_opp_l by lia. reflexivity. }
  assert (E2: Z.quot y z2 = - Z.quot (-y) z2).
  { replace y with (- - y) at 1 by lia. rewrite Z.quot_opp_l by lia. reflexivity. }
  rewrite E1, E2.
  pose proof (q_mono_z_ge0 (-y) z1 z2 ltac:(lia) Hz1 Hz2). lia.
Qed.

(* ===== Zinf lattice extras ===== *)
Lemma xlo : forall yb zl zu vy vz,
  zle yb (Fin vy) -> zle (Fin 1) zl -> zle zl (Fin vz) -> zle (Fin vz) zu ->
  zle (zmin (idivt3 yb zl) (idivt3 yb zu)) (Fin (Z.quot vy vz)).
Proof.
  intros yb zl zu vy vz Hyb Hz1 Hzl Hzu.
  destruct zl as [zlv| |]; cbn in Hz1, Hzl; try contradiction.
  destruct yb as [ylv| |]; cbn in Hyb; try contradiction.
  - (* yb = Fin ylv, ylv <= vy ; zl = Fin zlv, 1<=zlv<=vz *)
    assert (Hvz : 0 < vz) by lia.
    assert (Hmy : Z.quot ylv vz <= Z.quot vy vz) by (apply Z.quot_le_mono; lia).
    destruct zu as [zuv| |]; cbn in Hzu; try contradiction.
    + (* zu = Fin zuv, vz<=zuv *)
      cbn.
      assert (Hzb : Z.min (Z.quot ylv zlv) (Z.quot ylv zuv) <= Z.quot ylv vz).
      { destruct (Z.le_gt_cases 0 ylv) as [Hp|Hn].
        - pose proof (q_mono_z_ge0 ylv vz zuv Hp ltac:(lia) ltac:(lia)).
          pose proof (Z.le_min_r (Z.quot ylv zlv) (Z.quot ylv zuv)). lia.
        - pose proof (q_mono_z_le0 ylv zlv vz ltac:(lia) ltac:(lia) ltac:(lia)).
          pose proof (Z.le_min_l (Z.quot ylv zlv) (Z.quot ylv zuv)). lia. }
      lia.
    + (* zu = Pinf : idivt3 (Fin ylv) Pinf = Fin 0 *)
      cbn.
      assert (Hzb : Z.min (Z.quot ylv zlv) 0 <= Z.quot ylv vz).
      { destruct (Z.le_gt_cases 0 ylv) as [Hp|Hn].
        - pose proof (Z.quot_pos ylv vz Hp Hvz).
          pose proof (Z.le_min_r (Z.quot ylv zlv) 0). lia.
        - pose proof (q_mono_z_le0 ylv zlv vz ltac:(lia) ltac:(lia) ltac:(lia)).
          pose proof (Z.le_min_l (Z.quot ylv zlv) 0). lia. }
      lia.
  - (* yb = Ninf : idivt3 Ninf (Fin zlv) = Ninf since zlv>0 *)
    cbn [idivt3]. rewrite (proj2 (Z.ltb_lt 0 zlv) ltac:(lia)).
    destruct zu; cbn; exact I.
Qed.

Lemma xhi : forall yb zl zu vy vz,
  zle (Fin vy) yb -> zle (Fin 1) zl -> zle zl (Fin vz) -> zle (Fin vz) zu ->
  zle (Fin (Z.quot vy vz)) (zmax (idivt3 yb zl) (idivt3 yb zu)).
Proof.
  intros yb zl zu vy vz Hyb Hz1 Hzl Hzu.
  destruct zl as [zlv| |]; cbn in Hz1, Hzl; try contradiction.
  destruct yb as [yuv| |]; cbn in Hyb; try contradiction.
  - assert (Hvz : 0 < vz) by lia.
    assert (Hmy : Z.quot vy vz <= Z.quot yuv vz) by (apply Z.quot_le_mono; lia).
    destruct zu as [zuv| |]; cbn in Hzu; try contradiction.
    + cbn.
      assert (Hzb : Z.quot yuv vz <= Z.max (Z.quot yuv zlv) (Z.quot yuv zuv)).
      { destruct (Z.le_gt_cases 0 yuv) as [Hp|Hn].
        - pose proof (q_mono_z_ge0 yuv zlv vz Hp ltac:(lia) ltac:(lia)).
          pose proof (Z.le_max_l (Z.quot yuv zlv) (Z.quot yuv zuv)). lia.
        - pose proof (q_mono_z_le0 yuv vz zuv ltac:(lia) ltac:(lia) ltac:(lia)).
          pose proof (Z.le_max_r (Z.quot yuv zlv) (Z.quot yuv zuv)). lia. }
      lia.
    + cbn.
      assert (Hzb : Z.quot yuv vz <= Z.max (Z.quot yuv zlv) 0).
      { destruct (Z.le_gt_cases 0 yuv) as [Hp|Hn].
        - pose proof (q_mono_z_ge0 yuv zlv vz Hp ltac:(lia) ltac:(lia)).
          pose proof (Z.le_max_l (Z.quot yuv zlv) 0). lia.
        - pose proof (q_nonpos yuv vz ltac:(lia) Hvz).
          pose proof (Z.le_max_r (Z.quot yuv zlv) 0). lia. }
      lia.
  - cbn [idivt3]. rewrite (proj2 (Z.ltb_lt 0 zlv) ltac:(lia)).
    destruct zu; cbn; exact I.
Qed.

(* ===== single-bound narrowing preserves the true point ===== *)
Lemma z1_pos_ob : forall s vy vz,
  1 <= vz -> zle (lo3 (sx3 s)) (Fin (Z.quot vy vz)) -> zle (Fin vy) (hi3 (sy3 s)) ->
  zpos (lo3 (sx3 s)) = true ->
  zle (Fin vz) (idivf3 (hi3 (sy3 s)) (lo3 (sx3 s))).
Proof.
  intros s vy vz Hvz Hxl Hyu Hzp.
  destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate; try (cbn in Hxl; contradiction).
  (* lo3 x = Fin a, 0 < a *)
  apply Z.ltb_lt in Hzp. cbn in Hxl.
  pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
  rewrite (proj2 (Z.ltb_lt 0 a) Hzp) in Hty. (* tymin = a*vz *)
  destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
  - cbn [idivf3]. cbn. apply F1; lia.
  - cbn [idivf3]. rewrite (proj2 (Z.ltb_lt 0 a) Hzp). exact I.
Qed.

Lemma z1_neg_ob : forall s vy vz,
  1 <= vz -> zle (lo3 (sx3 s)) (Fin (Z.quot vy vz)) -> zle (Fin vy) (hi3 (sy3 s)) ->
  zpos (lo3 (sx3 s)) = false ->
  zle (idivc3 (sadd3 (hi3 (sy3 s)) (-1)) (sadd3 (lo3 (sx3 s)) (-1))) (Fin vz).
Proof.
  intros s vy vz Hvz Hxl Hyu Hzp.
  destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate.
  - (* Fin a, a <= 0 *)
    apply Z.ltb_ge in Hzp. cbn in Hxl.
    pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
    rewrite (proj2 (Z.ltb_ge 0 a) Hzp) in Hty. (* tymin = (a-1)*vz+1 *)
    destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
    + cbn [sadd3 idivc3]. cbn. apply C1; nia.
    + cbn [sadd3 idivc3]. rewrite (proj2 (Z.ltb_ge 0 (a + -1)) ltac:(lia)). exact I.
  - (* Ninf : bound is 0 or 1 <= vz *)
    cbn [sadd3].
    destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
    + cbn [sadd3 idivc3]. destruct (u + -1 <? 0); cbn; lia.
    + cbn [sadd3 idivc3]. cbn; lia.
Qed.

(* Z2: tymax(x.ub,z) >= y.lb  --> refine z *)
Lemma z2_pos_ob : forall s vy vz,
  1 <= vz -> zle (Fin (Z.quot vy vz)) (hi3 (sx3 s)) -> zle (lo3 (sy3 s)) (Fin vy) ->
  zge0 (hi3 (sx3 s)) = true ->
  zle (idivc3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1)) (Fin vz).
Proof.
  intros s vy vz Hvz Hxu Hyl Hzg.
  destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  - (* Fin b, 0 <= b *)
    apply Z.leb_le in Hzg. cbn in Hxu.
    pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
    rewrite (proj2 (Z.leb_le 0 b) Hzg) in Hty. (* tymax = (b+1)*vz-1 *)
    destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
    + cbn [sadd3 idivc3]. cbn. apply CC1; lia.
    + cbn [sadd3 idivc3]. rewrite (proj2 (Z.ltb_lt 0 (b + 1)) ltac:(lia)). exact I.
  - (* Pinf : bound is 0 or 1 <= vz *)
    cbn [sadd3].
    destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
    + cbn [sadd3 idivc3]. destruct (0 <? l + 1); cbn; lia.
    + cbn [sadd3 idivc3]. cbn; lia.
Qed.

Lemma z2_neg_ob : forall s vy vz,
  1 <= vz -> zle (Fin (Z.quot vy vz)) (hi3 (sx3 s)) -> zle (lo3 (sy3 s)) (Fin vy) ->
  zge0 (hi3 (sx3 s)) = false ->
  zle (Fin vz) (idivf3 (lo3 (sy3 s)) (hi3 (sx3 s))).
Proof.
  intros s vy vz Hvz Hxu Hyl Hzg.
  destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  (* Fin b, b < 0 *)
  apply Z.leb_gt in Hzg. cbn in Hxu.
  pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
  rewrite (proj2 (Z.leb_gt 0 b) Hzg) in Hty. (* tymax = b*vz *)
  destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
  - cbn [idivf3]. cbn. apply FN1; lia.
  - cbn [idivf3]. rewrite (proj2 (Z.ltb_ge 0 b) ltac:(lia)). exact I.
Qed.

(* ===== imul3 reductions at infinities (positive z side) ===== *)
Lemma ylo_pos : forall s vy vz iz,
  1 <= vz -> zle (Fin 1) (lo3 iz) -> zle (lo3 iz) (Fin vz) -> zle (Fin vz) (hi3 iz) ->
  zle (lo3 (sx3 s)) (Fin (Z.quot vy vz)) -> zpos (lo3 (sx3 s)) = true ->
  zle (zmin (imul3 (lo3 (sx3 s)) (lo3 iz)) (imul3 (lo3 (sx3 s)) (hi3 iz))) (Fin vy).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxl Hzp.
  destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate; try (cbn in Hxl; contradiction).
  apply Z.ltb_lt in Hzp. cbn in Hxl.
  pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
  rewrite (proj2 (Z.ltb_lt 0 a) Hzp) in Hty.
  destruct (lo3 iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (hi3 iz) as [zu| |]; cbn in Hzu; try contradiction.
  - cbn. pose proof (Z.le_min_l (a*zl) (a*zu)). nia.
  - rewrite imul3_fp by lia. cbn. nia.
Qed.

Lemma ylo_neg : forall s vy vz iz,
  1 <= vz -> zle (Fin 1) (lo3 iz) -> zle (lo3 iz) (Fin vz) -> zle (Fin vz) (hi3 iz) ->
  zle (lo3 (sx3 s)) (Fin (Z.quot vy vz)) -> zpos (lo3 (sx3 s)) = false ->
  zle (zmin (sadd3 (imul3 (sadd3 (lo3 (sx3 s)) (-1)) (lo3 iz)) 1)
            (sadd3 (imul3 (sadd3 (lo3 (sx3 s)) (-1)) (hi3 iz)) 1)) (Fin vy).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxl Hzp.
  destruct (lo3 iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate.
  - (* Fin a, a<=0 *)
    apply Z.ltb_ge in Hzp. cbn in Hxl.
    pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
    rewrite (proj2 (Z.ltb_ge 0 a) Hzp) in Hty. (* (a-1)*vz+1 <= vy *)
    destruct (hi3 iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn [sadd3 imul3]. cbn. pose proof (Z.le_min_r (a + -1 * zl + 1)%Z (a + -1 * zu + 1)%Z). nia.
    + cbn [sadd3]. rewrite imul3_fn by lia. cbn. nia.
  - (* Ninf *)
    cbn [sadd3].
    destruct (hi3 iz) as [zu| |]; cbn in Hzu; try contradiction.
    + rewrite !imul3_ninf_fp by lia. cbn. exact I.
    + rewrite imul3_ninf_fp by lia. cbn. exact I.
Qed.

Lemma yhi_pos : forall s vy vz iz,
  1 <= vz -> zle (Fin 1) (lo3 iz) -> zle (lo3 iz) (Fin vz) -> zle (Fin vz) (hi3 iz) ->
  zle (Fin (Z.quot vy vz)) (hi3 (sx3 s)) -> zge0 (hi3 (sx3 s)) = true ->
  zle (Fin vy) (zmax (sadd3 (imul3 (sadd3 (hi3 (sx3 s)) 1) (lo3 iz)) (-1))
                     (sadd3 (imul3 (sadd3 (hi3 (sx3 s)) 1) (hi3 iz)) (-1))).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxu Hzg.
  destruct (lo3 iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  - (* Fin b, 0<=b *)
    apply Z.leb_le in Hzg. cbn in Hxu.
    pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
    rewrite (proj2 (Z.leb_le 0 b) Hzg) in Hty. (* vy <= (b+1)*vz-1 *)
    destruct (hi3 iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn [sadd3 imul3]. cbn. pose proof (Z.le_max_r (b + 1 * zl + -1)%Z (b + 1 * zu + -1)%Z). nia.
    + cbn [sadd3]. rewrite imul3_fp by lia. cbn. exact I.
  - (* Pinf : zmax collapses to Pinf via the lo-z corner *)
    cbn [sadd3]. rewrite imul3_pinf_fp by lia. cbn. exact I.
Qed.

Lemma yhi_neg : forall s vy vz iz,
  1 <= vz -> zle (Fin 1) (lo3 iz) -> zle (lo3 iz) (Fin vz) -> zle (Fin vz) (hi3 iz) ->
  zle (Fin (Z.quot vy vz)) (hi3 (sx3 s)) -> zge0 (hi3 (sx3 s)) = false ->
  zle (Fin vy) (zmax (imul3 (hi3 (sx3 s)) (lo3 iz)) (imul3 (hi3 (sx3 s)) (hi3 iz))).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxu Hzg.
  destruct (lo3 iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  (* Fin b, b<0 *)
  apply Z.leb_gt in Hzg. cbn in Hxu.
  pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
  rewrite (proj2 (Z.leb_gt 0 b) Hzg) in Hty. (* vy <= b*vz *)
  destruct (hi3 iz) as [zu| |]; cbn in Hzu; try contradiction.
  - cbn. pose proof (Z.le_max_l (b*zl) (b*zu)). nia.
  - rewrite imul3_fn by lia. cbn. nia.
Qed.

(* ===== step combinators for the z narrowings ===== *)
Lemma step_hilo : forall (C:bool) lo hi Bh Bl vz,
  zle lo (Fin vz) -> zle (Fin vz) hi ->
  (C = true -> zle (Fin vz) Bh) -> (C = false -> zle Bl (Fin vz)) ->
  mem3 (if C then Itv3 lo (zmin hi Bh) else Itv3 (zmax lo Bl) hi) vz.
Proof.
  intros C lo hi Bh Bl vz Hlo Hhi HT HF. destruct C.
  - apply mem3_narrow_hi; [exact Hlo|exact Hhi|apply HT;reflexivity].
  - apply mem3_narrow_lo; [exact Hlo|exact Hhi|apply HF;reflexivity].
Qed.

Lemma step_lohi : forall (C:bool) lo hi Bl Bh vz,
  zle lo (Fin vz) -> zle (Fin vz) hi ->
  (C = true -> zle Bl (Fin vz)) -> (C = false -> zle (Fin vz) Bh) ->
  mem3 (if C then Itv3 (zmax lo Bl) hi else Itv3 lo (zmin hi Bh)) vz.
Proof.
  intros C lo hi Bl Bh vz Hlo Hhi HT HF. destruct C.
  - apply mem3_narrow_lo; [exact Hlo|exact Hhi|apply HT;reflexivity].
  - apply mem3_narrow_hi; [exact Hlo|exact Hhi|apply HF;reflexivity].
Qed.

Lemma step_hilo_pos : forall (C:bool) lo hi Bh Bl,
  zle (Fin 1) lo ->
  zle (Fin 1) (lo3 (if C then Itv3 lo (zmin hi Bh) else Itv3 (zmax lo Bl) hi)).
Proof. intros C lo hi Bh Bl H. destruct C; cbn [lo3]; [exact H | eapply zle_trans;[exact H|apply zle_zmax_l]]. Qed.
Lemma step_lohi_pos : forall (C:bool) lo hi Bl Bh,
  zle (Fin 1) lo ->
  zle (Fin 1) (lo3 (if C then Itv3 (zmax lo Bl) hi else Itv3 lo (zmin hi Bh))).
Proof. intros C lo hi Bl Bh H. destruct C; cbn [lo3]; [eapply zle_trans;[exact H|apply zle_zmax_l] | exact H]. Qed.


(* ================================================================== *)
(** Support lemmas for the floored positive-slice soundness proof
    ([fpos_sound]): floor band, divisor monotonicity, corner-hull
    brackets, and the 4-way Z-step (empty branch => no solution) *)
(* ================================================================== *)

(* ===== floor band lemmas (z>0): floor(y/z)>=v <-> y>=v*z ; <=v <-> y<=(v+1)*z-1 ===== *)
Theorem tpos_sound : forall s vx vy vz,
  in_store3 s vx vy vz -> tsol vx vy vz -> 1 <= vz ->
  in_store3 (ztdiv_pos3 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hts Hvz1.
  destruct Hin as (Hmx & Hmy & Hmz).
  destruct Hts as [Hnz Hq]. subst vx.
  destruct Hmx as [Hxl Hxu]; destruct Hmy as [Hyl Hyu]; destruct Hmz as [Hzl0 Hzu0].
  unfold ztdiv_pos3; cbv zeta.
  (* --- z0 --- *)
  match goal with |- context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hmz0l : zle (lo3 z0) (Fin vz)) by (rewrite Hz0; cbn [lo3]; apply zmax_lub; [exact Hzl0 | cbn; lia]).
  assert (Hmz0u : zle (Fin vz) (hi3 z0)) by (rewrite Hz0; cbn [hi3]; exact Hzu0).
  assert (Hlz0 : zle (Fin 1) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_r).
  destruct (negb (nonempty3b z0)) eqn:E0.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj Hyl Hyu) | exact (conj Hmz0l Hmz0u)]]. }
  (* --- z1 --- *)
  match goal with |- context[if zpos (lo3 (sx3 s)) then ?A else ?B] =>
    remember (if zpos (lo3 (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hmz1 : mem3 z1 vz).
  { rewrite Hz1. apply step_hilo.
    - exact Hmz0l.
    - exact Hmz0u.
    - intro Hc. apply (z1_pos_ob s vy vz); [exact Hvz1 | exact Hxl | exact Hyu | exact Hc].
    - intro Hc. apply (z1_neg_ob s vy vz); [exact Hvz1 | exact Hxl | exact Hyu | exact Hc]. }
  assert (Hlz1 : zle (Fin 1) (lo3 z1)) by (rewrite Hz1; apply step_hilo_pos; exact Hlz0).
  destruct Hmz1 as [Hmz1l Hmz1u].
  (* --- z2 --- *)
  match goal with |- context[if zge0 (hi3 (sx3 s)) then ?A else ?B] =>
    remember (if zge0 (hi3 (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hmz2 : mem3 z2 vz).
  { rewrite Hz2. apply step_lohi.
    - exact Hmz1l.
    - exact Hmz1u.
    - intro Hc. apply (z2_pos_ob s vy vz); [exact Hvz1 | exact Hxu | exact Hyl | exact Hc].
    - intro Hc. apply (z2_neg_ob s vy vz); [exact Hvz1 | exact Hxu | exact Hyl | exact Hc]. }
  assert (Hlz2 : zle (Fin 1) (lo3 z2)) by (rewrite Hz2; apply step_lohi_pos; exact Hlz1).
  destruct Hmz2 as [Hmz2l Hmz2u].
  destruct (negb (nonempty3b z2)) eqn:E2.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj Hyl Hyu) | exact (conj Hmz2l Hmz2u)]]. }
  (* --- yF --- *)
  match goal with |- context[nonempty3b ?Y] => remember Y as yF eqn:HyF end.
  assert (Hmy : mem3 yF vy).
  { rewrite HyF. apply mem3_narrow_both.
    - exact Hyl.
    - exact Hyu.
    - destruct (zpos (lo3 (sx3 s))) eqn:Ezp.
      + apply (ylo_pos s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxl|exact Ezp].
      + apply (ylo_neg s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxl|exact Ezp].
    - destruct (zge0 (hi3 (sx3 s))) eqn:Ezg.
      + apply (yhi_pos s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxu|exact Ezg].
      + apply (yhi_neg s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxu|exact Ezg]. }
  destruct Hmy as [HmyL HmyU].
  destruct (negb (nonempty3b yF)) eqn:EY.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj HmyL HmyU) | exact (conj Hmz2l Hmz2u)]]. }
  (* --- final: xF --- *)
  split.
  - apply mem3_narrow_both.
    + exact Hxl.
    + exact Hxu.
    + eapply zle_trans; [apply zmin_zle_l | ].
      apply (xlo (lo3 yF) (lo3 z2) (hi3 z2)); [exact HmyL|exact Hlz2|exact Hmz2l|exact Hmz2u].
    + eapply zle_trans; [ | apply zle_zmax_r ].
      apply (xhi (hi3 yF) (lo3 z2) (hi3 z2)); [exact HmyU|exact Hlz2|exact Hmz2l|exact Hmz2u].
  - split; [exact (conj HmyL HmyU) | exact (conj Hmz2l Hmz2u)].
Qed.


(* ================================================================== *)
(** Support machinery for [tpos_ne_feasible]: the reverse band lemmas,
    the Zinf band bounds, the propagator-reconstruction core
    [zpos3_band], and the finite-witness picker. *)
(* ================================================================== *)

(* ===== reverse band lemmas: band bound on y implies the quotient bound ===== *)
Lemma tymin_lb_rev : forall v y z, 0 < z ->
  (if 0 <? v then v*z else (v-1)*z+1) <= y -> v <= Z.quot y z.
Proof.
  intros v y z Hz H.
  destruct (Z.ltb_spec 0 v) as [Hv|Hv].
  - rewrite Z.quot_div_nonneg by nia.
    apply Z.div_le_lower_bound; [lia | nia].
  - destruct (Z.le_gt_cases 0 y) as [Hy|Hy].
    + rewrite Z.quot_div_nonneg by lia.
      pose proof (Z.div_pos y z Hy Hz). lia.
    + rewrite quot_neg_eq by lia.
      pose proof (Z.div_mod (- y) z ltac:(lia)).
      pose proof (Z.mod_pos_bound (- y) z ltac:(lia)). nia.
Qed.

Lemma tymax_ub_rev : forall v y z, 0 < z ->
  y <= (if 0 <=? v then (v+1)*z-1 else v*z) -> Z.quot y z <= v.
Proof.
  intros v y z Hz H.
  destruct (Z.leb_spec 0 v) as [Hv|Hv].
  - destruct (Z.le_gt_cases 0 y) as [Hy|Hy].
    + rewrite Z.quot_div_nonneg by lia.
      pose proof (Z.div_mod y z ltac:(lia)).
      pose proof (Z.mod_pos_bound y z ltac:(lia)). nia.
    + rewrite quot_neg_eq by lia.
      pose proof (Z.div_pos (- y) z ltac:(lia) Hz). lia.
  - destruct (Z.le_gt_cases 0 y) as [Hy|Hy].
    + (* y>=0 but v<0 and y<=v*z<=0 => y=0-ish; v*z<0 so y<=v*z<0 contradicts y>=0 unless... *)
      assert (v * z < 0) by nia. lia.
    + rewrite quot_neg_eq by lia.
      pose proof (Z.div_mod (- y) z ltac:(lia)).
      pose proof (Z.mod_pos_bound (- y) z ltac:(lia)). nia.
Qed.

(* ===== reverse division helpers (bound on quotient implies the product ineq) ===== *)
Definition tyminZ (xl : Zinf) (vz : Z) : Zinf :=
  match xl with
  | Fin a => Fin (if 0 <? a then a * vz else (a - 1) * vz + 1)
  | Ninf => Ninf
  | Pinf => Pinf
  end.
Definition tymaxZ (xu : Zinf) (vz : Z) : Zinf :=
  match xu with
  | Fin b => Fin (if 0 <=? b then (b + 1) * vz - 1 else b * vz)
  | Pinf => Pinf
  | Ninf => Ninf
  end.

Lemma quot_ge : forall xl vy vz, 1 <= vz ->
  zle (tyminZ xl vz) (Fin vy) -> zle xl (Fin (Z.quot vy vz)).
Proof.
  intros [a| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  apply tymin_lb_rev; [lia | exact H].
Qed.

Lemma quot_le : forall xu vy vz, 1 <= vz ->
  zle (Fin vy) (tymaxZ xu vz) -> zle (Fin (Z.quot vy vz)) xu.
Proof.
  intros [b| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  apply tymax_ub_rev; [lia | exact H].
Qed.

Lemma band_ne : forall xl xu vz, 1 <= vz ->
  zle xl xu -> zle (tyminZ xl vz) (tymaxZ xu vz).
Proof.
  intros [a| |] [b| |] vz Hvz H; cbn in *; try exact I; try contradiction.
  destruct (Z.ltb_spec 0 a); destruct (Z.leb_spec 0 b); nia.
Qed.

(* ===== band-condition extraction from the narrowed divisor bounds ===== *)
Lemma z1band_neg : forall yu vz a, a <= 0 -> yu <> Ninf ->
  zle (idivc3 (sadd3 yu (-1)) (sadd3 (Fin a) (-1))) (Fin vz) ->
  zle (Fin ((a - 1) * vz + 1)) yu.
Proof.
  intros yu vz a Ha Hyn H. cbn [sadd3] in H.
  destruct yu as [u| |]; try congruence.
  - cbn [sadd3 idivc3] in H. cbn in H.
    assert (Hle : (a + -1) * vz <= u + -1) by (apply RC1; [lia | exact H]). cbn. nia.
  - cbn. exact I.
Qed.

Lemma z2band_neg : forall yl vz b, b < 0 -> yl <> Pinf ->
  zle (Fin vz) (idivf3 yl (Fin b)) -> zle yl (Fin (b * vz)).
Proof.
  intros yl vz b Hb Hyp H.
  destruct yl as [l| |]; try congruence.
  - cbn [idivf3] in H. cbn in H.
    assert (Hle : l <= b * vz) by (apply mul_ge_div_neg; [lia | exact H]). cbn. lia.
  - cbn. exact I.
Qed.

(* ===== picking a finite witness in a nonempty Zinf interval ===== *)
Lemma step_hilo_lo : forall (C:bool) lo hi Bh Bl,
  zle lo (lo3 (if C then Itv3 lo (zmin hi Bh) else Itv3 (zmax lo Bl) hi)).
Proof. intros; destruct C; cbn [lo3]; [apply zle_refl | apply zle_zmax_l]. Qed.
Lemma step_hilo_hi : forall (C:bool) lo hi Bh Bl,
  zle (hi3 (if C then Itv3 lo (zmin hi Bh) else Itv3 (zmax lo Bl) hi)) hi.
Proof. intros; destruct C; cbn [hi3]; [apply zmin_zle_l | apply zle_refl]. Qed.
Lemma step_lohi_lo : forall (C:bool) lo hi Bl Bh,
  zle lo (lo3 (if C then Itv3 (zmax lo Bl) hi else Itv3 lo (zmin hi Bh))).
Proof. intros; destruct C; cbn [lo3]; [apply zle_zmax_l | apply zle_refl]. Qed.
Lemma step_lohi_hi : forall (C:bool) lo hi Bl Bh,
  zle (hi3 (if C then Itv3 (zmax lo Bl) hi else Itv3 lo (zmin hi Bh))) hi.
Proof. intros; destruct C; cbn [hi3]; [apply zle_refl | apply zmin_zle_l]. Qed.

Lemma zpos3_band : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (ztdiv_pos3 s) = true ->
  exists vz, 1 <= vz /\ mem3 (sz3 s) vz
    /\ zle (tyminZ (lo3 (sx3 s)) vz) (hi3 (sy3 s))
    /\ zle (lo3 (sy3 s)) (tymaxZ (hi3 (sx3 s)) vz).
Proof.
  intros s Hx Hy Hne.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  unfold ztdiv_pos3 in Hne; cbv zeta in Hne.
  match type of Hne with context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : zle (Fin 1) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_r).
  assert (Hz0hi : hi3 z0 = hi3 (sz3 s)) by (rewrite Hz0; cbn [hi3]; reflexivity).
  assert (Hz0lo : zle (lo3 (sz3 s)) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_l).
  destruct (nonempty3b z0) eqn:E0; cbn [negb] in Hne;
    [ | unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne;
        rewrite E0, !andb_false_r in Hne; discriminate ].
  match type of Hne with context[if zpos (lo3 (sx3 s)) then ?A else ?B] =>
    remember (if zpos (lo3 (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : zle (Fin 1) (lo3 z1)) by (rewrite Hz1; apply step_hilo_pos; exact Hz0l1).
  assert (Hlo01 : zle (lo3 z0) (lo3 z1)) by (rewrite Hz1; apply step_hilo_lo).
  assert (Hhi01 : zle (hi3 z1) (hi3 z0)) by (rewrite Hz1; apply step_hilo_hi).
  match type of Hne with context[if zge0 (hi3 (sx3 s)) then ?A else ?B] =>
    remember (if zge0 (hi3 (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : zle (Fin 1) (lo3 z2)) by (rewrite Hz2; apply step_lohi_pos; exact Hz1l1).
  assert (Hlo12 : zle (lo3 z1) (lo3 z2)) by (rewrite Hz2; apply step_lohi_lo).
  assert (Hhi12 : zle (hi3 z2) (hi3 z1)) by (rewrite Hz2; apply step_lohi_hi).
  destruct (nonempty3b z2) eqn:E2; cbn [negb] in Hne;
    [ | unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne;
        rewrite E2, !andb_false_r in Hne; discriminate ].
  (* reach the final store; we only need E2 : nonempty3b z2 = true *)
  clear Hne.
  (* extract vz = lo3 z2 as a finite value >= 1 *)
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  pose proof (ne_zle _ E2) as Hz2ne.
  destruct (fin_of_ge1 (lo3 z2) Hz2l1 Hz2lp) as [zv [Ez2lo Hvz1]].
  exists zv. split; [exact Hvz1 | ].
  (* mem3 (sz3 s) zv *)
  assert (Hzvhi : zle (Fin zv) (hi3 (sz3 s))).
  { rewrite <- Hz0hi. eapply zle_trans; [ | exact Hhi01].
    eapply zle_trans; [ | exact Hhi12]. rewrite <- Ez2lo. exact Hz2ne. }
  assert (Hzvlo : zle (lo3 (sz3 s)) (Fin zv)).
  { rewrite <- Ez2lo. eapply zle_trans; [exact Hz0lo | ].
    eapply zle_trans; [exact Hlo01 | exact Hlo12]. }
  split; [ split; [exact Hzvlo | exact Hzvhi] | ].
  assert (Hzvhi2 : zle (Fin zv) (hi3 z2)) by (rewrite <- Ez2lo; exact Hz2ne).
  split.
  - (* Z1 band: tyminZ (lo x) zv <= hi y *)
    destruct (lo3 (sx3 s)) as [a| |] eqn:Exl;
      [ | congruence | cbn [tyminZ]; exact I ].
    destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
    + (* a > 0 : zpos true -> z1 hi-narrow *)
      assert (Hzp : zpos (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
      rewrite Hzp in Hz1.
      cbn [tyminZ]. rewrite (proj2 (Z.ltb_lt 0 a) Ha).
      apply (z1band_pos (hi3 (sy3 s)) zv a Ha Hyun).
      eapply zle_trans; [ exact Hzvhi2 | ].
      eapply zle_trans; [ exact Hhi12 | ].
      rewrite Hz1; cbn [hi3]. apply zmin_zle_r.
    + (* a <= 0 : zpos false -> z1 lo-narrow *)
      assert (Hzp : zpos (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
      rewrite Hzp in Hz1.
      cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha).
      apply (z1band_neg (hi3 (sy3 s)) zv a Ha Hyun).
      eapply zle_trans; [ | rewrite <- Ez2lo; exact Hlo12 ].
      rewrite Hz1; cbn [lo3]. apply zle_zmax_r.
  - (* Z2 band: lo y <= tymaxZ (hi x) zv *)
    destruct (hi3 (sx3 s)) as [b| |] eqn:Exu;
      [ | cbn [tymaxZ]; apply zle_Pinf | congruence ].
    destruct (Z.lt_ge_cases 0 b) as [Hb|Hb].
    + (* b > 0 : zge0 true -> z2 lo-narrow *)
      assert (Hzg : zge0 (Fin b) = true) by (cbn; apply Z.leb_le; lia).
      rewrite Hzg in Hz2.
      cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 b) ltac:(lia)).
      apply (z2band_pos (lo3 (sy3 s)) zv b ltac:(lia) Hylp).
      eapply zle_trans; [ | rewrite <- Ez2lo; apply zle_refl ].
      rewrite Hz2; cbn [lo3]. apply zle_zmax_r.
    + (* b <= 0 : split zge0 on b = 0 vs b < 0 *)
      destruct (Z.eq_dec b 0) as [->|Hbn].
      * (* b = 0 : zge0 true -> lo-narrow *)
        assert (Hzg : zge0 (Fin 0) = true) by (cbn; reflexivity).
        rewrite Hzg in Hz2.
        cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 0) ltac:(lia)).
        apply (z2band_pos (lo3 (sy3 s)) zv 0 ltac:(lia) Hylp).
        eapply zle_trans; [ | rewrite <- Ez2lo; apply zle_refl ].
        rewrite Hz2; cbn [lo3]. apply zle_zmax_r.
      * (* b < 0 : zge0 false -> hi-narrow *)
        assert (Hzg : zge0 (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
        rewrite Hzg in Hz2.
        cbn [tymaxZ]. rewrite (proj2 (Z.leb_gt 0 b) ltac:(lia)).
        apply (z2band_neg (lo3 (sy3 s)) zv b ltac:(lia) Hylp).
        eapply zle_trans; [ exact Hzvhi2 | ].
        rewrite Hz2; cbn [hi3]. apply zmin_zle_r.
Qed.

(* ===== non-Pinf/non-Ninf preservation for the witness interval ===== *)
Lemma tyminZ_not_Pinf : forall xl vz, xl <> Pinf -> tyminZ xl vz <> Pinf.
Proof. intros [a| |] vz H; cbn; congruence. Qed.
Lemma tymaxZ_not_Ninf : forall xu vz, xu <> Ninf -> tymaxZ xu vz <> Ninf.
Proof. intros [b| |] vz H; cbn; congruence. Qed.


Theorem tpos_ne_feasible : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (ztdiv_pos3 s) = true -> slice_feasible tsol s.
Proof.
  intros s Hx Hy Hne.
  destruct (zpos3_band s Hx Hy Hne) as [vz [Hvz1 [Hmz [Hb1 Hb2]]]].
  pose proof (ne_zle _ Hx) as Hxle.
  pose proof (ne_zle _ Hy) as Hyle.
  pose proof (band_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz Hvz1 Hxle) as Hbn.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  set (L := zmax (tyminZ (lo3 (sx3 s)) vz) (lo3 (sy3 s))).
  set (U := zmin (tymaxZ (hi3 (sx3 s)) vz) (hi3 (sy3 s))).
  assert (HLU : zle L U).
  { unfold L, U. apply zle_zmin_glb.
    - apply zmax_lub; [exact Hbn | exact Hb2].
    - apply zmax_lub; [exact Hb1 | exact Hyle]. }
  assert (HLp : L <> Pinf)
    by (unfold L; apply zmax_not_Pinf; [apply tyminZ_not_Pinf; exact Hxlp | exact Hylp]).
  assert (HUn : U <> Ninf)
    by (unfold U; apply zmin_not_Ninf; [apply tymaxZ_not_Ninf; exact Hxun | exact Hyun]).
  destruct (pickf_mem L U HLU HLp HUn) as [HLvy HvyU].
  unfold L in HLvy. unfold U in HvyU.
  set (vy := pickf L U) in *.
  exists (Z.quot vy vz), vy, vz.
  split.
  - split; [ | split ].
    + split.
      * apply quot_ge; [exact Hvz1 | eapply zle_trans; [apply zle_zmax_l | exact HLvy]].
      * apply quot_le; [exact Hvz1 | eapply zle_trans; [exact HvyU | apply zmin_zle_l]].
    + split.
      * eapply zle_trans; [apply zle_zmax_r | exact HLvy].
      * eapply zle_trans; [exact HvyU | apply zmin_zle_r].
    + exact Hmz.
  - split; [ split; [lia | reflexivity] | exact Hvz1 ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Soundness                                                        *)
(* ------------------------------------------------------------------ *)

(* ================================================================== *)
(** Support lemmas for [ztdiv4_soundness]: mirroring, non-emptiness,
    and the bottom-absorbing join *)
(* ================================================================== *)

(* ---- mirroring on membership ---- *)
Theorem ztdiv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> tsol vx vy vz -> in_store3 (ztdiv4 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hts.
  assert (Hne : ne_store3 s = true) by (eapply ne_store3_true; exact Hin).
  unfold ztdiv4. rewrite Hne. cbn [negb].
  destruct Hts as [Hnz Hq].
  destruct (Z.lt_total vz 0) as [Hzneg | [Hz0 | Hzpos]].
  - (* vz <= -1 : negative slice via mirror *)
    apply in_join4_r.
    assert (Hmir : in_store3 (mir_xz s) (- vx) vy (- vz)) by (apply in_mir_xz; exact Hin).
    assert (Htmir : tsol (- vx) vy (- vz)).
    { split; [lia | ]. rewrite Hq. rewrite Z.quot_opp_r by lia. reflexivity. }
    pose proof (tpos_sound (mir_xz s) (- vx) vy (- vz) Hmir Htmir ltac:(lia)) as Hp.
    pose proof (in_mir_xz (ztdiv_pos3 (mir_xz s)) (- vx) vy (- vz) Hp) as Hback.
    rewrite !Z.opp_involutive in Hback. exact Hback.
  - exfalso; apply Hnz; exact Hz0.
  - (* vz >= 1 : positive slice directly *)
    apply in_join4_l.
    apply tpos_sound; [exact Hin | split; [exact Hnz | exact Hq] | lia].
Qed.

Lemma tsol_mir : forall vx vy vz, tsol vx vy vz -> tsol (- vx) vy (- vz).
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  rewrite Z.quot_opp_r by lia. rewrite Hq. reflexivity.
Qed.

Lemma wit_in_t : forall s t vz vy,
  slice_contains tsol s t -> 1 <= vz -> mem3 (sz3 s) vz -> mem3 (sy3 s) vy ->
  zle (tyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (tymaxZ (hi3 (sx3 s)) vz) ->
  mem3 (sx3 t) (Z.quot vy vz) /\ mem3 (sy3 t) vy /\ mem3 (sz3 t) vz.
Proof.
  intros s t vz vy Hct Hvz1 Hmz Hmy Hb1 Hb2.
  assert (Hin : in_store3 s (Z.quot vy vz) vy vz).
  { split; [ split | split; [exact Hmy | exact Hmz]].
    - apply quot_ge; [exact Hvz1 | exact Hb1].
    - apply quot_le; [exact Hvz1 | exact Hb2]. }
  assert (Hsol : tsol (Z.quot vy vz) vy vz) by (split; [lia | reflexivity]).
  exact (Hct _ _ _ Hin Hsol Hvz1).
Qed.

Lemma attain_vx : forall xl xu vz v, 0 < vz -> zle xl (Fin v) -> zle (Fin v) xu ->
  zle (tyminZ xl vz) (Fin (if 0 <? v then v * vz else (v - 1) * vz + 1)) /\
  zle (Fin (if 0 <? v then v * vz else (v - 1) * vz + 1)) (tymaxZ xu vz) /\
  Z.quot (if 0 <? v then v * vz else (v - 1) * vz + 1) vz = v.
Proof.
  intros xl xu vz v Hvz Hxl Hxu.
  set (vy := if 0 <? v then v * vz else (v - 1) * vz + 1).
  assert (Hq : Z.quot vy vz = v).
  { assert (Hge : v <= Z.quot vy vz) by (apply (tymin_lb_rev v vy vz Hvz); unfold vy; lia).
    assert (Hle : Z.quot vy vz <= v).
    { apply (tymax_ub_rev v vy vz Hvz). unfold vy.
      destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec 0 v); nia. }
    lia. }
  split; [ | split; [ | exact Hq ]].
  - destruct xl as [a| |]; cbn [tyminZ]; [ | cbn in Hxl; contradiction | exact I ].
    cbn in Hxl. cbn. unfold vy.
    destruct (Z.ltb_spec 0 a); destruct (Z.ltb_spec 0 v); nia.
  - destruct xu as [b| |]; cbn [tymaxZ]; [ | exact I | cbn in Hxu; contradiction ].
    cbn in Hxu. cbn. unfold vy.
    destruct (Z.leb_spec 0 b); destruct (Z.ltb_spec 0 v); nia.
Qed.

(* Mirror of attain_vx: vy = tymax-numerator(v,vz) is in the band, quotient exactly v. *)
Lemma attain_vx_hi : forall xl xu vz v, 0 < vz -> zle xl (Fin v) -> zle (Fin v) xu ->
  zle (tyminZ xl vz) (Fin (if 0 <=? v then (v + 1) * vz - 1 else v * vz)) /\
  zle (Fin (if 0 <=? v then (v + 1) * vz - 1 else v * vz)) (tymaxZ xu vz) /\
  Z.quot (if 0 <=? v then (v + 1) * vz - 1 else v * vz) vz = v.
Proof.
  intros xl xu vz v Hvz Hxl Hxu.
  set (vy := if 0 <=? v then (v + 1) * vz - 1 else v * vz).
  assert (Hq : Z.quot vy vz = v).
  { assert (Hle : Z.quot vy vz <= v) by (apply (tymax_ub_rev v vy vz Hvz); unfold vy; lia).
    assert (Hge : v <= Z.quot vy vz).
    { apply (tymin_lb_rev v vy vz Hvz). unfold vy.
      destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec 0 v); nia. }
    lia. }
  split; [ | split; [ | exact Hq ]].
  - destruct xl as [a| |]; cbn [tyminZ]; [ | cbn in Hxl; contradiction | exact I ].
    cbn in Hxl. cbn. unfold vy.
    destruct (Z.ltb_spec 0 a); destruct (Z.leb_spec 0 v); nia.
  - destruct xu as [b| |]; cbn [tymaxZ]; [ | exact I | cbn in Hxu; contradiction ].
    cbn in Hxu. cbn. unfold vy.
    destruct (Z.leb_spec 0 b); destruct (Z.leb_spec 0 v); nia.
Qed.

(* idivt3 is monotone in the numerator for a positive (finite) divisor. *)
Lemma idivt3_mono_pos : forall n1 n2 w, zle n1 n2 -> 0 < w ->
  zle (idivt3 n1 (Fin w)) (idivt3 n2 (Fin w)).
Proof.
  intros [a| |] [b| |] w Hn Hw; cbn [idivt3] in *;
    try rewrite (proj2 (Z.ltb_lt 0 w) Hw); cbn in *;
    try exact I; try contradiction.
  apply Z.quot_le_mono; lia.
Qed.

Theorem tpos_best : forall s, slice_feasible tsol s ->
  forall t, slice_contains tsol s t -> sle3 (ztdiv_pos3 s) t.
Proof.
  intros s Hfeas t Hct.
  destruct Hfeas as (fx & fy & fz & Hfin & Hfts & Hfz1).
  assert (HneO : ne_store3 (ztdiv_pos3 s) = true).
  { eapply ne_store3_true. apply tpos_sound; [exact Hfin | exact Hfts | exact Hfz1]. }
  destruct Hfin as (Hfxm & Hfym & Hfzm).
  assert (Hx : nonempty3b (sx3 s) = true) by (eapply nonempty3b_true; exact Hfxm).
  assert (Hy : nonempty3b (sy3 s) = true) by (eapply nonempty3b_true; exact Hfym).
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  pose proof (ne_zle _ Hx) as Hxle.
  pose proof (ne_zle _ Hy) as Hyle.
  unfold ztdiv_pos3 in HneO |- *; cbv zeta in HneO |- *.
  match goal with |- context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : zle (Fin 1) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_r).
  assert (Hz0hi : hi3 z0 = hi3 (sz3 s)) by (rewrite Hz0; cbn [hi3]; reflexivity).
  assert (Hz0lo : zle (lo3 (sz3 s)) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_l).
  destruct (nonempty3b z0) eqn:E0; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite E0, !andb_false_r in HneO; discriminate ].
  match goal with |- context[if zpos (lo3 (sx3 s)) then ?A else ?B] =>
    remember (if zpos (lo3 (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : zle (Fin 1) (lo3 z1)) by (rewrite Hz1; apply step_hilo_pos; exact Hz0l1).
  assert (Hlo01 : zle (lo3 z0) (lo3 z1)) by (rewrite Hz1; apply step_hilo_lo).
  assert (Hhi01 : zle (hi3 z1) (hi3 z0)) by (rewrite Hz1; apply step_hilo_hi).
  match goal with |- context[if zge0 (hi3 (sx3 s)) then ?A else ?B] =>
    remember (if zge0 (hi3 (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : zle (Fin 1) (lo3 z2)) by (rewrite Hz2; apply step_lohi_pos; exact Hz1l1).
  assert (Hlo12 : zle (lo3 z1) (lo3 z2)) by (rewrite Hz2; apply step_lohi_lo).
  assert (Hhi12 : zle (hi3 z2) (hi3 z1)) by (rewrite Hz2; apply step_lohi_hi).
  destruct (nonempty3b z2) eqn:E2; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite E2, !andb_false_r in HneO; discriminate ].
  match goal with |- context[nonempty3b ?Y] => remember Y as yF eqn:HyF end.
  destruct (nonempty3b yF) eqn:EY; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite EY, !andb_false_r in HneO; discriminate ].
  assert (Hband : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    zle (tyminZ (lo3 (sx3 s)) vz) (hi3 (sy3 s)) /\ zle (lo3 (sy3 s)) (tymaxZ (hi3 (sx3 s)) vz)).
  { intros vz Hvlo Hvhi. split.
    - destruct (lo3 (sx3 s)) as [a| |] eqn:Exl; [ | congruence | cbn [tyminZ]; exact I ].
      destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
      + assert (Hzp : zpos (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
        rewrite Hzp in Hz1. cbn [tyminZ]. rewrite (proj2 (Z.ltb_lt 0 a) Ha).
        apply (z1band_pos (hi3 (sy3 s)) vz a Ha Hyun).
        eapply zle_trans; [ exact Hvhi | ]. eapply zle_trans; [ exact Hhi12 | ].
        rewrite Hz1; cbn [hi3]. apply zmin_zle_r.
      + assert (Hzp : zpos (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
        rewrite Hzp in Hz1. cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha).
        apply (z1band_neg (hi3 (sy3 s)) vz a Ha Hyun).
        eapply zle_trans; [ | eapply zle_trans; [ exact Hlo12 | exact Hvlo ] ].
        rewrite Hz1; cbn [lo3]. apply zle_zmax_r.
    - destruct (hi3 (sx3 s)) as [b| |] eqn:Exu; [ | cbn [tymaxZ]; apply zle_Pinf | congruence ].
      destruct (Z.lt_ge_cases 0 b) as [Hb|Hb].
      + assert (Hzg : zge0 (Fin b) = true) by (cbn; apply Z.leb_le; lia).
        rewrite Hzg in Hz2. cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 b) ltac:(lia)).
        apply (z2band_pos (lo3 (sy3 s)) vz b ltac:(lia) Hylp).
        eapply zle_trans; [ | exact Hvlo ]. rewrite Hz2; cbn [lo3]. apply zle_zmax_r.
      + destruct (Z.eq_dec b 0) as [->|Hbn].
        * assert (Hzg : zge0 (Fin 0) = true) by (cbn; reflexivity).
          rewrite Hzg in Hz2. cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 0) ltac:(lia)).
          apply (z2band_pos (lo3 (sy3 s)) vz 0 ltac:(lia) Hylp).
          eapply zle_trans; [ | exact Hvlo ]. rewrite Hz2; cbn [lo3]. apply zle_zmax_r.
        * assert (Hzg : zge0 (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
          rewrite Hzg in Hz2. cbn [tymaxZ]. rewrite (proj2 (Z.leb_gt 0 b) ltac:(lia)).
          apply (z2band_neg (lo3 (sy3 s)) vz b ltac:(lia) Hylp).
          eapply zle_trans; [ exact Hvhi | ].
          rewrite Hz2; cbn [hi3]. apply zmin_zle_r. }
  assert (Hmemz : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) -> mem3 (sz3 s) vz).
  { intros vz Hvlo Hvhi. unfold mem3. split.
    - eapply zle_trans; [exact Hz0lo | ]. eapply zle_trans; [exact Hlo01 | ].
      eapply zle_trans; [exact Hlo12 | exact Hvlo].
    - rewrite <- Hz0hi. eapply zle_trans; [exact Hvhi | ].
      eapply zle_trans; [exact Hhi12 | exact Hhi01]. }
  assert (Hv1 : forall vz, zle (lo3 z2) (Fin vz) -> 1 <= vz).
  { intros vz Hvlo. assert (HH : zle (Fin 1) (Fin vz)) by (eapply zle_trans; [exact Hz2l1 | exact Hvlo]).
    cbn in HH. lia. }
  assert (Hwit : forall vz vy, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    mem3 (sy3 s) vy -> zle (tyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (tymaxZ (hi3 (sx3 s)) vz) ->
    mem3 (sx3 t) (Z.quot vy vz) /\ mem3 (sy3 t) vy /\ mem3 (sz3 t) vz).
  { intros vz vy Hvlo Hvhi Hmy Hby1 Hby2.
    apply (wit_in_t s t vz vy Hct (Hv1 vz Hvlo) (Hmemz vz Hvlo Hvhi) Hmy Hby1 Hby2). }
  assert (Hpickvy : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    exists vy, mem3 (sy3 s) vy /\ zle (tyminZ (lo3 (sx3 s)) vz) (Fin vy) /\ zle (Fin vy) (tymaxZ (hi3 (sx3 s)) vz)).
  { intros vz Hvlo Hvhi.
    destruct (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (band_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    set (L := zmax (tyminZ (lo3 (sx3 s)) vz) (lo3 (sy3 s))).
    set (U := zmin (tymaxZ (hi3 (sx3 s)) vz) (hi3 (sy3 s))).
    assert (HLU : zle L U).
    { unfold L, U. apply zle_zmin_glb.
      - apply zmax_lub; [exact Hbn | exact Hb2].
      - apply zmax_lub; [exact Hb1 | exact Hyle]. }
    assert (HLp : L <> Pinf) by (unfold L; apply zmax_not_Pinf; [apply tyminZ_not_Pinf; exact Hxlp | exact Hylp]).
    assert (HUn : U <> Ninf) by (unfold U; apply zmin_not_Ninf; [apply tymaxZ_not_Ninf; exact Hxun | exact Hyun]).
    destruct (pickf_mem L U HLU HLp HUn) as [HLvy HvyU].
    unfold L in HLvy. unfold U in HvyU.
    exists (pickf L U). split; [ | split].
    - split; [ eapply zle_trans; [apply zle_zmax_r | exact HLvy] | eapply zle_trans; [exact HvyU | apply zmin_zle_r] ].
    - eapply zle_trans; [apply zle_zmax_l | exact HLvy].
    - eapply zle_trans; [exact HvyU | apply zmin_zle_l]. }
  assert (Hft : in_store3 t fx fy fz)
    by (apply Hct; [split; [exact Hfxm | split; [exact Hfym | exact Hfzm]] | exact Hfts | exact Hfz1]).
  destruct Hft as (Hftx & Hfty & Hftz).
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  pose proof (ne_zle _ E2) as Hz2ne.
  destruct (fin_of_ge1 (lo3 z2) Hz2l1 Hz2lp) as [zlo2 [Hzlo2 Hzlo21]].
  assert (Hzlo2lo : zle (lo3 z2) (Fin zlo2)) by (rewrite Hzlo2; apply zle_refl).
  assert (Hzlo2hi : zle (Fin zlo2) (hi3 z2)) by (rewrite <- Hzlo2; exact Hz2ne).
  assert (Hatt : forall vz vy, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    zle (lo3 (sy3 s)) (Fin vy) -> zle (Fin vy) (hi3 (sy3 s)) ->
    zle (tyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (tymaxZ (hi3 (sx3 s)) vz) ->
    zle (lo3 (sy3 t)) (Fin vy) /\ zle (Fin vy) (hi3 (sy3 t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (_ & Hmyt & _).
    split; [apply (mem3_lo _ _ Hmyt) | apply (mem3_hi _ _ Hmyt)]. }
  assert (Hattx : forall vz vy, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    zle (lo3 (sy3 s)) (Fin vy) -> zle (Fin vy) (hi3 (sy3 s)) ->
    zle (tyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (tymaxZ (hi3 (sx3 s)) vz) ->
    zle (lo3 (sx3 t)) (Fin (Z.quot vy vz)) /\ zle (Fin (Z.quot vy vz)) (hi3 (sx3 t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (Hmxt & _ & _).
    split; [apply (mem3_lo _ _ Hmxt) | apply (mem3_hi _ _ Hmxt)]. }
  pose proof (ne_zle _ EY) as Hyfne.
  assert (Hyfyl : zle (lo3 (sy3 s)) (lo3 yF)) by (rewrite HyF; cbn [lo3]; apply zle_zmax_l).
  assert (Hyfyh : zle (hi3 yF) (hi3 (sy3 s))) by (rewrite HyF; cbn [hi3]; apply zmin_zle_l).
  assert (Hyflo_hi : zle (lo3 yF) (hi3 (sy3 s))) by (eapply zle_trans; [exact Hyfne | exact Hyfyh]).
  assert (Hyfhi_lo : zle (lo3 (sy3 s)) (hi3 yF)) by (eapply zle_trans; [exact Hyfyl | exact Hyfne]).
  apply sle3_intro; cbn [sx3 sy3 sz3].
  - (* ===== X-COMPONENT (goal 1) ===== *)
    assert (Hlyf : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
      zle (lo3 yF) (tymaxZ (hi3 (sx3 s)) vz)).
    { intros vz Hvlo Hvhi.
      pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
      pose proof (band_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
      assert (Hvzge : zlo2 <= vz) by (pose proof Hvlo as HH; rewrite Hzlo2 in HH; cbn in HH; lia).
      rewrite HyF; cbn [lo3]. apply zmax_lub; [exact Hb2 | ].
      eapply zle_trans; [ | exact Hbn ].
      destruct (lo3 (sx3 s)) as [a| |] eqn:Exl.
      - destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
        + assert (Hzp : zpos (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
          rewrite Hzp, Hzlo2. cbn [tyminZ]. rewrite (proj2 (Z.ltb_lt 0 a) Ha). cbn [imul3].
          eapply zle_trans; [ apply zmin_zle_l | cbn; nia ].
        + assert (Hzp : zpos (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
          rewrite Hzp. cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha).
          destruct (hi3 z2) as [zh| |] eqn:Eh.
          * assert (Hvzle : vz <= zh) by (pose proof Hvhi as HH; cbn in HH; lia).
            rewrite Hzlo2. cbn [sadd3 imul3]. eapply zle_trans; [ apply zmin_zle_r | cbn; nia ].
          * cbn [sadd3]. rewrite imul3_fn by lia. cbn.
            eapply zle_trans; [ apply zmin_zle_r | cbn; exact I ].
          * congruence.
      - cbn [tyminZ]. apply zle_Pinf.
      - cbn [tyminZ zpos]. rewrite Hzlo2; cbn [sadd3]; rewrite imul3_ninf_fp by lia; cbn; exact I. }
    assert (Hbf : forall X a, zleb (Fin a) X = false -> zle X (Fin (a - 1))).
    { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | discriminate | exact I ]. }
  apply ile3_intro; cbn [lo3 hi3].
    { (* --- x-lower --- *)
      assert (Hcx : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
        forall ylv, lo3 yF = Fin ylv -> zle (lo3 (sx3 s)) (Fin (Z.quot ylv vz)) ->
        zle (lo3 (sx3 t)) (Fin (Z.quot ylv vz))).
      { intros vz Hvlo Hvhi ylv Eyl Hxc.
        assert (Hbl : zle (tyminZ (lo3 (sx3 s)) vz) (Fin ylv)).
        { destruct (lo3 (sx3 s)) as [a| |] eqn:Exl; cbn [tyminZ].
          - cbn in Hxc. cbn. apply (tymin_lb a ylv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
          - cbn in Hxc. contradiction.
          - exact I. }
        assert (Hbu : zle (Fin ylv) (tymaxZ (hi3 (sx3 s)) vz)) by (rewrite <- Eyl; apply (Hlyf vz Hvlo Hvhi)).
        assert (Hy1 : zle (lo3 (sy3 s)) (Fin ylv)) by (rewrite <- Eyl; exact Hyfyl).
        assert (Hy2 : zle (Fin ylv) (hi3 (sy3 s))) by (rewrite <- Eyl; exact Hyflo_hi).
        destruct (Hattx vz ylv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [HH _]. exact HH. }
      destruct (zleb (lo3 (sx3 s)) (zmin (zmin (idivt3 (lo3 yF) (lo3 z2)) (idivt3 (lo3 yF) (hi3 z2)))
         (zmin (idivt3 (hi3 yF) (lo3 z2)) (idivt3 (hi3 yF) (hi3 z2))))) eqn:Hclip.
      - apply zleb_zle in Hclip.
        eapply zle_trans; [ | apply zle_zmax_r ].
        destruct (lo3 yF) as [ylv| |] eqn:Eyl.
        + assert (Hcll : zle (lo3 (sx3 s)) (idivt3 (Fin ylv) (lo3 z2))).
          { eapply zle_trans; [exact Hclip | ]. eapply zle_trans; [apply zmin_zle_l | apply zmin_zle_l]. }
          assert (Hclh : zle (lo3 (sx3 s)) (idivt3 (Fin ylv) (hi3 z2))).
          { eapply zle_trans; [exact Hclip | ]. eapply zle_trans; [apply zmin_zle_l | apply zmin_zle_r]. }
          assert (HA : zle (lo3 (sx3 t)) (zmin (idivt3 (Fin ylv) (lo3 z2)) (idivt3 (Fin ylv) (hi3 z2)))).
          { apply zle_zmin_glb.
            - rewrite Hzlo2 in Hcll |- *. cbn [idivt3] in Hcll |- *. apply (Hcx zlo2 Hzlo2lo Hzlo2hi ylv eq_refl Hcll).
            - destruct (hi3 z2) as [zh| |] eqn:Eh.
              + cbn [idivt3] in Hclh |- *. apply (Hcx zh Hz2ne (zle_refl _) ylv eq_refl Hclh).
              + cbn [idivt3] in Hclh |- *.
                assert (Hq0 : Z.quot ylv (Z.max zlo2 (Z.abs ylv + 1)) = 0).
                { destruct (Z.le_gt_cases 0 ylv) as [Hp|Hn].
                  - apply Z.quot_small. lia.
                  - replace ylv with (- (- ylv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                rewrite <- Hq0. apply (Hcx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _) ylv eq_refl).
                rewrite Hq0. exact Hclh.
              + congruence. }
          apply zle_zmin_glb; [exact HA | ].
          eapply zle_trans; [exact HA | ].
          apply zle_zmin_glb.
          * eapply zle_trans; [apply zmin_zle_l | rewrite Hzlo2; apply idivt3_mono_pos; [exact Hyfne | lia] ].
          * eapply zle_trans; [apply zmin_zle_r | ].
            destruct (hi3 z2) as [zh| |] eqn:Eh; [ apply idivt3_mono_pos; [exact Hyfne | ] | apply zle_refl | congruence ].
            pose proof Hzlo2hi as HH; cbn in HH; lia.
        + pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
        + assert (En : idivt3 Ninf (Fin zlo2) = Ninf) by (cbn [idivt3]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
          rewrite Hzlo2, En. cbn [zmin].
          assert (Hxn : lo3 (sx3 s) = Ninf).
          { pose proof Hclip as HC. rewrite Hzlo2, En in HC. cbn [zmin] in HC. destruct (lo3 (sx3 s)) eqn:E; try reflexivity; cbn in HC; contradiction. }
          assert (Hyn : lo3 (sy3 s) = Ninf).
          { pose proof Hyfyl as HH. destruct (lo3 (sy3 s)) eqn:E; try reflexivity; cbn in HH; contradiction. }
          destruct (lo3 (sx3 t)) as [M| |] eqn:EtL; [ | | exact I ].
          2:{ exfalso. pose proof (mem3_lo (sx3 t) fx Hftx) as HH. rewrite EtL in HH. cbn in HH. exact HH. }
          exfalso.
          destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy0 [Hmy0 [Hby1 Hby2]]].
          set (vy := Z.min vy0 ((M-1) * zlo2)).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [rewrite Hyn; exact I | eapply zle_trans; [ | apply (mem3_hi _ _ Hmy0)]; cbn; unfold vy; lia]. }
          assert (Hbl : zle (tyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (rewrite Hxn; cbn; exact I).
          assert (Hbu : zle (Fin vy) (tymaxZ (hi3 (sx3 s)) zlo2)) by (eapply zle_trans; [ | exact Hby2]; cbn; unfold vy; lia).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
          pose proof (mem3_lo (sx3 t) _ Hmxt) as HH. rewrite EtL in HH. cbn in HH.
          assert (Hqle : Z.quot vy zlo2 <= Z.quot ((M-1) * zlo2) zlo2) by (apply Z.quot_le_mono; [lia | unfold vy; lia]).
          rewrite Z.quot_mul in Hqle by lia. lia.
      - eapply zle_trans; [ | apply zle_zmax_l ].
        destruct (lo3 (sx3 s)) as [xl| |] eqn:Exl; [ | congruence | cbn [zleb] in Hclip; discriminate ].
        assert (Hclipx : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
          zle (idivt3 (lo3 yF) (Fin vz)) (Fin (xl - 1)) -> zle (lo3 (sx3 t)) (Fin xl)).
        { intros vz Hvlo Hvhi Hcorner.
          pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
          destruct (attain_vx (Fin xl) (hi3 (sx3 s)) vz xl ltac:(pose proof (Hv1 vz Hvlo); lia) (zle_refl _) Hxle) as (Hbl & Hbu & Hqeq).
          set (vy := if 0 <? xl then xl * vz else (xl - 1) * vz + 1) in *.
          assert (Hvyhi : zle (Fin vy) (hi3 (sy3 s))) by (unfold vy; cbn [tyminZ] in Hb1; exact Hb1).
          assert (Hvylo : zle (lo3 (sy3 s)) (Fin vy)).
          { eapply zle_trans; [exact Hyfyl | ].
            destruct (lo3 yF) as [ylv| |] eqn:Eyl.
            - cbn [idivt3] in Hcorner. cbn in Hcorner. cbn.
              destruct (Z.lt_ge_cases ylv vy) as [H|H]; [lia | exfalso].
              pose proof (Z.quot_le_mono vy ylv vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
            - pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
            - exact I. }
          destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [HH _]. rewrite Hqeq in HH. exact HH. }
        destruct (zleb (Fin xl) (idivt3 (lo3 yF) (lo3 z2))) eqn:Ell.
        + destruct (hi3 z2) as [zh| |] eqn:Eh.
          * apply (Hclipx zh Hz2ne (zle_refl _)).
            destruct (zleb (Fin xl) (idivt3 (lo3 yF) (Fin zh))) eqn:Elh.
            -- exfalso. apply zleb_zle in Ell, Elh.
               assert (Hge : zle (Fin xl) (zmin (zmin (idivt3 (lo3 yF) (lo3 z2)) (idivt3 (lo3 yF) (Fin zh)))
                 (zmin (idivt3 (hi3 yF) (lo3 z2)) (idivt3 (hi3 yF) (Fin zh))))).
               { apply zle_zmin_glb; apply zle_zmin_glb; try assumption.
                 - eapply zle_trans; [exact Ell | rewrite Hzlo2; apply idivt3_mono_pos; [exact Hyfne | lia] ].
                 - eapply zle_trans; [exact Elh | apply idivt3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia] ]. }
               apply zleb_zle in Hge. rewrite Hge in Hclip. discriminate.
            -- apply Hbf. exact Elh.
          * destruct (Z.le_gt_cases xl 0) as [Hxl0|Hxl0].
            -- exfalso. apply zleb_zle in Ell.
               assert (Hge : zle (Fin xl) (zmin (zmin (idivt3 (lo3 yF) (lo3 z2)) (idivt3 (lo3 yF) Pinf))
                 (zmin (idivt3 (hi3 yF) (lo3 z2)) (idivt3 (hi3 yF) Pinf)))).
               { apply zle_zmin_glb; apply zle_zmin_glb.
                 - exact Ell.
                 - cbn [idivt3]. cbn. lia.
                 - eapply zle_trans; [exact Ell | rewrite Hzlo2; apply idivt3_mono_pos; [exact Hyfne | lia] ].
                 - cbn [idivt3]. cbn. lia. }
               apply zleb_zle in Hge. rewrite Hge in Hclip. discriminate.
            -- destruct (lo3 yF) as [ylv| |] eqn:Eyl.
               ++ apply (Hclipx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                  cbn [idivt3].
                  assert (Hq0 : Z.quot ylv (Z.max zlo2 (Z.abs ylv + 1)) = 0).
                  { destruct (Z.le_gt_cases 0 ylv) as [Hp|Hn].
                    - apply Z.quot_small. lia.
                    - replace ylv with (- (- ylv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                  rewrite Hq0. cbn. lia.
               ++ pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
               ++ apply (Hclipx (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                  cbn [idivt3]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). exact I.
          * congruence.
        + apply (Hclipx zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ell. apply Hbf. exact Ell. }
    { (* --- x-upper --- *)
      assert (Hhyf : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
        zle (tyminZ (lo3 (sx3 s)) vz) (hi3 yF)).
      { intros vz Hvlo Hvhi.
        pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
        pose proof (band_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
        assert (Hvzge : zlo2 <= vz) by (pose proof Hvlo as HH; rewrite Hzlo2 in HH; cbn in HH; lia).
        rewrite HyF; cbn [hi3]. apply zle_zmin_glb; [exact Hb1 | ].
        eapply zle_trans; [ exact Hbn | ].
        destruct (hi3 (sx3 s)) as [b| |] eqn:Exu.
        - destruct (Z.le_gt_cases 0 b) as [Hb|Hb].
          + assert (Hzg : zge0 (Fin b) = true) by (cbn; apply Z.leb_le; lia).
            rewrite Hzg. cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 b) Hb).
            destruct (hi3 z2) as [zh| |] eqn:Eh.
            * assert (Hvzle : vz <= zh) by (pose proof Hvhi as HH; cbn in HH; lia).
              rewrite Hzlo2. cbn [sadd3 imul3]. eapply zle_trans; [ | apply zle_zmax_r ]. cbn. nia.
            * cbn [sadd3]. rewrite imul3_fp by lia. rewrite Hzlo2. cbn. exact I.
            * congruence.
          + assert (Hzg : zge0 (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
            rewrite Hzg. cbn [tymaxZ]. rewrite (proj2 (Z.leb_gt 0 b) Hb).
            rewrite Hzlo2. cbn [imul3]. eapply zle_trans; [ | apply zle_zmax_l ]. cbn. nia.
        - cbn [tymaxZ zge0]. rewrite Hzlo2; cbn [sadd3]; rewrite imul3_pinf_fp by lia; cbn; exact I.
        - cbn [tymaxZ]. exact I. }
      assert (Hcxu : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
        forall yhv, hi3 yF = Fin yhv -> zle (Fin (Z.quot yhv vz)) (hi3 (sx3 s)) ->
        zle (Fin (Z.quot yhv vz)) (hi3 (sx3 t))).
      { intros vz Hvlo Hvhi yhv Eyh Hxc.
        assert (Hbu : zle (Fin yhv) (tymaxZ (hi3 (sx3 s)) vz)).
        { destruct (hi3 (sx3 s)) as [b| |] eqn:Exu; cbn [tymaxZ].
          - cbn in Hxc. cbn. apply (tymax_ub b yhv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
          - exact I.
          - cbn in Hxc. contradiction. }
        assert (Hbl : zle (tyminZ (lo3 (sx3 s)) vz) (Fin yhv)) by (rewrite <- Eyh; apply (Hhyf vz Hvlo Hvhi)).
        assert (Hy1 : zle (lo3 (sy3 s)) (Fin yhv)) by (rewrite <- Eyh; exact Hyfhi_lo).
        assert (Hy2 : zle (Fin yhv) (hi3 (sy3 s))) by (rewrite <- Eyh; exact Hyfyh).
        destruct (Hattx vz yhv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [_ HH]. exact HH. }
      destruct (zleb (zmax (zmax (idivt3 (lo3 yF) (lo3 z2)) (idivt3 (lo3 yF) (hi3 z2)))
         (zmax (idivt3 (hi3 yF) (lo3 z2)) (idivt3 (hi3 yF) (hi3 z2)))) (hi3 (sx3 s))) eqn:Hclip.
      - apply zleb_zle in Hclip.
        eapply zle_trans; [ apply zmin_zle_r | ].
        destruct (hi3 yF) as [yhv| |] eqn:Eyh.
        + assert (Hchl : zle (idivt3 (Fin yhv) (lo3 z2)) (hi3 (sx3 s))).
          { eapply zle_trans; [ | exact Hclip ]. eapply zle_trans; [ | apply zle_zmax_r]. apply zle_zmax_l. }
          assert (Hchh : zle (idivt3 (Fin yhv) (hi3 z2)) (hi3 (sx3 s))).
          { eapply zle_trans; [ | exact Hclip ]. eapply zle_trans; [ | apply zle_zmax_r]. apply zle_zmax_r. }
          assert (HA : zle (zmax (idivt3 (Fin yhv) (lo3 z2)) (idivt3 (Fin yhv) (hi3 z2))) (hi3 (sx3 t))).
          { apply zmax_lub.
            - rewrite Hzlo2 in Hchl |- *. cbn [idivt3] in Hchl |- *. apply (Hcxu zlo2 Hzlo2lo Hzlo2hi yhv eq_refl Hchl).
            - destruct (hi3 z2) as [zh| |] eqn:Eh.
              + cbn [idivt3] in Hchh |- *. apply (Hcxu zh Hz2ne (zle_refl _) yhv eq_refl Hchh).
              + cbn [idivt3] in Hchh |- *.
                assert (Hq0 : Z.quot yhv (Z.max zlo2 (Z.abs yhv + 1)) = 0).
                { destruct (Z.le_gt_cases 0 yhv) as [Hp|Hn].
                  - apply Z.quot_small. lia.
                  - replace yhv with (- (- yhv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                rewrite <- Hq0. apply (Hcxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _) yhv eq_refl).
                rewrite Hq0. exact Hchh.
              + congruence. }
          apply zmax_lub; [ | exact HA ].
          eapply zle_trans; [ | exact HA ].
          apply zmax_lub.
          * eapply zle_trans; [ | apply zle_zmax_l ]. rewrite Hzlo2. apply idivt3_mono_pos; [exact Hyfne | lia].
          * eapply zle_trans; [ | apply zle_zmax_r ].
            destruct (hi3 z2) as [zh| |] eqn:Eh; [ apply idivt3_mono_pos; [exact Hyfne | ] | apply zle_refl | congruence ].
            pose proof Hzlo2hi as HH; cbn in HH; lia.
        + assert (Hzp : forall x, zmax x Pinf = Pinf) by (intros [?| |]; reflexivity).
          assert (Ep : idivt3 Pinf (Fin zlo2) = Pinf) by (cbn [idivt3]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
          rewrite Hzlo2, Ep. cbn [zmax]. rewrite Hzp.
          assert (Hxp : hi3 (sx3 s) = Pinf).
          { pose proof Hclip as HC. rewrite Hzlo2, Ep in HC. cbn [zmax] in HC. rewrite Hzp in HC. destruct (hi3 (sx3 s)) eqn:E; try reflexivity; cbn in HC; contradiction. }
          assert (Hyp : hi3 (sy3 s) = Pinf).
          { pose proof Hyfyh as HH. destruct (hi3 (sy3 s)) eqn:E; try reflexivity; cbn in HH; contradiction. }
          destruct (hi3 (sx3 t)) as [M| |] eqn:EtH; [ | exact I | ].
          2:{ exfalso. pose proof (mem3_hi (sx3 t) fx Hftx) as HH. rewrite EtH in HH. cbn in HH. exact HH. }
          exfalso.
          destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy0 [Hmy0 [Hby1 Hby2]]].
          set (vy := Z.max vy0 ((M+1) * zlo2)).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [eapply zle_trans; [apply (mem3_lo _ _ Hmy0) | ]; cbn; unfold vy; lia | rewrite Hyp; exact I]. }
          assert (Hbl : zle (tyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (eapply zle_trans; [exact Hby1 | ]; cbn; unfold vy; lia).
          assert (Hbu : zle (Fin vy) (tymaxZ (hi3 (sx3 s)) zlo2)) by (rewrite Hxp; cbn; exact I).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
          pose proof (mem3_hi (sx3 t) _ Hmxt) as HH. rewrite EtH in HH. cbn in HH.
          assert (Hqge : Z.quot ((M+1) * zlo2) zlo2 <= Z.quot vy zlo2) by (apply Z.quot_le_mono; [lia | unfold vy; lia]).
          rewrite Z.quot_mul in Hqge by lia. lia.
        + pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
      - eapply zle_trans; [ apply zmin_zle_l | ].
        assert (Hzlp : forall x, zleb x Pinf = true) by (intros [?| |]; reflexivity).
        destruct (hi3 (sx3 s)) as [xu| |] eqn:Exu; [ | rewrite Hzlp in Hclip; discriminate | congruence ].
        assert (Hclipxu : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
          zle (Fin (xu + 1)) (idivt3 (hi3 yF) (Fin vz)) -> zle (Fin xu) (hi3 (sx3 t))).
        { intros vz Hvlo Hvhi Hcorner.
          pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
          destruct (attain_vx_hi (lo3 (sx3 s)) (Fin xu) vz xu ltac:(pose proof (Hv1 vz Hvlo); lia) Hxle (zle_refl _)) as (Hbl & Hbu & Hqeq).
          set (vy := if 0 <=? xu then (xu + 1) * vz - 1 else xu * vz) in *.
          assert (Hvylo : zle (lo3 (sy3 s)) (Fin vy)) by (unfold vy; cbn [tymaxZ] in Hb2; exact Hb2).
          assert (Hvyhi : zle (Fin vy) (hi3 (sy3 s))).
          { eapply zle_trans; [ | exact Hyfyh ].
            destruct (hi3 yF) as [yhv| |] eqn:Eyh.
            - cbn [idivt3] in Hcorner. cbn in Hcorner. cbn.
              destruct (Z.lt_ge_cases vy yhv) as [H|H]; [lia | exfalso].
              pose proof (Z.quot_le_mono yhv vy vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
            - exact I.
            - pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
          destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [_ HH]. rewrite Hqeq in HH. exact HH. }
        assert (Hbfu : forall X a, zleb X (Fin a) = false -> zle (Fin (a + 1)) X).
        { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | exact I | discriminate ]. }
        destruct (zleb (idivt3 (hi3 yF) (lo3 z2)) (Fin xu)) eqn:Ehl.
        + destruct (hi3 z2) as [zh| |] eqn:Eh.
          * apply (Hclipxu zh Hz2ne (zle_refl _)).
            destruct (zleb (idivt3 (hi3 yF) (Fin zh)) (Fin xu)) eqn:Ehh.
            -- exfalso. apply zleb_zle in Ehl, Ehh.
               assert (Hle : zle (zmax (zmax (idivt3 (lo3 yF) (lo3 z2)) (idivt3 (lo3 yF) (Fin zh)))
                 (zmax (idivt3 (hi3 yF) (lo3 z2)) (idivt3 (hi3 yF) (Fin zh)))) (Fin xu)).
               { apply zmax_lub; apply zmax_lub; try assumption.
                 - eapply zle_trans; [ | exact Ehl ]. rewrite Hzlo2. apply idivt3_mono_pos; [exact Hyfne | lia].
                 - eapply zle_trans; [ | exact Ehh ]. apply idivt3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia]. }
               apply zleb_zle in Hle. rewrite Hle in Hclip. discriminate.
            -- apply Hbfu. exact Ehh.
          * destruct (Z.le_gt_cases 0 xu) as [Hxu0|Hxu0].
            -- exfalso. apply zleb_zle in Ehl.
               assert (Hle : zle (zmax (zmax (idivt3 (lo3 yF) (lo3 z2)) (idivt3 (lo3 yF) Pinf))
                 (zmax (idivt3 (hi3 yF) (lo3 z2)) (idivt3 (hi3 yF) Pinf))) (Fin xu)).
               { apply zmax_lub; apply zmax_lub.
                 - eapply zle_trans; [ | exact Ehl ]. rewrite Hzlo2. apply idivt3_mono_pos; [exact Hyfne | lia].
                 - cbn [idivt3]. cbn. lia.
                 - exact Ehl.
                 - cbn [idivt3]. cbn. lia. }
               apply zleb_zle in Hle. rewrite Hle in Hclip. discriminate.
            -- destruct (hi3 yF) as [yhv| |] eqn:Eyh.
               ++ apply (Hclipxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                  cbn [idivt3].
                  assert (Hq0 : Z.quot yhv (Z.max zlo2 (Z.abs yhv + 1)) = 0).
                  { destruct (Z.le_gt_cases 0 yhv) as [Hp|Hn].
                    - apply Z.quot_small. lia.
                    - replace yhv with (- (- yhv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                  rewrite Hq0. cbn. lia.
               ++ apply (Hclipxu (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                  cbn [idivt3]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). exact I.
               ++ pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
          * congruence.
        + apply (Hclipxu zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ehl. apply Hbfu. exact Ehl. }
  - (* ===== Y-COMPONENT (goal 2) ===== *)
    apply ile3_intro.
    + (* --- y-lower --- *)
      destruct (lo3 yF) as [vlo| |] eqn:Eylo.
      2:{ pose proof (nonempty_bounds _ EY) as [HH _]; congruence. }
      2:{ assert (Hlo0 : lo3 (sy3 s) = Ninf) by (destruct (lo3 (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyl; contradiction).
          assert (Hzm : forall x, zmax Ninf x = x) by (intros [?| |]; reflexivity).
          rewrite HyF in Eylo; cbn [lo3] in Eylo; rewrite Hlo0, Hzm in Eylo.
          destruct (lo3 (sy3 t)) as [M| |] eqn:EtL; [ | | exact I ].
          2:{ exfalso. pose proof (mem3_lo (sy3 t) fy Hfty) as HH. rewrite EtL in HH. cbn in HH. exact HH. }
          exfalso.
          assert (HMfy : M <= fy) by (pose proof (mem3_lo (sy3 t) fy Hfty) as HH; rewrite EtL in HH; cbn in HH; exact HH).
          assert (Hfyhi : zle (Fin fy) (hi3 (sy3 s))) by (apply (mem3_hi _ _ Hfym)).
          destruct (lo3 (sx3 s)) as [a| |] eqn:Exl.
          + cbn [zpos] in Eylo. destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
            * rewrite (proj2 (Z.ltb_lt 0 a) Ha) in Eylo. rewrite Hzlo2 in Eylo.
              destruct (hi3 z2) as [zh| |] eqn:Eh.
              -- cbn in Eylo. discriminate.
              -- rewrite imul3_fp in Eylo by lia. cbn in Eylo. discriminate.
              -- congruence.
            * rewrite (proj2 (Z.ltb_ge 0 a) Ha) in Eylo. rewrite Hzlo2 in Eylo.
              destruct (hi3 z2) as [zh| |] eqn:Eh.
              -- cbn in Eylo. discriminate.
              -- set (vz := Z.max zlo2 (Z.max 1 (2 - M))).
                 assert (HB1 : zle (lo3 z2) (Fin vz)) by (rewrite Hzlo2; cbn; unfold vz; lia).
                 assert (HB2 : zle (Fin vz) Pinf) by apply zle_Pinf.
                 set (vy := (a-1)*vz+1).
                 assert (HvyM : vy <= M - 1) by (unfold vy, vz; nia).
                 assert (Hmemy : mem3 (sy3 s) vy).
                 { split; [rewrite Hlo0; exact I | eapply zle_trans'; [ | exact Hfyhi]; cbn; lia]. }
                 assert (Htymin : zle (tyminZ (Fin a) vz) (Fin vy)).
                 { cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha). unfold vy. cbn. lia. }
                 assert (Htymax : zle (Fin vy) (tymaxZ (hi3 (sx3 s)) vz)).
                 { pose proof (band_ne (Fin a) (hi3 (sx3 s)) vz (Hv1 vz HB1) Hxle) as Hbn.
                   assert (Etm : tyminZ (Fin a) vz = Fin vy) by (cbn; rewrite (proj2 (Z.ltb_ge 0 a) Ha); unfold vy; reflexivity).
                   rewrite Etm in Hbn. exact Hbn. }
                 destruct (Hwit vz vy HB1 HB2 Hmemy Htymin Htymax) as (_ & Hmyt & _).
                 pose proof (mem3_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. lia.
              -- congruence.
          + congruence.
          + destruct (tymaxZ (hi3 (sx3 s)) zlo2) as [tm| |] eqn:Etm.
            * set (vy := Z.min (M-1) tm).
              assert (Hmemy : mem3 (sy3 s) vy).
              { split; [rewrite Hlo0; exact I | eapply zle_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
              assert (Htymin : zle (tyminZ Ninf zlo2) (Fin vy)) by (cbn; exact I).
              assert (Htymax : zle (Fin vy) (tymaxZ (hi3 (sx3 s)) zlo2)) by (rewrite Etm; cbn; unfold vy; lia).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (mem3_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
            * set (vy := M-1).
              assert (Hmemy : mem3 (sy3 s) vy).
              { split; [rewrite Hlo0; exact I | eapply zle_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
              assert (Htymin : zle (tyminZ Ninf zlo2) (Fin vy)) by (cbn; exact I).
              assert (Htymax : zle (Fin vy) (tymaxZ (hi3 (sx3 s)) zlo2)) by (rewrite Etm; apply zle_Pinf).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (mem3_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
            * exfalso. apply (tymaxZ_not_Ninf (hi3 (sx3 s)) zlo2 Hxun). exact Etm. }
      assert (Hex : exists vzs, zle (lo3 z2) (Fin vzs) /\ zle (Fin vzs) (hi3 z2) /\
        zle (tyminZ (lo3 (sx3 s)) vzs) (Fin vlo) /\ zle (Fin vlo) (tymaxZ (hi3 (sx3 s)) vzs)).
      { destruct (lo3 (sx3 s)) as [a| |] eqn:Exl.
        - destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
          + exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
            pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
            pose proof (band_ne (Fin a) (hi3 (sx3 s)) zlo2 Hzlo21 Hxle) as Hbn.
            assert (Hzmin : zmin (imul3 (Fin a) (lo3 z2)) (imul3 (Fin a) (hi3 z2)) = Fin (a*zlo2)).
            { rewrite Hzlo2. destruct (hi3 z2) as [zhi2| |] eqn:Eh; [ | | congruence ].
              - cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.min_l by nia; reflexivity.
              - cbn. rewrite (proj2 (Z.eqb_neq a 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 a) Ha); reflexivity. }
            assert (Hzp : zpos (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
            assert (Etym : tyminZ (Fin a) zlo2 = Fin (a*zlo2)) by (cbn; rewrite (proj2 (Z.ltb_lt 0 a) Ha); reflexivity).
            split.
            * rewrite Etym, <- Eylo, HyF; cbn [lo3]; rewrite Hzp, Hzmin. apply zle_zmax_r.
            * rewrite <- Eylo, HyF; cbn [lo3]; rewrite Hzp, Hzmin.
              apply zmax_lub; [exact Hb2 | rewrite <- Etym; exact Hbn].
          + destruct (hi3 z2) as [zhi2| |] eqn:Eh.
            * assert (Hzhi2lo : zle (lo3 z2) (Fin zhi2)) by exact Hz2ne.
              exists zhi2. split; [exact Hzhi2lo | split; [apply zle_refl | ]].
              pose proof (Hband zhi2 Hzhi2lo (zle_refl _)) as [Hb1 Hb2].
              pose proof (band_ne (Fin a) (hi3 (sx3 s)) zhi2 (Hv1 zhi2 Hzhi2lo) Hxle) as Hbn.
              assert (Hzp : zpos (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
              assert (Etym : tyminZ (Fin a) zhi2 = Fin ((a-1)*zhi2+1)) by (cbn; rewrite (proj2 (Z.ltb_ge 0 a) Ha); reflexivity).
              assert (Hzmin : zmin (sadd3 (imul3 (sadd3 (Fin a) (-1)) (lo3 z2)) 1) (sadd3 (imul3 (sadd3 (Fin a) (-1)) (Fin zhi2)) 1) = Fin ((a-1)*zhi2+1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.min_r by nia; nia. }
              split.
              -- rewrite Etym, <- Eylo, HyF; cbn [lo3]; rewrite Hzp, Hzmin. apply zle_zmax_r.
              -- rewrite <- Eylo, HyF; cbn [lo3]; rewrite Hzp, Hzmin.
                 apply zmax_lub; [exact Hb2 | rewrite <- Etym; exact Hbn].
            * assert (Hzp: zpos (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
              assert (Hlo3yf : lo3 yF = lo3 (sy3 s)).
              { rewrite HyF; cbn [lo3]; rewrite Hzp, Hzlo2; cbn [sadd3];
                rewrite imul3_fn by lia; cbn; destruct (lo3 (sy3 s)); reflexivity. }
              assert (Hyleq : lo3 (sy3 s) = Fin vlo) by (rewrite <- Hlo3yf; exact Eylo).
              set (vzs := Z.max zlo2 (Z.max 1 (1 - vlo))).
              assert (Hvge : 1 - vlo <= vzs) by (unfold vzs; lia).
              assert (Hvz0 : 0 <= vzs) by (unfold vzs; lia).
              assert (HB1 : zle (lo3 z2) (Fin vzs)) by (rewrite Hzlo2; cbn; unfold vzs; lia).
              exists vzs. split; [exact HB1 | split; [apply zle_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply zle_Pinf)) as [Hb1 Hb2].
              split.
              -- cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha). cbn. nia.
              -- rewrite Hyleq in Hb2. exact Hb2.
            * congruence.
        - congruence.
        - exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          assert (Hlo3yf : lo3 yF = lo3 (sy3 s)).
          { rewrite HyF; cbn [lo3 zpos]; rewrite Hzlo2; cbn [sadd3];
            rewrite imul3_ninf_fp by lia; cbn; destruct (lo3 (sy3 s)); reflexivity. }
          assert (Hyleq : lo3 (sy3 s) = Fin vlo) by (rewrite <- Hlo3yf; exact Eylo).
          split; [ cbn [tyminZ]; exact I | rewrite Hyleq in Hb2; exact Hb2 ]. }
      destruct Hex as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vlo A B Hyfyl Hyflo_hi C D) as [HH _]. exact HH.
    + (* --- y-upper --- *)
      destruct (hi3 yF) as [vhi| |] eqn:Eyhi.
      2:{ assert (Hhi0 : hi3 (sy3 s) = Pinf) by (destruct (hi3 (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyh; contradiction).
          assert (HzM : forall x, zmin Pinf x = x) by (intros [?| |]; reflexivity).
          rewrite HyF in Eyhi; cbn [hi3] in Eyhi; rewrite Hhi0, HzM in Eyhi.
          destruct (hi3 (sy3 t)) as [M| |] eqn:EtH; [ | exact I | ].
          2:{ exfalso. pose proof (mem3_hi (sy3 t) fy Hfty) as HH. rewrite EtH in HH. cbn in HH. exact HH. }
          exfalso.
          assert (HfyM : fy <= M) by (pose proof (mem3_hi (sy3 t) fy Hfty) as HH; rewrite EtH in HH; cbn in HH; exact HH).
          assert (Hfylo : zle (lo3 (sy3 s)) (Fin fy)) by (apply (mem3_lo _ _ Hfym)).
          destruct (hi3 (sx3 s)) as [xu| |] eqn:Exu.
          + cbn [zge0] in Eyhi. destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
            * rewrite (proj2 (Z.leb_le 0 xu) Hu) in Eyhi. rewrite Hzlo2 in Eyhi.
              destruct (hi3 z2) as [zh| |] eqn:Eh.
              -- cbn in Eyhi. discriminate.
              -- set (vz := Z.max zlo2 (Z.max 1 (M + 2))).
                 assert (HB1 : zle (lo3 z2) (Fin vz)) by (rewrite Hzlo2; cbn; unfold vz; lia).
                 assert (HB2 : zle (Fin vz) Pinf) by apply zle_Pinf.
                 set (vy := (xu+1)*vz-1).
                 assert (HvyM : M + 1 <= vy) by (unfold vy, vz; nia).
                 assert (Hmemy : mem3 (sy3 s) vy).
                 { split; [eapply zle_trans'; [exact Hfylo | ]; cbn; lia | rewrite Hhi0; exact I]. }
                 assert (Htymax : zle (Fin vy) (tymaxZ (Fin xu) vz)).
                 { cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 xu) Hu). unfold vy. cbn. lia. }
                 assert (Htymin : zle (tyminZ (lo3 (sx3 s)) vz) (Fin vy)).
                 { pose proof (band_ne (lo3 (sx3 s)) (Fin xu) vz (Hv1 vz HB1) Hxle) as Hbn.
                   assert (Etm : tymaxZ (Fin xu) vz = Fin vy) by (cbn; rewrite (proj2 (Z.leb_le 0 xu) Hu); unfold vy; reflexivity).
                   rewrite Etm in Hbn. exact Hbn. }
                 destruct (Hwit vz vy HB1 HB2 Hmemy Htymin Htymax) as (_ & Hmyt & _).
                 pose proof (mem3_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. lia.
              -- congruence.
            * rewrite (proj2 (Z.leb_gt 0 xu) Hu) in Eyhi. rewrite Hzlo2 in Eyhi.
              destruct (hi3 z2) as [zh| |] eqn:Eh.
              -- cbn in Eyhi. discriminate.
              -- rewrite imul3_fn in Eyhi by lia. cbn in Eyhi. discriminate.
              -- congruence.
          + destruct (tyminZ (lo3 (sx3 s)) zlo2) as [tmn| |] eqn:Etm.
            * set (vy := Z.max (M+1) tmn).
              assert (Hmemy : mem3 (sy3 s) vy).
              { split; [eapply zle_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
              assert (Htymax : zle (Fin vy) (tymaxZ Pinf zlo2)) by (cbn [tymaxZ]; apply zle_Pinf).
              assert (Htymin : zle (tyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; unfold vy; lia).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (mem3_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
            * exfalso. apply (tyminZ_not_Pinf (lo3 (sx3 s)) zlo2 Hxlp). exact Etm.
            * set (vy := M+1).
              assert (Hmemy : mem3 (sy3 s) vy).
              { split; [eapply zle_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
              assert (Htymax : zle (Fin vy) (tymaxZ Pinf zlo2)) by (cbn [tymaxZ]; apply zle_Pinf).
              assert (Htymin : zle (tyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; exact I).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (mem3_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
          + congruence. }
      2:{ pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
      assert (Hexu : exists vzs, zle (lo3 z2) (Fin vzs) /\ zle (Fin vzs) (hi3 z2) /\
        zle (tyminZ (lo3 (sx3 s)) vzs) (Fin vhi) /\ zle (Fin vhi) (tymaxZ (hi3 (sx3 s)) vzs)).
      { destruct (hi3 (sx3 s)) as [xu| |] eqn:Exu.
        - destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
          + destruct (hi3 z2) as [zhi2| |] eqn:Eh.
            * assert (Hzhi2lo : zle (lo3 z2) (Fin zhi2)) by exact Hz2ne.
              exists zhi2. split; [exact Hzhi2lo | split; [apply zle_refl | ]].
              pose proof (Hband zhi2 Hzhi2lo (zle_refl _)) as [Hb1 Hb2].
              pose proof (band_ne (lo3 (sx3 s)) (Fin xu) zhi2 (Hv1 zhi2 Hzhi2lo) Hxle) as Hbn.
              assert (Hzge : zge0 (Fin xu) = true) by (cbn; apply Z.leb_le; lia).
              assert (Etym : tymaxZ (Fin xu) zhi2 = Fin ((xu+1)*zhi2-1)) by (cbn; rewrite (proj2 (Z.leb_le 0 xu) Hu); reflexivity).
              assert (Hzmax : zmax (sadd3 (imul3 (sadd3 (Fin xu) 1) (lo3 z2)) (-1)) (sadd3 (imul3 (sadd3 (Fin xu) 1) (Fin zhi2)) (-1)) = Fin ((xu+1)*zhi2-1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.max_r by nia; nia. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzge, Hzmax. apply zle_zmin_glb; [exact Hb1 | rewrite <- Etym; exact Hbn].
              -- rewrite Etym, <- Eyhi, HyF; cbn [hi3]; rewrite Hzge, Hzmax. rewrite <- Etym. apply zmin_zle_r.
            * assert (Hzge : zge0 (Fin xu) = true) by (cbn; apply Z.leb_le; lia).
              assert (Hhi0 : hi3 yF = hi3 (sy3 s)).
              { rewrite HyF; cbn [hi3]; rewrite Hzge, Hzlo2; cbn [sadd3];
                rewrite imul3_fp by lia; cbn; destruct (hi3 (sy3 s)); reflexivity. }
              assert (Hyheq : hi3 (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
              set (vzs := Z.max zlo2 (Z.max 1 (vhi + 2))).
              assert (Hvge : vhi + 2 <= vzs) by (unfold vzs; lia).
              assert (Hvz0 : 0 <= vzs) by (unfold vzs; lia).
              assert (HB1 : zle (lo3 z2) (Fin vzs)) by (rewrite Hzlo2; cbn; unfold vzs; lia).
              exists vzs. split; [exact HB1 | split; [apply zle_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply zle_Pinf)) as [Hb1 Hb2].
              split.
              -- rewrite <- Hyheq. exact Hb1.
              -- cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 xu) Hu). cbn. nia.
            * congruence.
          + exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
            pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
            pose proof (band_ne (lo3 (sx3 s)) (Fin xu) zlo2 Hzlo21 Hxle) as Hbn.
            assert (Hzge : zge0 (Fin xu) = false) by (cbn; apply Z.leb_gt; lia).
            assert (Etym : tymaxZ (Fin xu) zlo2 = Fin (xu*zlo2)) by (cbn; rewrite (proj2 (Z.leb_gt 0 xu) Hu); reflexivity).
            assert (Hzmax : zmax (imul3 (Fin xu) (lo3 z2)) (imul3 (Fin xu) (hi3 z2)) = Fin (xu*zlo2)).
            { rewrite Hzlo2. destruct (hi3 z2) as [zhi2| |] eqn:Eh; [ | | congruence ].
              - cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.max_l by nia; reflexivity.
              - cbn. rewrite (proj2 (Z.eqb_neq xu 0) ltac:(lia)), (proj2 (Z.ltb_ge 0 xu) ltac:(lia)); reflexivity. }
            split.
            -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzge, Hzmax. apply zle_zmin_glb; [exact Hb1 | rewrite <- Etym; exact Hbn].
            -- rewrite Etym, <- Eyhi, HyF; cbn [hi3]; rewrite Hzge, Hzmax. rewrite <- Etym. apply zmin_zle_r.
        - assert (Hhi0 : hi3 yF = hi3 (sy3 s)).
          { rewrite HyF; cbn [hi3 zge0]; rewrite Hzlo2; cbn [sadd3];
            rewrite imul3_pinf_fp by lia; cbn; destruct (hi3 (sy3 s)); reflexivity. }
          assert (Hyheq : hi3 (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
          exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          split.
          -- rewrite <- Hyheq. exact Hb1.
          -- cbn [tymaxZ]. apply zle_Pinf.
        - congruence. }
      destruct Hexu as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vhi A B Hyfhi_lo Hyfyh C D) as [_ HH]. exact HH.
  - (* ===== Z-COMPONENT (goal 3) ===== *)
    apply ile3_intro.
    + destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy [Hmy [Hby1 Hby2]]].
      destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmy Hby1 Hby2) as (_ & _ & Hmzt).
      rewrite Hzlo2. apply (mem3_lo (sz3 t) zlo2 Hmzt).
    + destruct (hi3 z2) as [zhi2| |] eqn:Ehz2.
      * assert (Hlo : zle (lo3 z2) (Fin zhi2)) by exact Hz2ne.
        destruct (Hpickvy zhi2 Hlo (zle_refl _)) as [vy [Hmy [Hby1 Hby2]]].
        destruct (Hwit zhi2 vy Hlo (zle_refl _) Hmy Hby1 Hby2) as (_ & _ & Hmzt).
        apply (mem3_hi (sz3 t) zhi2 Hmzt).
      * destruct (hi3 (sz3 t)) as [M| |] eqn:Eht.
        -- exfalso.
           assert (Hvzlo : zle (lo3 z2) (Fin (Z.max zlo2 (M+1)))) by (rewrite Hzlo2; cbn; lia).
           assert (Hvzhi : zle (Fin (Z.max zlo2 (M+1))) Pinf) by apply zle_Pinf.
           destruct (Hpickvy (Z.max zlo2 (M+1)) Hvzlo Hvzhi) as [vy [Hmy [Hby1 Hby2]]].
           destruct (Hwit (Z.max zlo2 (M+1)) vy Hvzlo Hvzhi Hmy Hby1 Hby2) as (_ & _ & Hmzt).
           pose proof (mem3_hi (sz3 t) _ Hmzt) as HH. rewrite Eht in HH. cbn in HH. lia.
        -- apply zle_Pinf.
        -- exfalso. pose proof (mem3_hi (sz3 t) fz Hftz) as HH. rewrite Eht in HH. cbn in HH. exact HH.
      * congruence.
Qed.

(* ================================================================== *)
(** Floor positive-slice completeness: support lemmas                  *)
(* ================================================================== *)

Lemma ztdiv4_best_feasible : forall s,
  feasible3 tsol s -> forall t, contains3 tsol s t -> sle3 (ztdiv4 s) t.
Proof.
  intros s Hf t Hct.
  destruct Hf as (fx & fy & fz & Hfin & Hfts).
  assert (Es : ne_store3 s = true) by (eapply ne_store3_true; exact Hfin).
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  assert (HneOut : ne_store3 (ztdiv4 s) = true)
    by (eapply ne_store3_true; apply ztdiv4_soundness; [exact Hfin | exact Hfts]).
  unfold ztdiv4 in *. rewrite Es in *. cbn [negb] in *.
  apply join4_sle_cases; [ | | exact HneOut ].
  - (* positive slice *)
    intro Ep. apply tpos_best.
    + apply (tpos_ne_feasible s Esx Esy Ep).
    + intros vx vy vz Hin Hts Hvz. apply Hct; assumption.
  - (* negative slice *)
    intro En.
    rewrite <- (mir_xz_invol t).
    apply (proj2 (sle3_mir_xz (ztdiv_pos3 (mir_xz s)) (mir_xz t))).
    apply tpos_best.
    + rewrite ne_mir_xz in En.
      assert (Esx' : nonempty3b (sx3 (mir_xz s)) = true)
        by (unfold mir_xz; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
      assert (Esy' : nonempty3b (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
      apply (tpos_ne_feasible (mir_xz s) Esx' Esy' En).
    + intros vx vy vz Hin Hts Hvz.
      (* mirror the slice solution back into s, apply Hct, mirror the containment *)
      pose proof (in_mir_xz_inv s vx vy vz Hin) as Hins.
      pose proof (tsol_mir vx vy vz Hts) as Htss.
      pose proof (Hct (- vx) vy (- vz) Hins Htss) as Hint.
      pose proof (in_mir_xz t (- vx) vy (- vz) Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
Qed.

Theorem ztdiv4_ne_feasible : forall s,
  ne_store3 (ztdiv4 s) = true -> feasible3 tsol s.
Proof.
  intros s Hne. unfold ztdiv4 in Hne.
  destruct (ne_store3 s) eqn:Es; [ | cbn in Hne; congruence ].
  cbn [negb] in Hne.
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  unfold join4 in Hne.
  destruct (ne_store3 (ztdiv_pos3 s)) eqn:Ep; cbn [negb] in Hne.
  - destruct (tpos_ne_feasible s Esx Esy Ep) as (vx & vy & vz & Hin & Hts & Hvz).
    exists vx, vy, vz. split; assumption.
  - rewrite ne_mir_xz in Hne.
    assert (Esx' : nonempty3b (sx3 (mir_xz s)) = true)
      by (unfold mir_xz; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
    assert (Esy' : nonempty3b (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
    destruct (tpos_ne_feasible (mir_xz s) Esx' Esy' Hne) as (vx & vy & vz & Hin & Hts & Hvz).
    exists (- vx), vy, (- vz).
    split; [ apply in_mir_xz_inv; exact Hin | apply tsol_mir; exact Hts ].
Qed.

Theorem ztdiv4_complete : forall s t, contains3 tsol s t -> sle3 (ztdiv4 s) t.
Proof.
  intros s t Hct. destruct (ne_store3 (ztdiv4 s)) eqn:E;
    [ exact (ztdiv4_best_feasible s (ztdiv4_ne_feasible s E) t Hct) | apply sle3_bot; exact E ].
Qed.
(* Floor *)


(* [itv.v] already provides the extended tests [zpos] ("> 0"), [zneg] ("< 0")
   and [ziszero] ("= 0"); we reuse them here. *)

(* same_sign(x, y) := (x < 0) == (y < 0) *)
Definition same_sign3 (a b : Zinf) : bool := Bool.eqb (zneg a) (zneg b).

(* compact, C++-faithful extended multiplication *)
Definition imul3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x * y)                     (* both finite *)
  | _, _ => if ziszero a || ziszero b then Fin 0    (* 0 * oo = 0  *)
            else if same_sign3 a b then Pinf else Ninf
  end.

(* one-Z-variable mixed cases (finite x infinite): after ruling out the finite
   zero, split its sign both ways; [cbn] then reduces the boolean [eqb]s and the
   RHS sign tests, and the two impossible sign combinations die by [lia]. *)
Ltac mix_case v :=
  destruct (Z.eqb_spec v 0) as [->|?]; cbn; [reflexivity|];
  unfold same_sign3, zneg; cbn;
  destruct (Z.ltb_spec v 0) as [?|?];
  destruct (Z.ltb_spec 0 v) as [?|?];
  cbn; first [ reflexivity | exfalso; lia ].

(* the compact version is exactly [itv.v]'s [imul3] *)
Theorem imul3'_eq : forall a b, imul3' a b = imul3 a b.
Proof.
  intros [x| |] [y| |]; cbn; try reflexivity.
  - mix_case x.
  - mix_case x.
  - mix_case y.
  - mix_case y.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Truncated corner division                                       *)
(* ------------------------------------------------------------------ *)

(** The C++ compact form (precondition: b <> 0):
      idiv_t(a, b) :=
        if a,b both finite   : tdiv(a, b)          (* battery::tdiv = round toward 0 *)
        else if b = +/-oo    : 0
        else                 : b > 0 ? a : ineg2(a)
    where [tdiv] is truncated division ([Z.quot]) and [ineg2] is the extended
    negation ([ineg3] from [zdiv.v], +oo <-> -oo).

    [zdiv.v]'s [idivt3] spells out the constructor pairs; here we give the
    compact rendering and prove it is the SAME function. *)

Definition idivt3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (Z.quot x y)             (* both finite: tdiv(a, b) *)
  | _, (Pinf | Ninf) => Fin 0                     (* b = +/-oo               *)
  | _, Fin w => if 0 <? w then a else ineg3 a     (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [zdiv.v]'s [idivt3] (unconditionally, even
   at the excluded b = 0 where both sides agree via [Z.quot _ 0 = 0]) *)
Theorem idivt3'_eq : forall a b, idivt3' a b = idivt3 a b.
Proof. intros [x| |] [y| |]; cbn; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Ceiling corner division                                         *)
(* ------------------------------------------------------------------ *)

(** The C++ compact form (precondition: b <> 0):
      idiv_c(a, b) :=
        if a,b both finite   : cdiv(a, b)           (* battery::cdiv = round up *)
        else if b = +oo      : a > 0 ? 1 : 0
        else if b = -oo      : a < 0 ? 1 : 0
        else                 : b > 0 ? a : ineg2(a)
    where [cdiv] is ceiling division and [ineg2] is [ineg3] (+oo <-> -oo).
    The "a > 0"/"a < 0" tests are [itv.v]'s extended [zpos]/[zneg].

    [itv.v]'s [idivc3] spells out the constructor pairs; here we prove the
    compact rendering is the SAME function. *)

Definition idivc3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (cdiv x y)                 (* both finite: cdiv(a, b) *)
  | _, Pinf => if zpos a then Fin 1 else Fin 0     (* b = +oo : a > 0 ? 1 : 0 *)
  | _, Ninf => if zneg a then Fin 1 else Fin 0     (* b = -oo : a < 0 ? 1 : 0 *)
  | _, Fin w => if 0 <? w then a else ineg3 a      (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [itv.v]'s [idivc3]; the finite/infinite
   corners need to move [Fin] across the [if] (zpos/zneg vs a folded [Fin]). *)
Theorem idivc3'_eq : forall a b, idivc3' a b = idivc3 a b.
Proof.
  intros [x| |] [y| |]; cbn; try reflexivity;
  first [ solve [ destruct (0 <? x); reflexivity ]
        | solve [ destruct (x <? 0); reflexivity ] ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Floor corner division                                           *)
(* ------------------------------------------------------------------ *)

(** The C++ compact form (precondition: b <> 0):
      idiv_f(a, b) :=
        if a,b both finite   : fdiv(a, b)           (* battery::fdiv = round down *)
        else if b = +oo      : a < 0 ? -1 : 0
        else if b = -oo      : a > 0 ? -1 : 0
        else                 : b > 0 ? a : ineg2(a)
    where [fdiv] is floor division ([Z.div]) and [ineg2] is [ineg3].
    The "a < 0"/"a > 0" tests are [itv.v]'s extended [zneg]/[zpos].

    [itv.v]'s [idivf3] spells out the constructor pairs; here we prove the
    compact rendering is the SAME function. *)

Definition idivf3' (a b : Zinf) : Zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x / y)                     (* both finite: fdiv(a, b) *)
  | _, Pinf => if zneg a then Fin (-1) else Fin 0   (* b = +oo : a < 0 ? -1 : 0 *)
  | _, Ninf => if zpos a then Fin (-1) else Fin 0   (* b = -oo : a > 0 ? -1 : 0 *)
  | _, Fin w => if 0 <? w then a else ineg3 a       (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [itv.v]'s [idivf3] *)
Theorem idivf3'_eq : forall a b, idivf3' a b = idivf3 a b.
Proof.
  intros [x| |] [y| |]; cbn; try reflexivity;
  first [ solve [ destruct (x <? 0); reflexivity ]
        | solve [ destruct (0 <? x); reflexivity ] ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Floor via ceil : floor(x/y) = -ceil(-x/y)                        *)
(* ------------------------------------------------------------------ *)

(* the classic identity floor(a) = -ceil(-a), here on the extended integers
   ([ineg3] = extended negation).  Holds unconditionally (even at y = 0). *)
Lemma idivf3_neg_idivc3 : forall x y, idivf3 x y = ineg3 (idivc3 (ineg3 x) y).
Proof.
  intros [v| |] [w| |]; cbn; try reflexivity.
  - (* Fin v, Fin w : v / w = - cdiv (-v) w *)
    f_equal. unfold cdiv. rewrite !Z.opp_involutive. reflexivity.
  - (* Fin v, Pinf : (v<0 ? -1 : 0) = -(0 < -v ? 1 : 0) *)
    destruct (Z.ltb_spec v 0); destruct (Z.ltb_spec 0 (- v)); cbn;
      first [ reflexivity | exfalso; lia ].
  - (* Fin v, Ninf : (0<v ? -1 : 0) = -(-v<0 ? 1 : 0) *)
    destruct (Z.ltb_spec 0 v); destruct (Z.ltb_spec (- v) 0); cbn;
      first [ reflexivity | exfalso; lia ].
  - (* Pinf, Fin w *) destruct (0 <? w); reflexivity.
  - (* Ninf, Fin w *) destruct (0 <? w); reflexivity.
Qed.

(* ================================================================== *)
(** ** Simplified truncated division = [old_tdiv.v]'s [ztdiv4]         *)
(* ================================================================== *)

(** The paper's "simplified truncated division" (Fig. "Simplified truncated
    division") is exactly [ztdiv4] from [old_tdiv.v]:
      - [tden+(x,y)]  = the Z-step of [ztdiv_pos3]  (feasible divisors from the
                        tymin/tymax band, one floor/ceil division per inequality);
      - [tnum+(x,z)]  = the Y-step of [ztdiv_pos3]  (hull of the band endpoints);
      - [tdiv+(y,z)]  = the X-step of [ztdiv_pos3]  (the 4-corner TRUNCATED hull
                        via [idivt3]);
      - [<x=tdiv+(y,z)>]                       = [ztdiv_pos3]  (the positive-z slice);
      - [<x=tdiv(y,z)> = <tdiv+> ⊔ (zneg_xz o <tdiv+> o zneg_xz)] = [ztdiv4]
                        (the two z-sign slices joined bottom-aware by [join4]).

    Two transcription slips in the figure (read against the verified code):
      (1) the X-step is written [d(x) <- fdiv+(d(y),d(z))] but must be [tdiv+]:
          a floor corner is UNSOUND here -- e.g. on x=[0,0], y=[-1,-1], z=[2,2]
          the solution (0,-1,2) (trunc(-1/2)=0) is lost because floor(-1/2)=-1
          drives x to [-1,-1] n [0,0] = bot; the truncated corner keeps it;
      (2) [tden+]'s else-branch numerator [ceil((xu-1)/(xl-1))] should read
          [ceil((yu-1)/(xl-1))] (yu, not xu), matching [ztdiv_pos3].
    With those corrections the figure is [ztdiv4] verbatim. *)

Definition ztdiv_simpl (s : store3) : store3 := ztdiv4 s.

Definition seq3 (a b : store3) : Prop := sle3 a b /\ sle3 b a.

(* Equivalence with [tdiv.v]'s [ztdivq]: both are sound AND complete (best),
   hence they coincide up to the quotient equivalence [~].  Each direction is
   "p complete + q sound", instantiated at the four already-proven facts. *)
Theorem ztdiv_simpl_equiv_ztdivq : forall s, seq3 (ztdiv_simpl s) (ztdivq s).
Proof.
  intro s. unfold ztdiv_simpl, seq3. split.
  - (* ztdiv4 s <= ztdivq s : ztdiv4 complete, ztdivq sound *)
    apply ztdiv4_complete. intros vx vy vz Hin Hts.
    apply ztdivq_soundness; [ exact Hin | destruct Hts; split; assumption ].
  - (* ztdivq s <= ztdiv4 s : ztdivq complete, ztdiv4 sound *)
    apply ztdivq_complete. intros vx vy vz Hin Hts.
    apply ztdiv4_soundness; [ exact Hin | destruct Hts; split; assumption ].
Qed.
