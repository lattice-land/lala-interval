(** * equivcpp.v : C++-faithful rendering of the infinity-aware helpers.

    The lala C++ code defines extended-integer multiplication compactly as
      mul_zinf(a, b) :=
        if a,b both finite         : a * b
        else if a = 0 or b = 0     : 0
        else                       : same_sign(a, b) ? +oo : -oo
      same_sign(x, y) := (x < 0) == (y < 0)
    over a machine type where +oo/-oo are sentinel values.

    [zitv.v]'s [mul_zinf] instead spells out all nine constructor pairs, which
    reduces cleanly under [cbn] in the propagator proofs.  Here we give the
    compact rendering [mul_zinf'] (matching the C++ line for line, using the
    [isneg_zinf] "< 0" test since [zinf] is not a single numeric type) and prove it
    is extensionally the SAME function as [mul_zinf]. *)

From Stdlib Require Import ZArith Bool Lia.
From LalaInterval Require Import Concrete ZItv3 zdiv.
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

Definition idivt3 (n m : zinf) : zinf :=
  match m with
  | Pinf | Ninf => Fin 0
  | Fin w => match n with
             | Fin v => Fin (Z.quot v w)
             | Pinf => if 0 <? w then Pinf else Ninf
             | Ninf => if 0 <? w then Ninf else Pinf
             end
  end.

(* negation on zinf; mirrors the C++ [ineg]. *)
Definition ztdiv_pos3 (s : zitv3) : zitv3 :=
  let x := x s in let y := sy3 s in
  let z := ZItv (max_zinf (lb (sz3 s)) (Fin 1)) (ub (sz3 s)) in
  if negb (is_not_bot_zitv z) then ZItv3 x y z else
  (* Z: tymin(x.lb, z) <= y.ub *)
  let z :=
    if ispos_zinf (lb x) then ZItv (lb z) (min_zinf (ub z) (fdiv_zinf (ub y) (lb x)))
    else ZItv (max_zinf (lb z) (cdiv_zinf (addk_zinf (ub y) (-1)) (addk_zinf (lb x) (-1)))) (ub z) in
  (* Z: tymax(x.ub, z) >= y.lb *)
  let z :=
    if geq0_zinf (ub x) then
      ZItv (max_zinf (lb z) (cdiv_zinf (addk_zinf (lb y) 1) (addk_zinf (ub x) 1))) (ub z)
    else ZItv (lb z) (min_zinf (ub z) (fdiv_zinf (lb y) (ub x))) in
  if negb (is_not_bot_zitv z) then ZItv3 x y z else
  (* Y: hull of [tymin(x.lb, z), tymax(x.ub, z)] over the narrowed z *)
  let y := ZItv
    (max_zinf (lb y)
          (if ispos_zinf (lb x)
           then min_zinf (mul_zinf (lb x) (lb z)) (mul_zinf (lb x) (ub z))
           else min_zinf (addk_zinf (mul_zinf (addk_zinf (lb x) (-1)) (lb z)) 1)
                     (addk_zinf (mul_zinf (addk_zinf (lb x) (-1)) (ub z)) 1)))
    (min_zinf (ub y)
          (if geq0_zinf (ub x)
           then max_zinf (addk_zinf (mul_zinf (addk_zinf (ub x) 1) (lb z)) (-1))
                     (addk_zinf (mul_zinf (addk_zinf (ub x) 1) (ub z)) (-1))
           else max_zinf (mul_zinf (ub x) (lb z)) (mul_zinf (ub x) (ub z)))) in
  if negb (is_not_bot_zitv y) then ZItv3 x y z else
  (* X: 4-corner hull of tdiv(y, z) *)
  let x := ZItv
    (max_zinf (lb x) (min_zinf (min_zinf (idivt3 (lb y) (lb z)) (idivt3 (lb y) (ub z)))
                        (min_zinf (idivt3 (ub y) (lb z)) (idivt3 (ub y) (ub z)))))
    (min_zinf (ub x) (max_zinf (max_zinf (idivt3 (lb y) (lb z)) (idivt3 (lb y) (ub z)))
                        (max_zinf (idivt3 (ub y) (lb z)) (idivt3 (ub y) (ub z))))) in
  ZItv3 x y z.

(* ------------------------------------------------------------------ *)
(** ** The four propagators (slice decomposition + join)               *)
(* ------------------------------------------------------------------ *)

(* the C++ join block: a failed positive slice is replaced wholesale by the
   negative one; a failed negative slice is dropped; otherwise hull. *)
Definition ztdiv4 (s : zitv3) : zitv3 :=
  if negb (ne_zitv3 s) then s
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

(* ===== zinf lattice extras ===== *)
Lemma xlo : forall yb zl zu vy vz,
  leq_zinf yb (Fin vy) -> leq_zinf (Fin 1) zl -> leq_zinf zl (Fin vz) -> leq_zinf (Fin vz) zu ->
  leq_zinf (min_zinf (idivt3 yb zl) (idivt3 yb zu)) (Fin (Z.quot vy vz)).
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
  leq_zinf (Fin vy) yb -> leq_zinf (Fin 1) zl -> leq_zinf zl (Fin vz) -> leq_zinf (Fin vz) zu ->
  leq_zinf (Fin (Z.quot vy vz)) (max_zinf (idivt3 yb zl) (idivt3 yb zu)).
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
  1 <= vz -> leq_zinf (lb (x s)) (Fin (Z.quot vy vz)) -> leq_zinf (Fin vy) (ub (sy3 s)) ->
  ispos_zinf (lb (x s)) = true ->
  leq_zinf (Fin vz) (fdiv_zinf (ub (sy3 s)) (lb (x s))).
Proof.
  intros s vy vz Hvz Hxl Hyu Hzp.
  destruct (lb (x s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate; try (cbn in Hxl; contradiction).
  (* lb x = Fin a, 0 < a *)
  apply Z.ltb_lt in Hzp. cbn in Hxl.
  pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
  rewrite (proj2 (Z.ltb_lt 0 a) Hzp) in Hty. (* tymin = a*vz *)
  destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
  - cbn [fdiv_zinf]. cbn. apply F1; lia.
  - cbn [fdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 a) Hzp). exact I.
Qed.

Lemma z1_neg_ob : forall s vy vz,
  1 <= vz -> leq_zinf (lb (x s)) (Fin (Z.quot vy vz)) -> leq_zinf (Fin vy) (ub (sy3 s)) ->
  ispos_zinf (lb (x s)) = false ->
  leq_zinf (cdiv_zinf (addk_zinf (ub (sy3 s)) (-1)) (addk_zinf (lb (x s)) (-1))) (Fin vz).
Proof.
  intros s vy vz Hvz Hxl Hyu Hzp.
  destruct (lb (x s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate.
  - (* Fin a, a <= 0 *)
    apply Z.ltb_ge in Hzp. cbn in Hxl.
    pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
    rewrite (proj2 (Z.ltb_ge 0 a) Hzp) in Hty. (* tymin = (a-1)*vz+1 *)
    destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
    + cbn [addk_zinf cdiv_zinf]. cbn. apply C1; nia.
    + cbn [addk_zinf cdiv_zinf]. rewrite (proj2 (Z.ltb_ge 0 (a + -1)) ltac:(lia)). exact I.
  - (* Ninf : bound is 0 or 1 <= vz *)
    cbn [addk_zinf].
    destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
    + cbn [addk_zinf cdiv_zinf]. destruct (u + -1 <? 0); cbn; lia.
    + cbn [addk_zinf cdiv_zinf]. cbn; lia.
Qed.

(* Z2: tymax(x.ub,z) >= y.lb  --> refine z *)
Lemma z2_pos_ob : forall s vy vz,
  1 <= vz -> leq_zinf (Fin (Z.quot vy vz)) (ub (x s)) -> leq_zinf (lb (sy3 s)) (Fin vy) ->
  geq0_zinf (ub (x s)) = true ->
  leq_zinf (cdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (x s)) 1)) (Fin vz).
Proof.
  intros s vy vz Hvz Hxu Hyl Hzg.
  destruct (ub (x s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  - (* Fin b, 0 <= b *)
    apply Z.leb_le in Hzg. cbn in Hxu.
    pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
    rewrite (proj2 (Z.leb_le 0 b) Hzg) in Hty. (* tymax = (b+1)*vz-1 *)
    destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
    + cbn [addk_zinf cdiv_zinf]. cbn. apply CC1; lia.
    + cbn [addk_zinf cdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 (b + 1)) ltac:(lia)). exact I.
  - (* Pinf : bound is 0 or 1 <= vz *)
    cbn [addk_zinf].
    destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
    + cbn [addk_zinf cdiv_zinf]. destruct (0 <? l + 1); cbn; lia.
    + cbn [addk_zinf cdiv_zinf]. cbn; lia.
Qed.

Lemma z2_neg_ob : forall s vy vz,
  1 <= vz -> leq_zinf (Fin (Z.quot vy vz)) (ub (x s)) -> leq_zinf (lb (sy3 s)) (Fin vy) ->
  geq0_zinf (ub (x s)) = false ->
  leq_zinf (Fin vz) (fdiv_zinf (lb (sy3 s)) (ub (x s))).
Proof.
  intros s vy vz Hvz Hxu Hyl Hzg.
  destruct (ub (x s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  (* Fin b, b < 0 *)
  apply Z.leb_gt in Hzg. cbn in Hxu.
  pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
  rewrite (proj2 (Z.leb_gt 0 b) Hzg) in Hty. (* tymax = b*vz *)
  destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
  - cbn [fdiv_zinf]. cbn. apply FN1; lia.
  - cbn [fdiv_zinf]. rewrite (proj2 (Z.ltb_ge 0 b) ltac:(lia)). exact I.
Qed.

(* ===== mul_zinf reductions at infinities (positive z side) ===== *)
Lemma ylo_pos : forall s vy vz iz,
  1 <= vz -> leq_zinf (Fin 1) (lb iz) -> leq_zinf (lb iz) (Fin vz) -> leq_zinf (Fin vz) (ub iz) ->
  leq_zinf (lb (x s)) (Fin (Z.quot vy vz)) -> ispos_zinf (lb (x s)) = true ->
  leq_zinf (min_zinf (mul_zinf (lb (x s)) (lb iz)) (mul_zinf (lb (x s)) (ub iz))) (Fin vy).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxl Hzp.
  destruct (lb (x s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate; try (cbn in Hxl; contradiction).
  apply Z.ltb_lt in Hzp. cbn in Hxl.
  pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
  rewrite (proj2 (Z.ltb_lt 0 a) Hzp) in Hty.
  destruct (lb iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (ub iz) as [zu| |]; cbn in Hzu; try contradiction.
  - cbn. pose proof (Z.le_min_l (a*zl) (a*zu)). nia.
  - rewrite mul_zinf_fp by lia. cbn. nia.
Qed.

Lemma ylo_neg : forall s vy vz iz,
  1 <= vz -> leq_zinf (Fin 1) (lb iz) -> leq_zinf (lb iz) (Fin vz) -> leq_zinf (Fin vz) (ub iz) ->
  leq_zinf (lb (x s)) (Fin (Z.quot vy vz)) -> ispos_zinf (lb (x s)) = false ->
  leq_zinf (min_zinf (addk_zinf (mul_zinf (addk_zinf (lb (x s)) (-1)) (lb iz)) 1)
            (addk_zinf (mul_zinf (addk_zinf (lb (x s)) (-1)) (ub iz)) 1)) (Fin vy).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxl Hzp.
  destruct (lb iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (lb (x s)) as [a| |] eqn:Ex; cbn in Hzp; try discriminate.
  - (* Fin a, a<=0 *)
    apply Z.ltb_ge in Hzp. cbn in Hxl.
    pose proof (tymin_lb a vy vz ltac:(lia) Hxl) as Hty.
    rewrite (proj2 (Z.ltb_ge 0 a) Hzp) in Hty. (* (a-1)*vz+1 <= vy *)
    destruct (ub iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn [addk_zinf mul_zinf]. cbn. pose proof (Z.le_min_r (a + -1 * zl + 1)%Z (a + -1 * zu + 1)%Z). nia.
    + cbn [addk_zinf]. rewrite mul_zinf_fn by lia. cbn. nia.
  - (* Ninf *)
    cbn [addk_zinf].
    destruct (ub iz) as [zu| |]; cbn in Hzu; try contradiction.
    + rewrite !mul_zinf_ninf_fp by lia. cbn. exact I.
    + rewrite mul_zinf_ninf_fp by lia. cbn. exact I.
Qed.

Lemma yhi_pos : forall s vy vz iz,
  1 <= vz -> leq_zinf (Fin 1) (lb iz) -> leq_zinf (lb iz) (Fin vz) -> leq_zinf (Fin vz) (ub iz) ->
  leq_zinf (Fin (Z.quot vy vz)) (ub (x s)) -> geq0_zinf (ub (x s)) = true ->
  leq_zinf (Fin vy) (max_zinf (addk_zinf (mul_zinf (addk_zinf (ub (x s)) 1) (lb iz)) (-1))
                     (addk_zinf (mul_zinf (addk_zinf (ub (x s)) 1) (ub iz)) (-1))).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxu Hzg.
  destruct (lb iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (ub (x s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  - (* Fin b, 0<=b *)
    apply Z.leb_le in Hzg. cbn in Hxu.
    pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
    rewrite (proj2 (Z.leb_le 0 b) Hzg) in Hty. (* vy <= (b+1)*vz-1 *)
    destruct (ub iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn [addk_zinf mul_zinf]. cbn. pose proof (Z.le_max_r (b + 1 * zl + -1)%Z (b + 1 * zu + -1)%Z). nia.
    + cbn [addk_zinf]. rewrite mul_zinf_fp by lia. cbn. exact I.
  - (* Pinf : max_zinf collapses to Pinf via the lo-z corner *)
    cbn [addk_zinf]. rewrite mul_zinf_pinf_fp by lia. cbn. exact I.
Qed.

Lemma yhi_neg : forall s vy vz iz,
  1 <= vz -> leq_zinf (Fin 1) (lb iz) -> leq_zinf (lb iz) (Fin vz) -> leq_zinf (Fin vz) (ub iz) ->
  leq_zinf (Fin (Z.quot vy vz)) (ub (x s)) -> geq0_zinf (ub (x s)) = false ->
  leq_zinf (Fin vy) (max_zinf (mul_zinf (ub (x s)) (lb iz)) (mul_zinf (ub (x s)) (ub iz))).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxu Hzg.
  destruct (lb iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (ub (x s)) as [b| |] eqn:Ex; cbn in Hzg; try discriminate; try (cbn in Hxu; contradiction).
  (* Fin b, b<0 *)
  apply Z.leb_gt in Hzg. cbn in Hxu.
  pose proof (tymax_ub b vy vz ltac:(lia) Hxu) as Hty.
  rewrite (proj2 (Z.leb_gt 0 b) Hzg) in Hty. (* vy <= b*vz *)
  destruct (ub iz) as [zu| |]; cbn in Hzu; try contradiction.
  - cbn. pose proof (Z.le_max_l (b*zl) (b*zu)). nia.
  - rewrite mul_zinf_fn by lia. cbn. nia.
Qed.

(* ===== step combinators for the z narrowings ===== *)
Lemma step_hilo : forall (C:bool) lo hi Bh Bl vz,
  leq_zinf lo (Fin vz) -> leq_zinf (Fin vz) hi ->
  (C = true -> leq_zinf (Fin vz) Bh) -> (C = false -> leq_zinf Bl (Fin vz)) ->
  contains (if C then ZItv lo (min_zinf hi Bh) else ZItv (max_zinf lo Bl) hi) vz.
Proof.
  intros C lo hi Bh Bl vz Hlo Hhi HT HF. destruct C.
  - apply contains_narrow_hi; [exact Hlo|exact Hhi|apply HT;reflexivity].
  - apply contains_narrow_lo; [exact Hlo|exact Hhi|apply HF;reflexivity].
Qed.

Lemma step_lohi : forall (C:bool) lo hi Bl Bh vz,
  leq_zinf lo (Fin vz) -> leq_zinf (Fin vz) hi ->
  (C = true -> leq_zinf Bl (Fin vz)) -> (C = false -> leq_zinf (Fin vz) Bh) ->
  contains (if C then ZItv (max_zinf lo Bl) hi else ZItv lo (min_zinf hi Bh)) vz.
Proof.
  intros C lo hi Bl Bh vz Hlo Hhi HT HF. destruct C.
  - apply contains_narrow_lo; [exact Hlo|exact Hhi|apply HT;reflexivity].
  - apply contains_narrow_hi; [exact Hlo|exact Hhi|apply HF;reflexivity].
Qed.

Lemma step_hilo_pos : forall (C:bool) lo hi Bh Bl,
  leq_zinf (Fin 1) lo ->
  leq_zinf (Fin 1) (lb (if C then ZItv lo (min_zinf hi Bh) else ZItv (max_zinf lo Bl) hi)).
Proof. intros C lo hi Bh Bl H. destruct C; cbn [lb]; [exact H | eapply leq_zinf_trans;[exact H|apply leq_zinf_max_zinf_l]]. Qed.
Lemma step_lohi_pos : forall (C:bool) lo hi Bl Bh,
  leq_zinf (Fin 1) lo ->
  leq_zinf (Fin 1) (lb (if C then ZItv (max_zinf lo Bl) hi else ZItv lo (min_zinf hi Bh))).
Proof. intros C lo hi Bl Bh H. destruct C; cbn [lb]; [eapply leq_zinf_trans;[exact H|apply leq_zinf_max_zinf_l] | exact H]. Qed.


(* ================================================================== *)
(** Support lemmas for the floored positive-slice soundness proof
    ([fpos_sound]): floor band, divisor monotonicity, corner-hull
    brackets, and the 4-way Z-step (empty branch => no solution) *)
(* ================================================================== *)

(* ===== floor band lemmas (z>0): floor(y/z)>=v <-> y>=v*z ; <=v <-> y<=(v+1)*z-1 ===== *)
Theorem tpos_sound : forall s vx vy vz,
  in_zitv3 s vx vy vz -> tsol vx vy vz -> 1 <= vz ->
  in_zitv3 (ztdiv_pos3 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hts Hvz1.
  destruct Hin as (Hmx & Hmy & Hmz).
  destruct Hts as [Hnz Hq]. subst vx.
  destruct Hmx as [Hxl Hxu]; destruct Hmy as [Hyl Hyu]; destruct Hmz as [Hzl0 Hzu0].
  unfold ztdiv_pos3; cbv zeta.
  (* --- z0 --- *)
  match goal with |- context[is_not_bot_zitv ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hmz0l : leq_zinf (lb z0) (Fin vz)) by (rewrite Hz0; cbn [lb]; apply max_zinf_lub; [exact Hzl0 | cbn; lia]).
  assert (Hmz0u : leq_zinf (Fin vz) (ub z0)) by (rewrite Hz0; cbn [ub]; exact Hzu0).
  assert (Hlz0 : leq_zinf (Fin 1) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_r).
  destruct (negb (is_not_bot_zitv z0)) eqn:E0.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj Hyl Hyu) | exact (conj Hmz0l Hmz0u)]]. }
  (* --- z1 --- *)
  match goal with |- context[if ispos_zinf (lb (x s)) then ?A else ?B] =>
    remember (if ispos_zinf (lb (x s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hmz1 : contains z1 vz).
  { rewrite Hz1. apply step_hilo.
    - exact Hmz0l.
    - exact Hmz0u.
    - intro Hc. apply (z1_pos_ob s vy vz); [exact Hvz1 | exact Hxl | exact Hyu | exact Hc].
    - intro Hc. apply (z1_neg_ob s vy vz); [exact Hvz1 | exact Hxl | exact Hyu | exact Hc]. }
  assert (Hlz1 : leq_zinf (Fin 1) (lb z1)) by (rewrite Hz1; apply step_hilo_pos; exact Hlz0).
  destruct Hmz1 as [Hmz1l Hmz1u].
  (* --- z2 --- *)
  match goal with |- context[if geq0_zinf (ub (x s)) then ?A else ?B] =>
    remember (if geq0_zinf (ub (x s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hmz2 : contains z2 vz).
  { rewrite Hz2. apply step_lohi.
    - exact Hmz1l.
    - exact Hmz1u.
    - intro Hc. apply (z2_pos_ob s vy vz); [exact Hvz1 | exact Hxu | exact Hyl | exact Hc].
    - intro Hc. apply (z2_neg_ob s vy vz); [exact Hvz1 | exact Hxu | exact Hyl | exact Hc]. }
  assert (Hlz2 : leq_zinf (Fin 1) (lb z2)) by (rewrite Hz2; apply step_lohi_pos; exact Hlz1).
  destruct Hmz2 as [Hmz2l Hmz2u].
  destruct (negb (is_not_bot_zitv z2)) eqn:E2.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj Hyl Hyu) | exact (conj Hmz2l Hmz2u)]]. }
  (* --- yF --- *)
  match goal with |- context[is_not_bot_zitv ?Y] => remember Y as yF eqn:HyF end.
  assert (Hmy : contains yF vy).
  { rewrite HyF. apply contains_narrow_both.
    - exact Hyl.
    - exact Hyu.
    - destruct (ispos_zinf (lb (x s))) eqn:Ezp.
      + apply (ylo_pos s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxl|exact Ezp].
      + apply (ylo_neg s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxl|exact Ezp].
    - destruct (geq0_zinf (ub (x s))) eqn:Ezg.
      + apply (yhi_pos s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxu|exact Ezg].
      + apply (yhi_neg s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxu|exact Ezg]. }
  destruct Hmy as [HmyL HmyU].
  destruct (negb (is_not_bot_zitv yF)) eqn:EY.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj HmyL HmyU) | exact (conj Hmz2l Hmz2u)]]. }
  (* --- final: xF --- *)
  split.
  - apply contains_narrow_both.
    + exact Hxl.
    + exact Hxu.
    + eapply leq_zinf_trans; [apply leq_zinf_min_zinf_l | ].
      apply (xlo (lb yF) (lb z2) (ub z2)); [exact HmyL|exact Hlz2|exact Hmz2l|exact Hmz2u].
    + eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ].
      apply (xhi (ub yF) (lb z2) (ub z2)); [exact HmyU|exact Hlz2|exact Hmz2l|exact Hmz2u].
  - split; [exact (conj HmyL HmyU) | exact (conj Hmz2l Hmz2u)].
Qed.


(* ================================================================== *)
(** Support machinery for [tpos_ne_feasible]: the reverse band lemmas,
    the zinf band bounds, the propagator-reconstruction core
    [ispos_zinf3_band], and the finite-witness picker. *)
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
Definition tyminZ (xl : zinf) (vz : Z) : zinf :=
  match xl with
  | Fin a => Fin (if 0 <? a then a * vz else (a - 1) * vz + 1)
  | Ninf => Ninf
  | Pinf => Pinf
  end.
Definition tymaxZ (xu : zinf) (vz : Z) : zinf :=
  match xu with
  | Fin b => Fin (if 0 <=? b then (b + 1) * vz - 1 else b * vz)
  | Pinf => Pinf
  | Ninf => Ninf
  end.

Lemma quot_ge : forall xl vy vz, 1 <= vz ->
  leq_zinf (tyminZ xl vz) (Fin vy) -> leq_zinf xl (Fin (Z.quot vy vz)).
Proof.
  intros [a| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  apply tymin_lb_rev; [lia | exact H].
Qed.

Lemma quot_le : forall xu vy vz, 1 <= vz ->
  leq_zinf (Fin vy) (tymaxZ xu vz) -> leq_zinf (Fin (Z.quot vy vz)) xu.
Proof.
  intros [b| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  apply tymax_ub_rev; [lia | exact H].
Qed.

Lemma band_ne : forall xl xu vz, 1 <= vz ->
  leq_zinf xl xu -> leq_zinf (tyminZ xl vz) (tymaxZ xu vz).
Proof.
  intros [a| |] [b| |] vz Hvz H; cbn in *; try exact I; try contradiction.
  destruct (Z.ltb_spec 0 a); destruct (Z.leb_spec 0 b); nia.
Qed.

(* ===== band-condition extraction from the narrowed divisor bounds ===== *)
Lemma z1band_neg : forall yu vz a, a <= 0 -> yu <> Ninf ->
  leq_zinf (cdiv_zinf (addk_zinf yu (-1)) (addk_zinf (Fin a) (-1))) (Fin vz) ->
  leq_zinf (Fin ((a - 1) * vz + 1)) yu.
Proof.
  intros yu vz a Ha Hyn H. cbn [addk_zinf] in H.
  destruct yu as [u| |]; try congruence.
  - cbn [addk_zinf cdiv_zinf] in H. cbn in H.
    assert (Hle : (a + -1) * vz <= u + -1) by (apply RC1; [lia | exact H]). cbn. nia.
  - cbn. exact I.
Qed.

Lemma z2band_neg : forall yl vz b, b < 0 -> yl <> Pinf ->
  leq_zinf (Fin vz) (fdiv_zinf yl (Fin b)) -> leq_zinf yl (Fin (b * vz)).
Proof.
  intros yl vz b Hb Hyp H.
  destruct yl as [l| |]; try congruence.
  - cbn [fdiv_zinf] in H. cbn in H.
    assert (Hle : l <= b * vz) by (apply mul_ge_div_neg; [lia | exact H]). cbn. lia.
  - cbn. exact I.
Qed.

(* ===== picking a finite witness in a nonempty zinf interval ===== *)
Lemma step_hilo_lo : forall (C:bool) lo hi Bh Bl,
  leq_zinf lo (lb (if C then ZItv lo (min_zinf hi Bh) else ZItv (max_zinf lo Bl) hi)).
Proof. intros; destruct C; cbn [lb]; [apply leq_zinf_refl | apply leq_zinf_max_zinf_l]. Qed.
Lemma step_hilo_hi : forall (C:bool) lo hi Bh Bl,
  leq_zinf (ub (if C then ZItv lo (min_zinf hi Bh) else ZItv (max_zinf lo Bl) hi)) hi.
Proof. intros; destruct C; cbn [ub]; [apply leq_zinf_min_zinf_l | apply leq_zinf_refl]. Qed.
Lemma step_lohi_lo : forall (C:bool) lo hi Bl Bh,
  leq_zinf lo (lb (if C then ZItv (max_zinf lo Bl) hi else ZItv lo (min_zinf hi Bh))).
Proof. intros; destruct C; cbn [lb]; [apply leq_zinf_max_zinf_l | apply leq_zinf_refl]. Qed.
Lemma step_lohi_hi : forall (C:bool) lo hi Bl Bh,
  leq_zinf (ub (if C then ZItv (max_zinf lo Bl) hi else ZItv lo (min_zinf hi Bh))) hi.
Proof. intros; destruct C; cbn [ub]; [apply leq_zinf_refl | apply leq_zinf_min_zinf_l]. Qed.

Lemma ispos_zinf3_band : forall s,
  is_not_bot_zitv (x s) = true -> is_not_bot_zitv (sy3 s) = true ->
  ne_zitv3 (ztdiv_pos3 s) = true ->
  exists vz, 1 <= vz /\ contains (sz3 s) vz
    /\ leq_zinf (tyminZ (lb (x s)) vz) (ub (sy3 s))
    /\ leq_zinf (lb (sy3 s)) (tymaxZ (ub (x s)) vz).
Proof.
  intros s Hx Hy Hne.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  unfold ztdiv_pos3 in Hne; cbv zeta in Hne.
  match type of Hne with context[is_not_bot_zitv ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : leq_zinf (Fin 1) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_r).
  assert (Hz0hi : ub z0 = ub (sz3 s)) by (rewrite Hz0; cbn [ub]; reflexivity).
  assert (Hz0lo : leq_zinf (lb (sz3 s)) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_l).
  destruct (is_not_bot_zitv z0) eqn:E0; cbn [negb] in Hne;
    [ | unfold ne_zitv3 in Hne; cbn [x sy3 sz3] in Hne;
        rewrite E0, !andb_false_r in Hne; discriminate ].
  match type of Hne with context[if ispos_zinf (lb (x s)) then ?A else ?B] =>
    remember (if ispos_zinf (lb (x s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : leq_zinf (Fin 1) (lb z1)) by (rewrite Hz1; apply step_hilo_pos; exact Hz0l1).
  assert (Hlo01 : leq_zinf (lb z0) (lb z1)) by (rewrite Hz1; apply step_hilo_lo).
  assert (Hhi01 : leq_zinf (ub z1) (ub z0)) by (rewrite Hz1; apply step_hilo_hi).
  match type of Hne with context[if geq0_zinf (ub (x s)) then ?A else ?B] =>
    remember (if geq0_zinf (ub (x s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : leq_zinf (Fin 1) (lb z2)) by (rewrite Hz2; apply step_lohi_pos; exact Hz1l1).
  assert (Hlo12 : leq_zinf (lb z1) (lb z2)) by (rewrite Hz2; apply step_lohi_lo).
  assert (Hhi12 : leq_zinf (ub z2) (ub z1)) by (rewrite Hz2; apply step_lohi_hi).
  destruct (is_not_bot_zitv z2) eqn:E2; cbn [negb] in Hne;
    [ | unfold ne_zitv3 in Hne; cbn [x sy3 sz3] in Hne;
        rewrite E2, !andb_false_r in Hne; discriminate ].
  (* reach the final store; we only need E2 : is_not_bot_zitv z2 = true *)
  clear Hne.
  (* extract vz = lb z2 as a finite value >= 1 *)
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  pose proof (ne_leq_zinf _ E2) as Hz2ne.
  destruct (fin_of_ge1 (lb z2) Hz2l1 Hz2lp) as [zv [Ez2lo Hvz1]].
  exists zv. split; [exact Hvz1 | ].
  (* contains (sz3 s) zv *)
  assert (Hzvhi : leq_zinf (Fin zv) (ub (sz3 s))).
  { rewrite <- Hz0hi. eapply leq_zinf_trans; [ | exact Hhi01].
    eapply leq_zinf_trans; [ | exact Hhi12]. rewrite <- Ez2lo. exact Hz2ne. }
  assert (Hzvlo : leq_zinf (lb (sz3 s)) (Fin zv)).
  { rewrite <- Ez2lo. eapply leq_zinf_trans; [exact Hz0lo | ].
    eapply leq_zinf_trans; [exact Hlo01 | exact Hlo12]. }
  split; [ split; [exact Hzvlo | exact Hzvhi] | ].
  assert (Hzvhi2 : leq_zinf (Fin zv) (ub z2)) by (rewrite <- Ez2lo; exact Hz2ne).
  split.
  - (* Z1 band: tyminZ (lo x) zv <= hi y *)
    destruct (lb (x s)) as [a| |] eqn:Exl;
      [ | congruence | cbn [tyminZ]; exact I ].
    destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
    + (* a > 0 : ispos_zinf true -> z1 hi-narrow *)
      assert (Hzp : ispos_zinf (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
      rewrite Hzp in Hz1.
      cbn [tyminZ]. rewrite (proj2 (Z.ltb_lt 0 a) Ha).
      apply (z1band_pos (ub (sy3 s)) zv a Ha Hyun).
      eapply leq_zinf_trans; [ exact Hzvhi2 | ].
      eapply leq_zinf_trans; [ exact Hhi12 | ].
      rewrite Hz1; cbn [ub]. apply min_zinf_leq_zinf_r.
    + (* a <= 0 : ispos_zinf false -> z1 lo-narrow *)
      assert (Hzp : ispos_zinf (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
      rewrite Hzp in Hz1.
      cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha).
      apply (z1band_neg (ub (sy3 s)) zv a Ha Hyun).
      eapply leq_zinf_trans; [ | rewrite <- Ez2lo; exact Hlo12 ].
      rewrite Hz1; cbn [lb]. apply leq_zinf_max_zinf_r.
  - (* Z2 band: lo y <= tymaxZ (hi x) zv *)
    destruct (ub (x s)) as [b| |] eqn:Exu;
      [ | cbn [tymaxZ]; apply leq_zinf_Pinf | congruence ].
    destruct (Z.lt_ge_cases 0 b) as [Hb|Hb].
    + (* b > 0 : geq0_zinf true -> z2 lo-narrow *)
      assert (Hzg : geq0_zinf (Fin b) = true) by (cbn; apply Z.leb_le; lia).
      rewrite Hzg in Hz2.
      cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 b) ltac:(lia)).
      apply (z2band_pos (lb (sy3 s)) zv b ltac:(lia) Hylp).
      eapply leq_zinf_trans; [ | rewrite <- Ez2lo; apply leq_zinf_refl ].
      rewrite Hz2; cbn [lb]. apply leq_zinf_max_zinf_r.
    + (* b <= 0 : split geq0_zinf on b = 0 vs b < 0 *)
      destruct (Z.eq_dec b 0) as [->|Hbn].
      * (* b = 0 : geq0_zinf true -> lo-narrow *)
        assert (Hzg : geq0_zinf (Fin 0) = true) by (cbn; reflexivity).
        rewrite Hzg in Hz2.
        cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 0) ltac:(lia)).
        apply (z2band_pos (lb (sy3 s)) zv 0 ltac:(lia) Hylp).
        eapply leq_zinf_trans; [ | rewrite <- Ez2lo; apply leq_zinf_refl ].
        rewrite Hz2; cbn [lb]. apply leq_zinf_max_zinf_r.
      * (* b < 0 : geq0_zinf false -> hi-narrow *)
        assert (Hzg : geq0_zinf (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
        rewrite Hzg in Hz2.
        cbn [tymaxZ]. rewrite (proj2 (Z.leb_gt 0 b) ltac:(lia)).
        apply (z2band_neg (lb (sy3 s)) zv b ltac:(lia) Hylp).
        eapply leq_zinf_trans; [ exact Hzvhi2 | ].
        rewrite Hz2; cbn [ub]. apply min_zinf_leq_zinf_r.
Qed.

(* ===== non-Pinf/non-Ninf preservation for the witness interval ===== *)
Lemma tyminZ_not_Pinf : forall xl vz, xl <> Pinf -> tyminZ xl vz <> Pinf.
Proof. intros [a| |] vz H; cbn; congruence. Qed.
Lemma tymaxZ_not_Ninf : forall xu vz, xu <> Ninf -> tymaxZ xu vz <> Ninf.
Proof. intros [b| |] vz H; cbn; congruence. Qed.


Theorem tpos_ne_feasible : forall s,
  is_not_bot_zitv (x s) = true -> is_not_bot_zitv (sy3 s) = true ->
  ne_zitv3 (ztdiv_pos3 s) = true -> slice_feasible tsol s.
Proof.
  intros s Hx Hy Hne.
  destruct (ispos_zinf3_band s Hx Hy Hne) as [vz [Hvz1 [Hmz [Hb1 Hb2]]]].
  pose proof (ne_leq_zinf _ Hx) as Hxle.
  pose proof (ne_leq_zinf _ Hy) as Hyle.
  pose proof (band_ne (lb (x s)) (ub (x s)) vz Hvz1 Hxle) as Hbn.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  set (L := max_zinf (tyminZ (lb (x s)) vz) (lb (sy3 s))).
  set (U := min_zinf (tymaxZ (ub (x s)) vz) (ub (sy3 s))).
  assert (HLU : leq_zinf L U).
  { unfold L, U. apply leq_zinf_min_zinf_glb.
    - apply max_zinf_lub; [exact Hbn | exact Hb2].
    - apply max_zinf_lub; [exact Hb1 | exact Hyle]. }
  assert (HLp : L <> Pinf)
    by (unfold L; apply max_zinf_not_Pinf; [apply tyminZ_not_Pinf; exact Hxlp | exact Hylp]).
  assert (HUn : U <> Ninf)
    by (unfold U; apply min_zinf_not_Ninf; [apply tymaxZ_not_Ninf; exact Hxun | exact Hyun]).
  destruct (pickf_mem L U HLU HLp HUn) as [HLvy HvyU].
  unfold L in HLvy. unfold U in HvyU.
  set (vy := pickf L U) in *.
  exists (Z.quot vy vz), vy, vz.
  split.
  - split; [ | split ].
    + split.
      * apply quot_ge; [exact Hvz1 | eapply leq_zinf_trans; [apply leq_zinf_max_zinf_l | exact HLvy]].
      * apply quot_le; [exact Hvz1 | eapply leq_zinf_trans; [exact HvyU | apply leq_zinf_min_zinf_l]].
    + split.
      * eapply leq_zinf_trans; [apply leq_zinf_max_zinf_r | exact HLvy].
      * eapply leq_zinf_trans; [exact HvyU | apply min_zinf_leq_zinf_r].
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
  in_zitv3 s vx vy vz -> tsol vx vy vz -> in_zitv3 (ztdiv4 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hts.
  assert (Hne : ne_zitv3 s = true) by (eapply ne_zitv3_true; exact Hin).
  unfold ztdiv4. rewrite Hne. cbn [negb].
  destruct Hts as [Hnz Hq].
  destruct (Z.lt_total vz 0) as [Hisneg_zinf | [Hz0 | Hispos_zinf]].
  - (* vz <= -1 : negative slice via mirror *)
    apply in_join4_r.
    assert (Hmir : in_zitv3 (mir_xz s) (- vx) vy (- vz)) by (apply in_mir_xz; exact Hin).
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
  slice_contains tsol s t -> 1 <= vz -> contains (sz3 s) vz -> contains (sy3 s) vy ->
  leq_zinf (tyminZ (lb (x s)) vz) (Fin vy) -> leq_zinf (Fin vy) (tymaxZ (ub (x s)) vz) ->
  contains (x t) (Z.quot vy vz) /\ contains (sy3 t) vy /\ contains (sz3 t) vz.
Proof.
  intros s t vz vy Hct Hvz1 Hmz Hmy Hb1 Hb2.
  assert (Hin : in_zitv3 s (Z.quot vy vz) vy vz).
  { split; [ split | split; [exact Hmy | exact Hmz]].
    - apply quot_ge; [exact Hvz1 | exact Hb1].
    - apply quot_le; [exact Hvz1 | exact Hb2]. }
  assert (Hsol : tsol (Z.quot vy vz) vy vz) by (split; [lia | reflexivity]).
  exact (Hct _ _ _ Hin Hsol Hvz1).
Qed.

Lemma attain_vx : forall xl xu vz v, 0 < vz -> leq_zinf xl (Fin v) -> leq_zinf (Fin v) xu ->
  leq_zinf (tyminZ xl vz) (Fin (if 0 <? v then v * vz else (v - 1) * vz + 1)) /\
  leq_zinf (Fin (if 0 <? v then v * vz else (v - 1) * vz + 1)) (tymaxZ xu vz) /\
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
Lemma attain_vx_hi : forall xl xu vz v, 0 < vz -> leq_zinf xl (Fin v) -> leq_zinf (Fin v) xu ->
  leq_zinf (tyminZ xl vz) (Fin (if 0 <=? v then (v + 1) * vz - 1 else v * vz)) /\
  leq_zinf (Fin (if 0 <=? v then (v + 1) * vz - 1 else v * vz)) (tymaxZ xu vz) /\
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
Lemma idivt3_mono_pos : forall n1 n2 w, leq_zinf n1 n2 -> 0 < w ->
  leq_zinf (idivt3 n1 (Fin w)) (idivt3 n2 (Fin w)).
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
  assert (HneO : ne_zitv3 (ztdiv_pos3 s) = true).
  { eapply ne_zitv3_true. apply tpos_sound; [exact Hfin | exact Hfts | exact Hfz1]. }
  destruct Hfin as (Hfxm & Hfym & Hfzm).
  assert (Hx : is_not_bot_zitv (x s) = true) by (eapply isbot_true; exact Hfxm).
  assert (Hy : is_not_bot_zitv (sy3 s) = true) by (eapply isbot_true; exact Hfym).
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  pose proof (ne_leq_zinf _ Hx) as Hxle.
  pose proof (ne_leq_zinf _ Hy) as Hyle.
  unfold ztdiv_pos3 in HneO |- *; cbv zeta in HneO |- *.
  match goal with |- context[is_not_bot_zitv ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : leq_zinf (Fin 1) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_r).
  assert (Hz0hi : ub z0 = ub (sz3 s)) by (rewrite Hz0; cbn [ub]; reflexivity).
  assert (Hz0lo : leq_zinf (lb (sz3 s)) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_l).
  destruct (is_not_bot_zitv z0) eqn:E0; cbn [negb] in HneO |- *;
    [ | unfold ne_zitv3 in HneO; cbn [x sy3 sz3] in HneO;
        rewrite E0, !andb_false_r in HneO; discriminate ].
  match goal with |- context[if ispos_zinf (lb (x s)) then ?A else ?B] =>
    remember (if ispos_zinf (lb (x s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : leq_zinf (Fin 1) (lb z1)) by (rewrite Hz1; apply step_hilo_pos; exact Hz0l1).
  assert (Hlo01 : leq_zinf (lb z0) (lb z1)) by (rewrite Hz1; apply step_hilo_lo).
  assert (Hhi01 : leq_zinf (ub z1) (ub z0)) by (rewrite Hz1; apply step_hilo_hi).
  match goal with |- context[if geq0_zinf (ub (x s)) then ?A else ?B] =>
    remember (if geq0_zinf (ub (x s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : leq_zinf (Fin 1) (lb z2)) by (rewrite Hz2; apply step_lohi_pos; exact Hz1l1).
  assert (Hlo12 : leq_zinf (lb z1) (lb z2)) by (rewrite Hz2; apply step_lohi_lo).
  assert (Hhi12 : leq_zinf (ub z2) (ub z1)) by (rewrite Hz2; apply step_lohi_hi).
  destruct (is_not_bot_zitv z2) eqn:E2; cbn [negb] in HneO |- *;
    [ | unfold ne_zitv3 in HneO; cbn [x sy3 sz3] in HneO;
        rewrite E2, !andb_false_r in HneO; discriminate ].
  match goal with |- context[is_not_bot_zitv ?Y] => remember Y as yF eqn:HyF end.
  destruct (is_not_bot_zitv yF) eqn:EY; cbn [negb] in HneO |- *;
    [ | unfold ne_zitv3 in HneO; cbn [x sy3 sz3] in HneO;
        rewrite EY, !andb_false_r in HneO; discriminate ].
  assert (Hband : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (tyminZ (lb (x s)) vz) (ub (sy3 s)) /\ leq_zinf (lb (sy3 s)) (tymaxZ (ub (x s)) vz)).
  { intros vz Hvlo Hvhi. split.
    - destruct (lb (x s)) as [a| |] eqn:Exl; [ | congruence | cbn [tyminZ]; exact I ].
      destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
      + assert (Hzp : ispos_zinf (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
        rewrite Hzp in Hz1. cbn [tyminZ]. rewrite (proj2 (Z.ltb_lt 0 a) Ha).
        apply (z1band_pos (ub (sy3 s)) vz a Ha Hyun).
        eapply leq_zinf_trans; [ exact Hvhi | ]. eapply leq_zinf_trans; [ exact Hhi12 | ].
        rewrite Hz1; cbn [ub]. apply min_zinf_leq_zinf_r.
      + assert (Hzp : ispos_zinf (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
        rewrite Hzp in Hz1. cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha).
        apply (z1band_neg (ub (sy3 s)) vz a Ha Hyun).
        eapply leq_zinf_trans; [ | eapply leq_zinf_trans; [ exact Hlo12 | exact Hvlo ] ].
        rewrite Hz1; cbn [lb]. apply leq_zinf_max_zinf_r.
    - destruct (ub (x s)) as [b| |] eqn:Exu; [ | cbn [tymaxZ]; apply leq_zinf_Pinf | congruence ].
      destruct (Z.lt_ge_cases 0 b) as [Hb|Hb].
      + assert (Hzg : geq0_zinf (Fin b) = true) by (cbn; apply Z.leb_le; lia).
        rewrite Hzg in Hz2. cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 b) ltac:(lia)).
        apply (z2band_pos (lb (sy3 s)) vz b ltac:(lia) Hylp).
        eapply leq_zinf_trans; [ | exact Hvlo ]. rewrite Hz2; cbn [lb]. apply leq_zinf_max_zinf_r.
      + destruct (Z.eq_dec b 0) as [->|Hbn].
        * assert (Hzg : geq0_zinf (Fin 0) = true) by (cbn; reflexivity).
          rewrite Hzg in Hz2. cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 0) ltac:(lia)).
          apply (z2band_pos (lb (sy3 s)) vz 0 ltac:(lia) Hylp).
          eapply leq_zinf_trans; [ | exact Hvlo ]. rewrite Hz2; cbn [lb]. apply leq_zinf_max_zinf_r.
        * assert (Hzg : geq0_zinf (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
          rewrite Hzg in Hz2. cbn [tymaxZ]. rewrite (proj2 (Z.leb_gt 0 b) ltac:(lia)).
          apply (z2band_neg (lb (sy3 s)) vz b ltac:(lia) Hylp).
          eapply leq_zinf_trans; [ exact Hvhi | ].
          rewrite Hz2; cbn [ub]. apply min_zinf_leq_zinf_r. }
  assert (Hmemz : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) -> contains (sz3 s) vz).
  { intros vz Hvlo Hvhi. unfold contains. split.
    - eapply leq_zinf_trans; [exact Hz0lo | ]. eapply leq_zinf_trans; [exact Hlo01 | ].
      eapply leq_zinf_trans; [exact Hlo12 | exact Hvlo].
    - rewrite <- Hz0hi. eapply leq_zinf_trans; [exact Hvhi | ].
      eapply leq_zinf_trans; [exact Hhi12 | exact Hhi01]. }
  assert (Hv1 : forall vz, leq_zinf (lb z2) (Fin vz) -> 1 <= vz).
  { intros vz Hvlo. assert (HH : leq_zinf (Fin 1) (Fin vz)) by (eapply leq_zinf_trans; [exact Hz2l1 | exact Hvlo]).
    cbn in HH. lia. }
  assert (Hwit : forall vz vy, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    contains (sy3 s) vy -> leq_zinf (tyminZ (lb (x s)) vz) (Fin vy) -> leq_zinf (Fin vy) (tymaxZ (ub (x s)) vz) ->
    contains (x t) (Z.quot vy vz) /\ contains (sy3 t) vy /\ contains (sz3 t) vz).
  { intros vz vy Hvlo Hvhi Hmy Hby1 Hby2.
    apply (wit_in_t s t vz vy Hct (Hv1 vz Hvlo) (Hmemz vz Hvlo Hvhi) Hmy Hby1 Hby2). }
  assert (Hpickvy : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    exists vy, contains (sy3 s) vy /\ leq_zinf (tyminZ (lb (x s)) vz) (Fin vy) /\ leq_zinf (Fin vy) (tymaxZ (ub (x s)) vz)).
  { intros vz Hvlo Hvhi.
    destruct (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (band_ne (lb (x s)) (ub (x s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    set (L := max_zinf (tyminZ (lb (x s)) vz) (lb (sy3 s))).
    set (U := min_zinf (tymaxZ (ub (x s)) vz) (ub (sy3 s))).
    assert (HLU : leq_zinf L U).
    { unfold L, U. apply leq_zinf_min_zinf_glb.
      - apply max_zinf_lub; [exact Hbn | exact Hb2].
      - apply max_zinf_lub; [exact Hb1 | exact Hyle]. }
    assert (HLp : L <> Pinf) by (unfold L; apply max_zinf_not_Pinf; [apply tyminZ_not_Pinf; exact Hxlp | exact Hylp]).
    assert (HUn : U <> Ninf) by (unfold U; apply min_zinf_not_Ninf; [apply tymaxZ_not_Ninf; exact Hxun | exact Hyun]).
    destruct (pickf_mem L U HLU HLp HUn) as [HLvy HvyU].
    unfold L in HLvy. unfold U in HvyU.
    exists (pickf L U). split; [ | split].
    - split; [ eapply leq_zinf_trans; [apply leq_zinf_max_zinf_r | exact HLvy] | eapply leq_zinf_trans; [exact HvyU | apply min_zinf_leq_zinf_r] ].
    - eapply leq_zinf_trans; [apply leq_zinf_max_zinf_l | exact HLvy].
    - eapply leq_zinf_trans; [exact HvyU | apply leq_zinf_min_zinf_l]. }
  assert (Hft : in_zitv3 t fx fy fz)
    by (apply Hct; [split; [exact Hfxm | split; [exact Hfym | exact Hfzm]] | exact Hfts | exact Hfz1]).
  destruct Hft as (Hftx & Hfty & Hftz).
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  pose proof (ne_leq_zinf _ E2) as Hz2ne.
  destruct (fin_of_ge1 (lb z2) Hz2l1 Hz2lp) as [zlo2 [Hzlo2 Hzlo21]].
  assert (Hzlo2lo : leq_zinf (lb z2) (Fin zlo2)) by (rewrite Hzlo2; apply leq_zinf_refl).
  assert (Hzlo2hi : leq_zinf (Fin zlo2) (ub z2)) by (rewrite <- Hzlo2; exact Hz2ne).
  assert (Hatt : forall vz vy, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (lb (sy3 s)) (Fin vy) -> leq_zinf (Fin vy) (ub (sy3 s)) ->
    leq_zinf (tyminZ (lb (x s)) vz) (Fin vy) -> leq_zinf (Fin vy) (tymaxZ (ub (x s)) vz) ->
    leq_zinf (lb (sy3 t)) (Fin vy) /\ leq_zinf (Fin vy) (ub (sy3 t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (_ & Hmyt & _).
    split; [apply (contains_lo _ _ Hmyt) | apply (contains_hi _ _ Hmyt)]. }
  assert (Hattx : forall vz vy, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (lb (sy3 s)) (Fin vy) -> leq_zinf (Fin vy) (ub (sy3 s)) ->
    leq_zinf (tyminZ (lb (x s)) vz) (Fin vy) -> leq_zinf (Fin vy) (tymaxZ (ub (x s)) vz) ->
    leq_zinf (lb (x t)) (Fin (Z.quot vy vz)) /\ leq_zinf (Fin (Z.quot vy vz)) (ub (x t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (Hmxt & _ & _).
    split; [apply (contains_lo _ _ Hmxt) | apply (contains_hi _ _ Hmxt)]. }
  pose proof (ne_leq_zinf _ EY) as Hyfne.
  assert (Hyfyl : leq_zinf (lb (sy3 s)) (lb yF)) by (rewrite HyF; cbn [lb]; apply leq_zinf_max_zinf_l).
  assert (Hyfyh : leq_zinf (ub yF) (ub (sy3 s))) by (rewrite HyF; cbn [ub]; apply leq_zinf_min_zinf_l).
  assert (Hyflo_hi : leq_zinf (lb yF) (ub (sy3 s))) by (eapply leq_zinf_trans; [exact Hyfne | exact Hyfyh]).
  assert (Hyfhi_lo : leq_zinf (lb (sy3 s)) (ub yF)) by (eapply leq_zinf_trans; [exact Hyfyl | exact Hyfne]).
  apply sle3_intro; cbn [x sy3 sz3].
  - (* ===== X-COMPONENT (goal 1) ===== *)
    assert (Hlyf : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
      leq_zinf (lb yF) (tymaxZ (ub (x s)) vz)).
    { intros vz Hvlo Hvhi.
      pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
      pose proof (band_ne (lb (x s)) (ub (x s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
      assert (Hvzge : zlo2 <= vz) by (pose proof Hvlo as HH; rewrite Hzlo2 in HH; cbn in HH; lia).
      rewrite HyF; cbn [lb]. apply max_zinf_lub; [exact Hb2 | ].
      eapply leq_zinf_trans; [ | exact Hbn ].
      destruct (lb (x s)) as [a| |] eqn:Exl.
      - destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
        + assert (Hzp : ispos_zinf (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
          rewrite Hzp, Hzlo2. cbn [tyminZ]. rewrite (proj2 (Z.ltb_lt 0 a) Ha). cbn [mul_zinf].
          eapply leq_zinf_trans; [ apply leq_zinf_min_zinf_l | cbn; nia ].
        + assert (Hzp : ispos_zinf (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
          rewrite Hzp. cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha).
          destruct (ub z2) as [zh| |] eqn:Eh.
          * assert (Hvleq_zinf : vz <= zh) by (pose proof Hvhi as HH; cbn in HH; lia).
            rewrite Hzlo2. cbn [addk_zinf mul_zinf]. eapply leq_zinf_trans; [ apply min_zinf_leq_zinf_r | cbn; nia ].
          * cbn [addk_zinf]. rewrite mul_zinf_fn by lia. cbn.
            eapply leq_zinf_trans; [ apply min_zinf_leq_zinf_r | cbn; exact I ].
          * congruence.
      - cbn [tyminZ]. apply leq_zinf_Pinf.
      - cbn [tyminZ ispos_zinf]. rewrite Hzlo2; cbn [addk_zinf]; rewrite mul_zinf_ninf_fp by lia; cbn; exact I. }
    assert (Hbf : forall X a, leqb_zinf (Fin a) X = false -> leq_zinf X (Fin (a - 1))).
    { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | discriminate | exact I ]. }
  apply leq_zitv_intro; cbn [lb ub].
    { (* --- x-lower --- *)
      assert (Hcx : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
        forall ylv, lb yF = Fin ylv -> leq_zinf (lb (x s)) (Fin (Z.quot ylv vz)) ->
        leq_zinf (lb (x t)) (Fin (Z.quot ylv vz))).
      { intros vz Hvlo Hvhi ylv Eyl Hxc.
        assert (Hbl : leq_zinf (tyminZ (lb (x s)) vz) (Fin ylv)).
        { destruct (lb (x s)) as [a| |] eqn:Exl; cbn [tyminZ].
          - cbn in Hxc. cbn. apply (tymin_lb a ylv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
          - cbn in Hxc. contradiction.
          - exact I. }
        assert (Hbu : leq_zinf (Fin ylv) (tymaxZ (ub (x s)) vz)) by (rewrite <- Eyl; apply (Hlyf vz Hvlo Hvhi)).
        assert (Hy1 : leq_zinf (lb (sy3 s)) (Fin ylv)) by (rewrite <- Eyl; exact Hyfyl).
        assert (Hy2 : leq_zinf (Fin ylv) (ub (sy3 s))) by (rewrite <- Eyl; exact Hyflo_hi).
        destruct (Hattx vz ylv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [HH _]. exact HH. }
      destruct (leqb_zinf (lb (x s)) (min_zinf (min_zinf (idivt3 (lb yF) (lb z2)) (idivt3 (lb yF) (ub z2)))
         (min_zinf (idivt3 (ub yF) (lb z2)) (idivt3 (ub yF) (ub z2))))) eqn:Hclip.
      - apply leq_zinf_prop_bool_equiv in Hclip.
        eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ].
        destruct (lb yF) as [ylv| |] eqn:Eyl.
        + assert (Hcll : leq_zinf (lb (x s)) (idivt3 (Fin ylv) (lb z2))).
          { eapply leq_zinf_trans; [exact Hclip | ]. eapply leq_zinf_trans; [apply leq_zinf_min_zinf_l | apply leq_zinf_min_zinf_l]. }
          assert (Hclh : leq_zinf (lb (x s)) (idivt3 (Fin ylv) (ub z2))).
          { eapply leq_zinf_trans; [exact Hclip | ]. eapply leq_zinf_trans; [apply leq_zinf_min_zinf_l | apply min_zinf_leq_zinf_r]. }
          assert (HA : leq_zinf (lb (x t)) (min_zinf (idivt3 (Fin ylv) (lb z2)) (idivt3 (Fin ylv) (ub z2)))).
          { apply leq_zinf_min_zinf_glb.
            - rewrite Hzlo2 in Hcll |- *. cbn [idivt3] in Hcll |- *. apply (Hcx zlo2 Hzlo2lo Hzlo2hi ylv eq_refl Hcll).
            - destruct (ub z2) as [zh| |] eqn:Eh.
              + cbn [idivt3] in Hclh |- *. apply (Hcx zh Hz2ne (leq_zinf_refl _) ylv eq_refl Hclh).
              + cbn [idivt3] in Hclh |- *.
                assert (Hq0 : Z.quot ylv (Z.max zlo2 (Z.abs ylv + 1)) = 0).
                { destruct (Z.le_gt_cases 0 ylv) as [Hp|Hn].
                  - apply Z.quot_small. lia.
                  - replace ylv with (- (- ylv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                rewrite <- Hq0. apply (Hcx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _) ylv eq_refl).
                rewrite Hq0. exact Hclh.
              + congruence. }
          apply leq_zinf_min_zinf_glb; [exact HA | ].
          eapply leq_zinf_trans; [exact HA | ].
          apply leq_zinf_min_zinf_glb.
          * eapply leq_zinf_trans; [apply leq_zinf_min_zinf_l | rewrite Hzlo2; apply idivt3_mono_pos; [exact Hyfne | lia] ].
          * eapply leq_zinf_trans; [apply min_zinf_leq_zinf_r | ].
            destruct (ub z2) as [zh| |] eqn:Eh; [ apply idivt3_mono_pos; [exact Hyfne | ] | apply leq_zinf_refl | congruence ].
            pose proof Hzlo2hi as HH; cbn in HH; lia.
        + pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
        + assert (En : idivt3 Ninf (Fin zlo2) = Ninf) by (cbn [idivt3]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
          rewrite Hzlo2, En. cbn [min_zinf].
          assert (Hxn : lb (x s) = Ninf).
          { pose proof Hclip as HC. rewrite Hzlo2, En in HC. cbn [min_zinf] in HC. destruct (lb (x s)) eqn:E; try reflexivity; cbn in HC; contradiction. }
          assert (Hyn : lb (sy3 s) = Ninf).
          { pose proof Hyfyl as HH. destruct (lb (sy3 s)) eqn:E; try reflexivity; cbn in HH; contradiction. }
          destruct (lb (x t)) as [M| |] eqn:EtL; [ | | exact I ].
          2:{ exfalso. pose proof (contains_lo (x t) fx Hftx) as HH. rewrite EtL in HH. cbn in HH. exact HH. }
          exfalso.
          destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy0 [Hmy0 [Hby1 Hby2]]].
          set (vy := Z.min vy0 ((M-1) * zlo2)).
          assert (Hmemy : contains (sy3 s) vy).
          { split; [rewrite Hyn; exact I | eapply leq_zinf_trans; [ | apply (contains_hi _ _ Hmy0)]; cbn; unfold vy; lia]. }
          assert (Hbl : leq_zinf (tyminZ (lb (x s)) zlo2) (Fin vy)) by (rewrite Hxn; cbn; exact I).
          assert (Hbu : leq_zinf (Fin vy) (tymaxZ (ub (x s)) zlo2)) by (eapply leq_zinf_trans; [ | exact Hby2]; cbn; unfold vy; lia).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
          pose proof (contains_lo (x t) _ Hmxt) as HH. rewrite EtL in HH. cbn in HH.
          assert (Hqle : Z.quot vy zlo2 <= Z.quot ((M-1) * zlo2) zlo2) by (apply Z.quot_le_mono; [lia | unfold vy; lia]).
          rewrite Z.quot_mul in Hqle by lia. lia.
      - eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ].
        destruct (lb (x s)) as [xl| |] eqn:Exl; [ | congruence | cbn [leqb_zinf] in Hclip; discriminate ].
        assert (Hclipx : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
          leq_zinf (idivt3 (lb yF) (Fin vz)) (Fin (xl - 1)) -> leq_zinf (lb (x t)) (Fin xl)).
        { intros vz Hvlo Hvhi Hcorner.
          pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
          destruct (attain_vx (Fin xl) (ub (x s)) vz xl ltac:(pose proof (Hv1 vz Hvlo); lia) (leq_zinf_refl _) Hxle) as (Hbl & Hbu & Hqeq).
          set (vy := if 0 <? xl then xl * vz else (xl - 1) * vz + 1) in *.
          assert (Hvyhi : leq_zinf (Fin vy) (ub (sy3 s))) by (unfold vy; cbn [tyminZ] in Hb1; exact Hb1).
          assert (Hvylo : leq_zinf (lb (sy3 s)) (Fin vy)).
          { eapply leq_zinf_trans; [exact Hyfyl | ].
            destruct (lb yF) as [ylv| |] eqn:Eyl.
            - cbn [idivt3] in Hcorner. cbn in Hcorner. cbn.
              destruct (Z.lt_ge_cases ylv vy) as [H|H]; [lia | exfalso].
              pose proof (Z.quot_le_mono vy ylv vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
            - pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
            - exact I. }
          destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [HH _]. rewrite Hqeq in HH. exact HH. }
        destruct (leqb_zinf (Fin xl) (idivt3 (lb yF) (lb z2))) eqn:Ell.
        + destruct (ub z2) as [zh| |] eqn:Eh.
          * apply (Hclipx zh Hz2ne (leq_zinf_refl _)).
            destruct (leqb_zinf (Fin xl) (idivt3 (lb yF) (Fin zh))) eqn:Elh.
            -- exfalso. apply leq_zinf_prop_bool_equiv in Ell, Elh.
               assert (Hge : leq_zinf (Fin xl) (min_zinf (min_zinf (idivt3 (lb yF) (lb z2)) (idivt3 (lb yF) (Fin zh)))
                 (min_zinf (idivt3 (ub yF) (lb z2)) (idivt3 (ub yF) (Fin zh))))).
               { apply leq_zinf_min_zinf_glb; apply leq_zinf_min_zinf_glb; try assumption.
                 - eapply leq_zinf_trans; [exact Ell | rewrite Hzlo2; apply idivt3_mono_pos; [exact Hyfne | lia] ].
                 - eapply leq_zinf_trans; [exact Elh | apply idivt3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia] ]. }
               apply leq_zinf_prop_bool_equiv in Hge. rewrite Hge in Hclip. discriminate.
            -- apply Hbf. exact Elh.
          * destruct (Z.le_gt_cases xl 0) as [Hxl0|Hxl0].
            -- exfalso. apply leq_zinf_prop_bool_equiv in Ell.
               assert (Hge : leq_zinf (Fin xl) (min_zinf (min_zinf (idivt3 (lb yF) (lb z2)) (idivt3 (lb yF) Pinf))
                 (min_zinf (idivt3 (ub yF) (lb z2)) (idivt3 (ub yF) Pinf)))).
               { apply leq_zinf_min_zinf_glb; apply leq_zinf_min_zinf_glb.
                 - exact Ell.
                 - cbn [idivt3]. cbn. lia.
                 - eapply leq_zinf_trans; [exact Ell | rewrite Hzlo2; apply idivt3_mono_pos; [exact Hyfne | lia] ].
                 - cbn [idivt3]. cbn. lia. }
               apply leq_zinf_prop_bool_equiv in Hge. rewrite Hge in Hclip. discriminate.
            -- destruct (lb yF) as [ylv| |] eqn:Eyl.
               ++ apply (Hclipx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                  cbn [idivt3].
                  assert (Hq0 : Z.quot ylv (Z.max zlo2 (Z.abs ylv + 1)) = 0).
                  { destruct (Z.le_gt_cases 0 ylv) as [Hp|Hn].
                    - apply Z.quot_small. lia.
                    - replace ylv with (- (- ylv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                  rewrite Hq0. cbn. lia.
               ++ pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
               ++ apply (Hclipx (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                  cbn [idivt3]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). exact I.
          * congruence.
        + apply (Hclipx zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ell. apply Hbf. exact Ell. }
    { (* --- x-upper --- *)
      assert (Hhyf : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
        leq_zinf (tyminZ (lb (x s)) vz) (ub yF)).
      { intros vz Hvlo Hvhi.
        pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
        pose proof (band_ne (lb (x s)) (ub (x s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
        assert (Hvzge : zlo2 <= vz) by (pose proof Hvlo as HH; rewrite Hzlo2 in HH; cbn in HH; lia).
        rewrite HyF; cbn [ub]. apply leq_zinf_min_zinf_glb; [exact Hb1 | ].
        eapply leq_zinf_trans; [ exact Hbn | ].
        destruct (ub (x s)) as [b| |] eqn:Exu.
        - destruct (Z.le_gt_cases 0 b) as [Hb|Hb].
          + assert (Hzg : geq0_zinf (Fin b) = true) by (cbn; apply Z.leb_le; lia).
            rewrite Hzg. cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 b) Hb).
            destruct (ub z2) as [zh| |] eqn:Eh.
            * assert (Hvleq_zinf : vz <= zh) by (pose proof Hvhi as HH; cbn in HH; lia).
              rewrite Hzlo2. cbn [addk_zinf mul_zinf]. eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ]. cbn. nia.
            * cbn [addk_zinf]. rewrite mul_zinf_fp by lia. rewrite Hzlo2. cbn. exact I.
            * congruence.
          + assert (Hzg : geq0_zinf (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
            rewrite Hzg. cbn [tymaxZ]. rewrite (proj2 (Z.leb_gt 0 b) Hb).
            rewrite Hzlo2. cbn [mul_zinf]. eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ]. cbn. nia.
        - cbn [tymaxZ geq0_zinf]. rewrite Hzlo2; cbn [addk_zinf]; rewrite mul_zinf_pinf_fp by lia; cbn; exact I.
        - cbn [tymaxZ]. exact I. }
      assert (Hcxu : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
        forall yhv, ub yF = Fin yhv -> leq_zinf (Fin (Z.quot yhv vz)) (ub (x s)) ->
        leq_zinf (Fin (Z.quot yhv vz)) (ub (x t))).
      { intros vz Hvlo Hvhi yhv Eyh Hxc.
        assert (Hbu : leq_zinf (Fin yhv) (tymaxZ (ub (x s)) vz)).
        { destruct (ub (x s)) as [b| |] eqn:Exu; cbn [tymaxZ].
          - cbn in Hxc. cbn. apply (tymax_ub b yhv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
          - exact I.
          - cbn in Hxc. contradiction. }
        assert (Hbl : leq_zinf (tyminZ (lb (x s)) vz) (Fin yhv)) by (rewrite <- Eyh; apply (Hhyf vz Hvlo Hvhi)).
        assert (Hy1 : leq_zinf (lb (sy3 s)) (Fin yhv)) by (rewrite <- Eyh; exact Hyfhi_lo).
        assert (Hy2 : leq_zinf (Fin yhv) (ub (sy3 s))) by (rewrite <- Eyh; exact Hyfyh).
        destruct (Hattx vz yhv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [_ HH]. exact HH. }
      destruct (leqb_zinf (max_zinf (max_zinf (idivt3 (lb yF) (lb z2)) (idivt3 (lb yF) (ub z2)))
         (max_zinf (idivt3 (ub yF) (lb z2)) (idivt3 (ub yF) (ub z2)))) (ub (x s))) eqn:Hclip.
      - apply leq_zinf_prop_bool_equiv in Hclip.
        eapply leq_zinf_trans; [ apply min_zinf_leq_zinf_r | ].
        destruct (ub yF) as [yhv| |] eqn:Eyh.
        + assert (Hchl : leq_zinf (idivt3 (Fin yhv) (lb z2)) (ub (x s))).
          { eapply leq_zinf_trans; [ | exact Hclip ]. eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r]. apply leq_zinf_max_zinf_l. }
          assert (Hchh : leq_zinf (idivt3 (Fin yhv) (ub z2)) (ub (x s))).
          { eapply leq_zinf_trans; [ | exact Hclip ]. eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r]. apply leq_zinf_max_zinf_r. }
          assert (HA : leq_zinf (max_zinf (idivt3 (Fin yhv) (lb z2)) (idivt3 (Fin yhv) (ub z2))) (ub (x t))).
          { apply max_zinf_lub.
            - rewrite Hzlo2 in Hchl |- *. cbn [idivt3] in Hchl |- *. apply (Hcxu zlo2 Hzlo2lo Hzlo2hi yhv eq_refl Hchl).
            - destruct (ub z2) as [zh| |] eqn:Eh.
              + cbn [idivt3] in Hchh |- *. apply (Hcxu zh Hz2ne (leq_zinf_refl _) yhv eq_refl Hchh).
              + cbn [idivt3] in Hchh |- *.
                assert (Hq0 : Z.quot yhv (Z.max zlo2 (Z.abs yhv + 1)) = 0).
                { destruct (Z.le_gt_cases 0 yhv) as [Hp|Hn].
                  - apply Z.quot_small. lia.
                  - replace yhv with (- (- yhv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                rewrite <- Hq0. apply (Hcxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _) yhv eq_refl).
                rewrite Hq0. exact Hchh.
              + congruence. }
          apply max_zinf_lub; [ | exact HA ].
          eapply leq_zinf_trans; [ | exact HA ].
          apply max_zinf_lub.
          * eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ]. rewrite Hzlo2. apply idivt3_mono_pos; [exact Hyfne | lia].
          * eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ].
            destruct (ub z2) as [zh| |] eqn:Eh; [ apply idivt3_mono_pos; [exact Hyfne | ] | apply leq_zinf_refl | congruence ].
            pose proof Hzlo2hi as HH; cbn in HH; lia.
        + assert (Hzp : forall x, max_zinf x Pinf = Pinf) by (intros [?| |]; reflexivity).
          assert (Ep : idivt3 Pinf (Fin zlo2) = Pinf) by (cbn [idivt3]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
          rewrite Hzlo2, Ep. cbn [max_zinf]. rewrite Hzp.
          assert (Hxp : ub (x s) = Pinf).
          { pose proof Hclip as HC. rewrite Hzlo2, Ep in HC. cbn [max_zinf] in HC. rewrite Hzp in HC. destruct (ub (x s)) eqn:E; try reflexivity; cbn in HC; contradiction. }
          assert (Hyp : ub (sy3 s) = Pinf).
          { pose proof Hyfyh as HH. destruct (ub (sy3 s)) eqn:E; try reflexivity; cbn in HH; contradiction. }
          destruct (ub (x t)) as [M| |] eqn:EtH; [ | exact I | ].
          2:{ exfalso. pose proof (contains_hi (x t) fx Hftx) as HH. rewrite EtH in HH. cbn in HH. exact HH. }
          exfalso.
          destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy0 [Hmy0 [Hby1 Hby2]]].
          set (vy := Z.max vy0 ((M+1) * zlo2)).
          assert (Hmemy : contains (sy3 s) vy).
          { split; [eapply leq_zinf_trans; [apply (contains_lo _ _ Hmy0) | ]; cbn; unfold vy; lia | rewrite Hyp; exact I]. }
          assert (Hbl : leq_zinf (tyminZ (lb (x s)) zlo2) (Fin vy)) by (eapply leq_zinf_trans; [exact Hby1 | ]; cbn; unfold vy; lia).
          assert (Hbu : leq_zinf (Fin vy) (tymaxZ (ub (x s)) zlo2)) by (rewrite Hxp; cbn; exact I).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
          pose proof (contains_hi (x t) _ Hmxt) as HH. rewrite EtH in HH. cbn in HH.
          assert (Hqge : Z.quot ((M+1) * zlo2) zlo2 <= Z.quot vy zlo2) by (apply Z.quot_le_mono; [lia | unfold vy; lia]).
          rewrite Z.quot_mul in Hqge by lia. lia.
        + pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
      - eapply leq_zinf_trans; [ apply leq_zinf_min_zinf_l | ].
        assert (Hzlp : forall x, leqb_zinf x Pinf = true) by (intros [?| |]; reflexivity).
        destruct (ub (x s)) as [xu| |] eqn:Exu; [ | rewrite Hzlp in Hclip; discriminate | congruence ].
        assert (Hclipxu : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
          leq_zinf (Fin (xu + 1)) (idivt3 (ub yF) (Fin vz)) -> leq_zinf (Fin xu) (ub (x t))).
        { intros vz Hvlo Hvhi Hcorner.
          pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
          destruct (attain_vx_hi (lb (x s)) (Fin xu) vz xu ltac:(pose proof (Hv1 vz Hvlo); lia) Hxle (leq_zinf_refl _)) as (Hbl & Hbu & Hqeq).
          set (vy := if 0 <=? xu then (xu + 1) * vz - 1 else xu * vz) in *.
          assert (Hvylo : leq_zinf (lb (sy3 s)) (Fin vy)) by (unfold vy; cbn [tymaxZ] in Hb2; exact Hb2).
          assert (Hvyhi : leq_zinf (Fin vy) (ub (sy3 s))).
          { eapply leq_zinf_trans; [ | exact Hyfyh ].
            destruct (ub yF) as [yhv| |] eqn:Eyh.
            - cbn [idivt3] in Hcorner. cbn in Hcorner. cbn.
              destruct (Z.lt_ge_cases vy yhv) as [H|H]; [lia | exfalso].
              pose proof (Z.quot_le_mono yhv vy vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
            - exact I.
            - pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
          destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [_ HH]. rewrite Hqeq in HH. exact HH. }
        assert (Hbfu : forall X a, leqb_zinf X (Fin a) = false -> leq_zinf (Fin (a + 1)) X).
        { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | exact I | discriminate ]. }
        destruct (leqb_zinf (idivt3 (ub yF) (lb z2)) (Fin xu)) eqn:Ehl.
        + destruct (ub z2) as [zh| |] eqn:Eh.
          * apply (Hclipxu zh Hz2ne (leq_zinf_refl _)).
            destruct (leqb_zinf (idivt3 (ub yF) (Fin zh)) (Fin xu)) eqn:Ehh.
            -- exfalso. apply leq_zinf_prop_bool_equiv in Ehl, Ehh.
               assert (Hle : leq_zinf (max_zinf (max_zinf (idivt3 (lb yF) (lb z2)) (idivt3 (lb yF) (Fin zh)))
                 (max_zinf (idivt3 (ub yF) (lb z2)) (idivt3 (ub yF) (Fin zh)))) (Fin xu)).
               { apply max_zinf_lub; apply max_zinf_lub; try assumption.
                 - eapply leq_zinf_trans; [ | exact Ehl ]. rewrite Hzlo2. apply idivt3_mono_pos; [exact Hyfne | lia].
                 - eapply leq_zinf_trans; [ | exact Ehh ]. apply idivt3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia]. }
               apply leq_zinf_prop_bool_equiv in Hle. rewrite Hle in Hclip. discriminate.
            -- apply Hbfu. exact Ehh.
          * destruct (Z.le_gt_cases 0 xu) as [Hxu0|Hxu0].
            -- exfalso. apply leq_zinf_prop_bool_equiv in Ehl.
               assert (Hle : leq_zinf (max_zinf (max_zinf (idivt3 (lb yF) (lb z2)) (idivt3 (lb yF) Pinf))
                 (max_zinf (idivt3 (ub yF) (lb z2)) (idivt3 (ub yF) Pinf))) (Fin xu)).
               { apply max_zinf_lub; apply max_zinf_lub.
                 - eapply leq_zinf_trans; [ | exact Ehl ]. rewrite Hzlo2. apply idivt3_mono_pos; [exact Hyfne | lia].
                 - cbn [idivt3]. cbn. lia.
                 - exact Ehl.
                 - cbn [idivt3]. cbn. lia. }
               apply leq_zinf_prop_bool_equiv in Hle. rewrite Hle in Hclip. discriminate.
            -- destruct (ub yF) as [yhv| |] eqn:Eyh.
               ++ apply (Hclipxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                  cbn [idivt3].
                  assert (Hq0 : Z.quot yhv (Z.max zlo2 (Z.abs yhv + 1)) = 0).
                  { destruct (Z.le_gt_cases 0 yhv) as [Hp|Hn].
                    - apply Z.quot_small. lia.
                    - replace yhv with (- (- yhv)) by lia. rewrite Z.quot_opp_l by lia. rewrite Z.quot_small; lia. }
                  rewrite Hq0. cbn. lia.
               ++ apply (Hclipxu (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                  cbn [idivt3]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). exact I.
               ++ pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
          * congruence.
        + apply (Hclipxu zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ehl. apply Hbfu. exact Ehl. }
  - (* ===== Y-COMPONENT (goal 2) ===== *)
    apply leq_zitv_intro.
    + (* --- y-lower --- *)
      destruct (lb yF) as [vlo| |] eqn:Eylo.
      2:{ pose proof (nonempty_bounds _ EY) as [HH _]; congruence. }
      2:{ assert (Hlo0 : lb (sy3 s) = Ninf) by (destruct (lb (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyl; contradiction).
          assert (Hzm : forall x, max_zinf Ninf x = x) by (intros [?| |]; reflexivity).
          rewrite HyF in Eylo; cbn [lb] in Eylo; rewrite Hlo0, Hzm in Eylo.
          destruct (lb (sy3 t)) as [M| |] eqn:EtL; [ | | exact I ].
          2:{ exfalso. pose proof (contains_lo (sy3 t) fy Hfty) as HH. rewrite EtL in HH. cbn in HH. exact HH. }
          exfalso.
          assert (HMfy : M <= fy) by (pose proof (contains_lo (sy3 t) fy Hfty) as HH; rewrite EtL in HH; cbn in HH; exact HH).
          assert (Hfyhi : leq_zinf (Fin fy) (ub (sy3 s))) by (apply (contains_hi _ _ Hfym)).
          destruct (lb (x s)) as [a| |] eqn:Exl.
          + cbn [ispos_zinf] in Eylo. destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
            * rewrite (proj2 (Z.ltb_lt 0 a) Ha) in Eylo. rewrite Hzlo2 in Eylo.
              destruct (ub z2) as [zh| |] eqn:Eh.
              -- cbn in Eylo. discriminate.
              -- rewrite mul_zinf_fp in Eylo by lia. cbn in Eylo. discriminate.
              -- congruence.
            * rewrite (proj2 (Z.ltb_ge 0 a) Ha) in Eylo. rewrite Hzlo2 in Eylo.
              destruct (ub z2) as [zh| |] eqn:Eh.
              -- cbn in Eylo. discriminate.
              -- set (vz := Z.max zlo2 (Z.max 1 (2 - M))).
                 assert (HB1 : leq_zinf (lb z2) (Fin vz)) by (rewrite Hzlo2; cbn; unfold vz; lia).
                 assert (HB2 : leq_zinf (Fin vz) Pinf) by apply leq_zinf_Pinf.
                 set (vy := (a-1)*vz+1).
                 assert (HvyM : vy <= M - 1) by (unfold vy, vz; nia).
                 assert (Hmemy : contains (sy3 s) vy).
                 { split; [rewrite Hlo0; exact I | eapply leq_zinf_trans'; [ | exact Hfyhi]; cbn; lia]. }
                 assert (Htymin : leq_zinf (tyminZ (Fin a) vz) (Fin vy)).
                 { cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha). unfold vy. cbn. lia. }
                 assert (Htymax : leq_zinf (Fin vy) (tymaxZ (ub (x s)) vz)).
                 { pose proof (band_ne (Fin a) (ub (x s)) vz (Hv1 vz HB1) Hxle) as Hbn.
                   assert (Etm : tyminZ (Fin a) vz = Fin vy) by (cbn; rewrite (proj2 (Z.ltb_ge 0 a) Ha); unfold vy; reflexivity).
                   rewrite Etm in Hbn. exact Hbn. }
                 destruct (Hwit vz vy HB1 HB2 Hmemy Htymin Htymax) as (_ & Hmyt & _).
                 pose proof (contains_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. lia.
              -- congruence.
          + congruence.
          + destruct (tymaxZ (ub (x s)) zlo2) as [tm| |] eqn:Etm.
            * set (vy := Z.min (M-1) tm).
              assert (Hmemy : contains (sy3 s) vy).
              { split; [rewrite Hlo0; exact I | eapply leq_zinf_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
              assert (Htymin : leq_zinf (tyminZ Ninf zlo2) (Fin vy)) by (cbn; exact I).
              assert (Htymax : leq_zinf (Fin vy) (tymaxZ (ub (x s)) zlo2)) by (rewrite Etm; cbn; unfold vy; lia).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (contains_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
            * set (vy := M-1).
              assert (Hmemy : contains (sy3 s) vy).
              { split; [rewrite Hlo0; exact I | eapply leq_zinf_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
              assert (Htymin : leq_zinf (tyminZ Ninf zlo2) (Fin vy)) by (cbn; exact I).
              assert (Htymax : leq_zinf (Fin vy) (tymaxZ (ub (x s)) zlo2)) by (rewrite Etm; apply leq_zinf_Pinf).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (contains_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
            * exfalso. apply (tymaxZ_not_Ninf (ub (x s)) zlo2 Hxun). exact Etm. }
      assert (Hex : exists vzs, leq_zinf (lb z2) (Fin vzs) /\ leq_zinf (Fin vzs) (ub z2) /\
        leq_zinf (tyminZ (lb (x s)) vzs) (Fin vlo) /\ leq_zinf (Fin vlo) (tymaxZ (ub (x s)) vzs)).
      { destruct (lb (x s)) as [a| |] eqn:Exl.
        - destruct (Z.lt_ge_cases 0 a) as [Ha|Ha].
          + exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
            pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
            pose proof (band_ne (Fin a) (ub (x s)) zlo2 Hzlo21 Hxle) as Hbn.
            assert (Hmin_zinf : min_zinf (mul_zinf (Fin a) (lb z2)) (mul_zinf (Fin a) (ub z2)) = Fin (a*zlo2)).
            { rewrite Hzlo2. destruct (ub z2) as [zhi2| |] eqn:Eh; [ | | congruence ].
              - cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.min_l by nia; reflexivity.
              - cbn. rewrite (proj2 (Z.eqb_neq a 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 a) Ha); reflexivity. }
            assert (Hzp : ispos_zinf (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
            assert (Etym : tyminZ (Fin a) zlo2 = Fin (a*zlo2)) by (cbn; rewrite (proj2 (Z.ltb_lt 0 a) Ha); reflexivity).
            split.
            * rewrite Etym, <- Eylo, HyF; cbn [lb]; rewrite Hzp, Hmin_zinf. apply leq_zinf_max_zinf_r.
            * rewrite <- Eylo, HyF; cbn [lb]; rewrite Hzp, Hmin_zinf.
              apply max_zinf_lub; [exact Hb2 | rewrite <- Etym; exact Hbn].
          + destruct (ub z2) as [zhi2| |] eqn:Eh.
            * assert (Hzhi2lo : leq_zinf (lb z2) (Fin zhi2)) by exact Hz2ne.
              exists zhi2. split; [exact Hzhi2lo | split; [apply leq_zinf_refl | ]].
              pose proof (Hband zhi2 Hzhi2lo (leq_zinf_refl _)) as [Hb1 Hb2].
              pose proof (band_ne (Fin a) (ub (x s)) zhi2 (Hv1 zhi2 Hzhi2lo) Hxle) as Hbn.
              assert (Hzp : ispos_zinf (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
              assert (Etym : tyminZ (Fin a) zhi2 = Fin ((a-1)*zhi2+1)) by (cbn; rewrite (proj2 (Z.ltb_ge 0 a) Ha); reflexivity).
              assert (Hmin_zinf : min_zinf (addk_zinf (mul_zinf (addk_zinf (Fin a) (-1)) (lb z2)) 1) (addk_zinf (mul_zinf (addk_zinf (Fin a) (-1)) (Fin zhi2)) 1) = Fin ((a-1)*zhi2+1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.min_r by nia; nia. }
              split.
              -- rewrite Etym, <- Eylo, HyF; cbn [lb]; rewrite Hzp, Hmin_zinf. apply leq_zinf_max_zinf_r.
              -- rewrite <- Eylo, HyF; cbn [lb]; rewrite Hzp, Hmin_zinf.
                 apply max_zinf_lub; [exact Hb2 | rewrite <- Etym; exact Hbn].
            * assert (Hzp: ispos_zinf (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
              assert (Hlbyf : lb yF = lb (sy3 s)).
              { rewrite HyF; cbn [lb]; rewrite Hzp, Hzlo2; cbn [addk_zinf];
                rewrite mul_zinf_fn by lia; cbn; destruct (lb (sy3 s)); reflexivity. }
              assert (Hyleq : lb (sy3 s) = Fin vlo) by (rewrite <- Hlbyf; exact Eylo).
              set (vzs := Z.max zlo2 (Z.max 1 (1 - vlo))).
              assert (Hvge : 1 - vlo <= vzs) by (unfold vzs; lia).
              assert (Hvz0 : 0 <= vzs) by (unfold vzs; lia).
              assert (HB1 : leq_zinf (lb z2) (Fin vzs)) by (rewrite Hzlo2; cbn; unfold vzs; lia).
              exists vzs. split; [exact HB1 | split; [apply leq_zinf_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply leq_zinf_Pinf)) as [Hb1 Hb2].
              split.
              -- cbn [tyminZ]. rewrite (proj2 (Z.ltb_ge 0 a) Ha). cbn. nia.
              -- rewrite Hyleq in Hb2. exact Hb2.
            * congruence.
        - congruence.
        - exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          assert (Hlbyf : lb yF = lb (sy3 s)).
          { rewrite HyF; cbn [lb ispos_zinf]; rewrite Hzlo2; cbn [addk_zinf];
            rewrite mul_zinf_ninf_fp by lia; cbn; destruct (lb (sy3 s)); reflexivity. }
          assert (Hyleq : lb (sy3 s) = Fin vlo) by (rewrite <- Hlbyf; exact Eylo).
          split; [ cbn [tyminZ]; exact I | rewrite Hyleq in Hb2; exact Hb2 ]. }
      destruct Hex as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vlo A B Hyfyl Hyflo_hi C D) as [HH _]. exact HH.
    + (* --- y-upper --- *)
      destruct (ub yF) as [vhi| |] eqn:Eyhi.
      2:{ assert (Hhi0 : ub (sy3 s) = Pinf) by (destruct (ub (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyh; contradiction).
          assert (HzM : forall x, min_zinf Pinf x = x) by (intros [?| |]; reflexivity).
          rewrite HyF in Eyhi; cbn [ub] in Eyhi; rewrite Hhi0, HzM in Eyhi.
          destruct (ub (sy3 t)) as [M| |] eqn:EtH; [ | exact I | ].
          2:{ exfalso. pose proof (contains_hi (sy3 t) fy Hfty) as HH. rewrite EtH in HH. cbn in HH. exact HH. }
          exfalso.
          assert (HfyM : fy <= M) by (pose proof (contains_hi (sy3 t) fy Hfty) as HH; rewrite EtH in HH; cbn in HH; exact HH).
          assert (Hfylo : leq_zinf (lb (sy3 s)) (Fin fy)) by (apply (contains_lo _ _ Hfym)).
          destruct (ub (x s)) as [xu| |] eqn:Exu.
          + cbn [geq0_zinf] in Eyhi. destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
            * rewrite (proj2 (Z.leb_le 0 xu) Hu) in Eyhi. rewrite Hzlo2 in Eyhi.
              destruct (ub z2) as [zh| |] eqn:Eh.
              -- cbn in Eyhi. discriminate.
              -- set (vz := Z.max zlo2 (Z.max 1 (M + 2))).
                 assert (HB1 : leq_zinf (lb z2) (Fin vz)) by (rewrite Hzlo2; cbn; unfold vz; lia).
                 assert (HB2 : leq_zinf (Fin vz) Pinf) by apply leq_zinf_Pinf.
                 set (vy := (xu+1)*vz-1).
                 assert (HvyM : M + 1 <= vy) by (unfold vy, vz; nia).
                 assert (Hmemy : contains (sy3 s) vy).
                 { split; [eapply leq_zinf_trans'; [exact Hfylo | ]; cbn; lia | rewrite Hhi0; exact I]. }
                 assert (Htymax : leq_zinf (Fin vy) (tymaxZ (Fin xu) vz)).
                 { cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 xu) Hu). unfold vy. cbn. lia. }
                 assert (Htymin : leq_zinf (tyminZ (lb (x s)) vz) (Fin vy)).
                 { pose proof (band_ne (lb (x s)) (Fin xu) vz (Hv1 vz HB1) Hxle) as Hbn.
                   assert (Etm : tymaxZ (Fin xu) vz = Fin vy) by (cbn; rewrite (proj2 (Z.leb_le 0 xu) Hu); unfold vy; reflexivity).
                   rewrite Etm in Hbn. exact Hbn. }
                 destruct (Hwit vz vy HB1 HB2 Hmemy Htymin Htymax) as (_ & Hmyt & _).
                 pose proof (contains_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. lia.
              -- congruence.
            * rewrite (proj2 (Z.leb_gt 0 xu) Hu) in Eyhi. rewrite Hzlo2 in Eyhi.
              destruct (ub z2) as [zh| |] eqn:Eh.
              -- cbn in Eyhi. discriminate.
              -- rewrite mul_zinf_fn in Eyhi by lia. cbn in Eyhi. discriminate.
              -- congruence.
          + destruct (tyminZ (lb (x s)) zlo2) as [tmn| |] eqn:Etm.
            * set (vy := Z.max (M+1) tmn).
              assert (Hmemy : contains (sy3 s) vy).
              { split; [eapply leq_zinf_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
              assert (Htymax : leq_zinf (Fin vy) (tymaxZ Pinf zlo2)) by (cbn [tymaxZ]; apply leq_zinf_Pinf).
              assert (Htymin : leq_zinf (tyminZ (lb (x s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; unfold vy; lia).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (contains_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
            * exfalso. apply (tyminZ_not_Pinf (lb (x s)) zlo2 Hxlp). exact Etm.
            * set (vy := M+1).
              assert (Hmemy : contains (sy3 s) vy).
              { split; [eapply leq_zinf_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
              assert (Htymax : leq_zinf (Fin vy) (tymaxZ Pinf zlo2)) by (cbn [tymaxZ]; apply leq_zinf_Pinf).
              assert (Htymin : leq_zinf (tyminZ (lb (x s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; exact I).
              destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Htymin Htymax) as (_ & Hmyt & _).
              pose proof (contains_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
          + congruence. }
      2:{ pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
      assert (Hexu : exists vzs, leq_zinf (lb z2) (Fin vzs) /\ leq_zinf (Fin vzs) (ub z2) /\
        leq_zinf (tyminZ (lb (x s)) vzs) (Fin vhi) /\ leq_zinf (Fin vhi) (tymaxZ (ub (x s)) vzs)).
      { destruct (ub (x s)) as [xu| |] eqn:Exu.
        - destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
          + destruct (ub z2) as [zhi2| |] eqn:Eh.
            * assert (Hzhi2lo : leq_zinf (lb z2) (Fin zhi2)) by exact Hz2ne.
              exists zhi2. split; [exact Hzhi2lo | split; [apply leq_zinf_refl | ]].
              pose proof (Hband zhi2 Hzhi2lo (leq_zinf_refl _)) as [Hb1 Hb2].
              pose proof (band_ne (lb (x s)) (Fin xu) zhi2 (Hv1 zhi2 Hzhi2lo) Hxle) as Hbn.
              assert (Hzge : geq0_zinf (Fin xu) = true) by (cbn; apply Z.leb_le; lia).
              assert (Etym : tymaxZ (Fin xu) zhi2 = Fin ((xu+1)*zhi2-1)) by (cbn; rewrite (proj2 (Z.leb_le 0 xu) Hu); reflexivity).
              assert (Hmax_zinf : max_zinf (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) (lb z2)) (-1)) (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) (Fin zhi2)) (-1)) = Fin ((xu+1)*zhi2-1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.max_r by nia; nia. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hzge, Hmax_zinf. apply leq_zinf_min_zinf_glb; [exact Hb1 | rewrite <- Etym; exact Hbn].
              -- rewrite Etym, <- Eyhi, HyF; cbn [ub]; rewrite Hzge, Hmax_zinf. rewrite <- Etym. apply min_zinf_leq_zinf_r.
            * assert (Hzge : geq0_zinf (Fin xu) = true) by (cbn; apply Z.leb_le; lia).
              assert (Hhi0 : ub yF = ub (sy3 s)).
              { rewrite HyF; cbn [ub]; rewrite Hzge, Hzlo2; cbn [addk_zinf];
                rewrite mul_zinf_fp by lia; cbn; destruct (ub (sy3 s)); reflexivity. }
              assert (Hyheq : ub (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
              set (vzs := Z.max zlo2 (Z.max 1 (vhi + 2))).
              assert (Hvge : vhi + 2 <= vzs) by (unfold vzs; lia).
              assert (Hvz0 : 0 <= vzs) by (unfold vzs; lia).
              assert (HB1 : leq_zinf (lb z2) (Fin vzs)) by (rewrite Hzlo2; cbn; unfold vzs; lia).
              exists vzs. split; [exact HB1 | split; [apply leq_zinf_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply leq_zinf_Pinf)) as [Hb1 Hb2].
              split.
              -- rewrite <- Hyheq. exact Hb1.
              -- cbn [tymaxZ]. rewrite (proj2 (Z.leb_le 0 xu) Hu). cbn. nia.
            * congruence.
          + exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
            pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
            pose proof (band_ne (lb (x s)) (Fin xu) zlo2 Hzlo21 Hxle) as Hbn.
            assert (Hzge : geq0_zinf (Fin xu) = false) by (cbn; apply Z.leb_gt; lia).
            assert (Etym : tymaxZ (Fin xu) zlo2 = Fin (xu*zlo2)) by (cbn; rewrite (proj2 (Z.leb_gt 0 xu) Hu); reflexivity).
            assert (Hmax_zinf : max_zinf (mul_zinf (Fin xu) (lb z2)) (mul_zinf (Fin xu) (ub z2)) = Fin (xu*zlo2)).
            { rewrite Hzlo2. destruct (ub z2) as [zhi2| |] eqn:Eh; [ | | congruence ].
              - cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia).
                rewrite Z.max_l by nia; reflexivity.
              - cbn. rewrite (proj2 (Z.eqb_neq xu 0) ltac:(lia)), (proj2 (Z.ltb_ge 0 xu) ltac:(lia)); reflexivity. }
            split.
            -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hzge, Hmax_zinf. apply leq_zinf_min_zinf_glb; [exact Hb1 | rewrite <- Etym; exact Hbn].
            -- rewrite Etym, <- Eyhi, HyF; cbn [ub]; rewrite Hzge, Hmax_zinf. rewrite <- Etym. apply min_zinf_leq_zinf_r.
        - assert (Hhi0 : ub yF = ub (sy3 s)).
          { rewrite HyF; cbn [ub geq0_zinf]; rewrite Hzlo2; cbn [addk_zinf];
            rewrite mul_zinf_pinf_fp by lia; cbn; destruct (ub (sy3 s)); reflexivity. }
          assert (Hyheq : ub (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
          exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          split.
          -- rewrite <- Hyheq. exact Hb1.
          -- cbn [tymaxZ]. apply leq_zinf_Pinf.
        - congruence. }
      destruct Hexu as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vhi A B Hyfhi_lo Hyfyh C D) as [_ HH]. exact HH.
  - (* ===== Z-COMPONENT (goal 3) ===== *)
    apply leq_zitv_intro.
    + destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy [Hmy [Hby1 Hby2]]].
      destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmy Hby1 Hby2) as (_ & _ & Hmzt).
      rewrite Hzlo2. apply (contains_lo (sz3 t) zlo2 Hmzt).
    + destruct (ub z2) as [zhi2| |] eqn:Ehz2.
      * assert (Hlo : leq_zinf (lb z2) (Fin zhi2)) by exact Hz2ne.
        destruct (Hpickvy zhi2 Hlo (leq_zinf_refl _)) as [vy [Hmy [Hby1 Hby2]]].
        destruct (Hwit zhi2 vy Hlo (leq_zinf_refl _) Hmy Hby1 Hby2) as (_ & _ & Hmzt).
        apply (contains_hi (sz3 t) zhi2 Hmzt).
      * destruct (ub (sz3 t)) as [M| |] eqn:Eht.
        -- exfalso.
           assert (Hvzlo : leq_zinf (lb z2) (Fin (Z.max zlo2 (M+1)))) by (rewrite Hzlo2; cbn; lia).
           assert (Hvzhi : leq_zinf (Fin (Z.max zlo2 (M+1))) Pinf) by apply leq_zinf_Pinf.
           destruct (Hpickvy (Z.max zlo2 (M+1)) Hvzlo Hvzhi) as [vy [Hmy [Hby1 Hby2]]].
           destruct (Hwit (Z.max zlo2 (M+1)) vy Hvzlo Hvzhi Hmy Hby1 Hby2) as (_ & _ & Hmzt).
           pose proof (contains_hi (sz3 t) _ Hmzt) as HH. rewrite Eht in HH. cbn in HH. lia.
        -- apply leq_zinf_Pinf.
        -- exfalso. pose proof (contains_hi (sz3 t) fz Hftz) as HH. rewrite Eht in HH. cbn in HH. exact HH.
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
  assert (Es : ne_zitv3 s = true) by (eapply ne_zitv3_true; exact Hfin).
  destruct (ne_zitv3_parts s Es) as (Esx & Esy & Esz).
  assert (HneOut : ne_zitv3 (ztdiv4 s) = true)
    by (eapply ne_zitv3_true; apply ztdiv4_soundness; [exact Hfin | exact Hfts]).
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
      assert (Esx' : is_not_bot_zitv (x (mir_xz s)) = true)
        by (unfold mir_xz; cbn [x]; rewrite isbot_mirror; exact Esx).
      assert (Esy' : is_not_bot_zitv (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
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
  ne_zitv3 (ztdiv4 s) = true -> feasible3 tsol s.
Proof.
  intros s Hne. unfold ztdiv4 in Hne.
  destruct (ne_zitv3 s) eqn:Es; [ | cbn in Hne; congruence ].
  cbn [negb] in Hne.
  destruct (ne_zitv3_parts s Es) as (Esx & Esy & Esz).
  unfold join4 in Hne.
  destruct (ne_zitv3 (ztdiv_pos3 s)) eqn:Ep; cbn [negb] in Hne.
  - destruct (tpos_ne_feasible s Esx Esy Ep) as (vx & vy & vz & Hin & Hts & Hvz).
    exists vx, vy, vz. split; assumption.
  - rewrite ne_mir_xz in Hne.
    assert (Esx' : is_not_bot_zitv (x (mir_xz s)) = true)
      by (unfold mir_xz; cbn [x]; rewrite isbot_mirror; exact Esx).
    assert (Esy' : is_not_bot_zitv (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
    destruct (tpos_ne_feasible (mir_xz s) Esx' Esy' Hne) as (vx & vy & vz & Hin & Hts & Hvz).
    exists (- vx), vy, (- vz).
    split; [ apply in_mir_xz_inv; exact Hin | apply tsol_mir; exact Hts ].
Qed.

Theorem ztdiv4_complete : forall s t, contains3 tsol s t -> sle3 (ztdiv4 s) t.
Proof.
  intros s t Hct. destruct (ne_zitv3 (ztdiv4 s)) eqn:E;
    [ exact (ztdiv4_best_feasible s (ztdiv4_ne_feasible s E) t Hct) | apply sle3_bot; exact E ].
Qed.
(* Floor *)


(* [zitv.v] already provides the extended tests [ispos_zinf] ("> 0"), [isneg_zinf] ("< 0")
   and [iszero_zinf] ("= 0"); we reuse them here. *)

(* same_sign(x, y) := (x < 0) == (y < 0) *)
Definition same_sign3 (a b : zinf) : bool := Bool.eqb (isneg_zinf a) (isneg_zinf b).

(* compact, C++-faithful extended multiplication *)
Definition mul_zinf' (a b : zinf) : zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x * y)                     (* both finite *)
  | _, _ => if iszero_zinf a || iszero_zinf b then Fin 0    (* 0 * oo = 0  *)
            else if same_sign3 a b then Pinf else Ninf
  end.

(* one-Z-variable mixed cases (finite x infinite): after ruling out the finite
   zero, split its sign both ways; [cbn] then reduces the boolean [eqb]s and the
   RHS sign tests, and the two impossible sign combinations die by [lia]. *)
Ltac mix_case v :=
  destruct (Z.eqb_spec v 0) as [->|?]; cbn; [reflexivity|];
  unfold same_sign3, isneg_zinf; cbn;
  destruct (Z.ltb_spec v 0) as [?|?];
  destruct (Z.ltb_spec 0 v) as [?|?];
  cbn; first [ reflexivity | exfalso; lia ].

(* the compact version is exactly [zitv.v]'s [mul_zinf] *)
Theorem mul_zinf'_eq : forall a b, mul_zinf' a b = mul_zinf a b.
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

Definition idivt3' (a b : zinf) : zinf :=
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
    The "a > 0"/"a < 0" tests are [zitv.v]'s extended [ispos_zinf]/[isneg_zinf].

    [zitv.v]'s [cdiv_zinf] spells out the constructor pairs; here we prove the
    compact rendering is the SAME function. *)

Definition cdiv_zinf' (a b : zinf) : zinf :=
  match a, b with
  | Fin x, Fin y => Fin (cdiv x y)                 (* both finite: cdiv(a, b) *)
  | _, Pinf => if ispos_zinf a then Fin 1 else Fin 0     (* b = +oo : a > 0 ? 1 : 0 *)
  | _, Ninf => if isneg_zinf a then Fin 1 else Fin 0     (* b = -oo : a < 0 ? 1 : 0 *)
  | _, Fin w => if 0 <? w then a else ineg3 a      (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [zitv.v]'s [cdiv_zinf]; the finite/infinite
   corners need to move [Fin] across the [if] (ispos_zinf/isneg_zinf vs a folded [Fin]). *)
Theorem cdiv_zinf'_eq : forall a b, cdiv_zinf' a b = cdiv_zinf a b.
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
    The "a < 0"/"a > 0" tests are [zitv.v]'s extended [isneg_zinf]/[ispos_zinf].

    [zitv.v]'s [fdiv_zinf] spells out the constructor pairs; here we prove the
    compact rendering is the SAME function. *)

Definition fdiv_zinf' (a b : zinf) : zinf :=
  match a, b with
  | Fin x, Fin y => Fin (x / y)                     (* both finite: fdiv(a, b) *)
  | _, Pinf => if isneg_zinf a then Fin (-1) else Fin 0   (* b = +oo : a < 0 ? -1 : 0 *)
  | _, Ninf => if ispos_zinf a then Fin (-1) else Fin 0   (* b = -oo : a > 0 ? -1 : 0 *)
  | _, Fin w => if 0 <? w then a else ineg3 a       (* b finite, a = +/-oo     *)
  end.

(* the compact version is exactly [zitv.v]'s [fdiv_zinf] *)
Theorem fdiv_zinf'_eq : forall a b, fdiv_zinf' a b = fdiv_zinf a b.
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
Lemma fdiv_zinf_neg_cdiv_zinf : forall x y, fdiv_zinf x y = ineg3 (cdiv_zinf (ineg3 x) y).
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
      - [<x=tdiv(y,z)> = <tdiv+> ⊔ (isneg_zinf_xz o <tdiv+> o isneg_zinf_xz)] = [ztdiv4]
                        (the two z-sign slices joined bottom-aware by [join4]).

    Two transcription slips in the figure (read against the verified code):
      (1) the X-step is written [d(x) <- fdiv+(d(y),d(z))] but must be [tdiv+]:
          a floor corner is UNSOUND here -- e.g. on x=[0,0], y=[-1,-1], z=[2,2]
          the solution (0,-1,2) (trunc(-1/2)=0) is lost because floor(-1/2)=-1
          drives x to [-1,-1] n [0,0] = bot; the truncated corner keeps it;
      (2) [tden+]'s else-branch numerator [ceil((xu-1)/(xl-1))] should read
          [ceil((yu-1)/(xl-1))] (yu, not xu), matching [ztdiv_pos3].
    With those corrections the figure is [ztdiv4] verbatim. *)

Definition ztdiv_simpl (s : zitv3) : zitv3 := ztdiv4 s.

Definition seq3 (a b : zitv3) : Prop := sle3 a b /\ sle3 b a.

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
