(** * div4: the four division propagators with INFINITE bounds

    Rocq model of the C++ [ztdiv_4]/[zfdiv_4]/[zcdiv_4]/[zediv_4]
    (zinterval.hpp): one-pass slice decomposition.  Only two positive-slice
    solvers are needed ([zfdiv_pos3] and [ztdiv_pos3], mirroring the C++
    [zfdiv_pos]/[ztdiv_pos]); every other case reduces to them through the
    mirror identities
      trunc(y/z) = -trunc(y/(-z))        floor(y/z) = floor((-y)/(-z))
      ceil(y/z)  = -floor((-y)/z)        ceil(y/z)  = -floor(y/(-z))
    applied by mirroring the intervals of x, y and/or z ([mirror_i], the C++
    [zmirror]).  The two slices are then joined ([join4]).

    Proved properties, following the paper's terminology:
      - soundness    : [z*div4_soundness]    (no solution is lost)
      - completeness : [z*div4_complete]     (a.k.a. optimality/best: the
        output is below every store containing the solutions), together with
        [z*div4_ne_feasible] (a non-empty output implies a solution exists),
        which extends completeness to infeasible inputs in the quotient
        lattice where all empty stores are identified with bottom.

    The Zinf interval infrastructure ([Zinf], [itv], [store3], the
    infinity-aware helpers [addk_zinf]/[mul_zinf]/[fdiv_zinf]/[cdiv_zinf]) is reused from
    [fdiv3]; none of that file's admitted theorems is used here. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import Concrete Zinf itv.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Additional helpers: truncated corner division, mirroring        *)
(* ------------------------------------------------------------------ *)

(* trunc(n/m) with limit semantics (precondition of use: m <> Fin 0);
   mirrors the C++ [idiv_t]. *)
Definition ineg3 (a : Zinf) : Zinf :=
  match a with Fin v => Fin (- v) | Pinf => Ninf | Ninf => Pinf end.

(* [l, u] := [-u, -l]; mirrors the C++ [zmirror] (bot maps to bot). *)
Definition mirror_i (i : itv) : itv := Itv (ineg3 (ub i)) (ineg3 (lb i)).

(* the three mirroring patterns used by the wrappers *)
Definition mir_yz (s : store3) : store3 :=
  St3 (sx3 s) (mirror_i (sy3 s)) (mirror_i (sz3 s)).
Definition mir_xy (s : store3) : store3 :=
  St3 (mirror_i (sx3 s)) (mirror_i (sy3 s)) (sz3 s).
Definition mir_xz (s : store3) : store3 :=
  St3 (mirror_i (sx3 s)) (sy3 s) (mirror_i (sz3 s)).

(* remaining sign tests on Zinf (sentinel encoding of the C++ comparisons) *)
Definition zeqm1 (a : Zinf) : bool :=
  match a with Fin v => v =? -1 | _ => false end.

(* the C++ meet_bot: both bounds to their bottom *)
Definition botitv : itv := Itv Pinf Ninf.

(* ------------------------------------------------------------------ *)
(** ** The two positive-slice solvers                                  *)
(* ------------------------------------------------------------------ *)

(** Contracts x, y, z for x = fdiv(y, z) on the positive slice of z
    (z first met with [1, +oo]); mirrors the C++ [zfdiv_pos] line by line:
      Z: the feasible z form a contiguous range computed exactly from the
         band  fdiv(y, z) in [xl, xu]  <=>  y in [xl*z, (xu+1)*z - 1];
      Y: hull of the band endpoints over the narrowed z;
      X: 4-corner floor hull over the narrowed y, z. *)
Definition zfdiv_pos3 (s : store3) : store3 :=
  let x := sx3 s in let y := sy3 s in
  let z := Itv (max_zinf (lb (sz3 s)) (Fin 1)) (ub (sz3 s)) in
  if negb (nonempty3b z) then St3 x y z else
  (* Z: x.lb * z <= y.ub *)
  let z :=
    if ispos_zinf (lb x) then Itv (lb z) (min_zinf (ub z) (fdiv_zinf (ub y) (lb x)))
    else if negb (iszero_zinf (lb x)) then
      Itv (max_zinf (lb z) (cdiv_zinf (ub y) (lb x))) (ub z)
    else if isneg_zinf (ub y) then botitv else z in
  (* Z: (x.ub + 1) * z >= y.lb + 1 *)
  let z :=
    if geq0_zinf (ub x) then
      Itv (max_zinf (lb z) (cdiv_zinf (addk_zinf (lb y) 1) (addk_zinf (ub x) 1))) (ub z)
    else if negb (zeqm1 (ub x)) then
      Itv (lb z) (min_zinf (ub z) (fdiv_zinf (addk_zinf (lb y) 1) (addk_zinf (ub x) 1)))
    else if geq0_zinf (lb y) then botitv else z in
  if negb (nonempty3b z) then St3 x y z else
  (* Y: hull of [x.lb*z, (x.ub+1)*z - 1] over the narrowed z *)
  let y := Itv
    (max_zinf (lb y) (min_zinf (mul_zinf (lb x) (lb z)) (mul_zinf (lb x) (ub z))))
    (min_zinf (ub y) (max_zinf (addk_zinf (mul_zinf (addk_zinf (ub x) 1) (lb z)) (-1))
                        (addk_zinf (mul_zinf (addk_zinf (ub x) 1) (ub z)) (-1)))) in
  if negb (nonempty3b y) then St3 x y z else
  (* X: 4-corner hull of fdiv(y, z) *)
  let x := Itv
    (max_zinf (lb x) (min_zinf (min_zinf (fdiv_zinf (lb y) (lb z)) (fdiv_zinf (lb y) (ub z)))
                        (min_zinf (fdiv_zinf (ub y) (lb z)) (fdiv_zinf (ub y) (ub z)))))
    (min_zinf (ub x) (max_zinf (max_zinf (fdiv_zinf (lb y) (lb z)) (fdiv_zinf (lb y) (ub z)))
                        (max_zinf (fdiv_zinf (ub y) (lb z)) (fdiv_zinf (ub y) (ub z))))) in
  St3 x y z.

(** Contracts x, y, z for x = tdiv(y, z) on the positive slice of z;
    mirrors the C++ [ztdiv_pos]:
      band  tdiv(y, z) in [xl, xu]  <=>  y in [tymin(xl, z), tymax(xu, z)]
      with tymin(v, z) = v > 0 ? v*z : (v-1)*z + 1
      and  tymax(v, z) = v >= 0 ? (v+1)*z - 1 : v*z. *)
Definition join4 (pos neg : store3) : store3 :=
  if negb (ne_store3 pos) then neg
  else if negb (ne_store3 neg) then pos
  else sjoin3 pos neg.

Definition zfdiv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (zfdiv_pos3 s) (mir_yz (zfdiv_pos3 (mir_yz s))).

Definition zcdiv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (mir_xy (zfdiv_pos3 (mir_xy s))) (mir_xz (zfdiv_pos3 (mir_xz s))).

Definition zediv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (zfdiv_pos3 s) (mir_xz (zfdiv_pos3 (mir_xz s))).

(* ------------------------------------------------------------------ *)
(** ** Truncated division expressed through the FLOOR solver           *)
(*     (mirrors the C++ [ztdiv_pos_f] / [ztdiv_5])                     *)
(* ------------------------------------------------------------------ *)

(* Positive-z slice of x = tdiv(y, z) via [zfdiv_pos3].  For z >= 1
   truncation toward zero equals floor on y >= 0 and ceil on y < 0, and
   ceil(y, z) = -floor(-y, z); so split y at 0, run the floor solver on each
   part (mirroring x, y on the negative part, where trunc = ceil) and join.
   (The z := z /\ [1, +oo] restriction is applied inside [zfdiv_pos3].) *)
Definition csol (x y z : Z) : Prop := z <> 0 /\ x = cdiv y z.
Definition esol (x y z : Z) : Prop :=
  z <> 0 /\ x = (if 0 <? z then y / z else cdiv y z).

(* generic containment/feasibility [contains3]/[feasible3] are provided by itv. *)

(* ------------------------------------------------------------------ *)
(** ** Positive-slice theorems (the proof core)

    Everything below reduces to these six statements about the two
    positive-slice solvers, restricted to the solutions with vz >= 1. *)
(* ------------------------------------------------------------------ *)

Definition slice_feasible (P : Z -> Z -> Z -> Prop) (s : store3) : Prop :=
  exists vx vy vz, in_store3 s vx vy vz /\ P vx vy vz /\ 1 <= vz.
Definition slice_contains (P : Z -> Z -> Z -> Prop) (s t : store3) : Prop :=
  forall vx vy vz, in_store3 s vx vy vz -> P vx vy vz -> 1 <= vz ->
  in_store3 t vx vy vz.

(* fpos_best and fpos_ne_feasible are proved below, after tpos_best,
   where all their support lemmas are available. *)

(* ================================================================== *)
(** Support lemmas for the truncated positive-slice soundness proof
    ([tpos_sound]).  Reusable arithmetic bridges (floor/ceil vs Z.quot),
    the band lemmas, corner-hull brackets, and step combinators *)
(* ================================================================== *)

(* ================= arithmetic bridge lemmas ================= *)
(* floor, positive divisor *)
Lemma F1 : forall n d q, 0 < d -> d*q <= n -> q <= n / d.
Proof. intros; apply Z.div_le_lower_bound; auto. Qed.
(* floor, negative divisor *)
Lemma FN1 : forall n d q, d < 0 -> n <= d*q -> q <= n / d.
Proof.
  intros n d q Hd Hle.
  rewrite <- (Z.div_opp_opp n d) by lia.
  apply Z.div_le_lower_bound; lia.
Qed.
(* ceil = cdiv, positive divisor *)
Lemma CC1 : forall n d q, 0 < d -> n <= d*q -> cdiv n d <= q.
Proof.
  intros n d q Hd Hle. unfold cdiv.
  assert (H: - q <= (- n) / d) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.
(* ceil = cdiv, negative divisor *)
Lemma C1 : forall n d q, d < 0 -> d*q <= n -> cdiv n d <= q.
Proof.
  intros n d q Hd Hle. unfold cdiv.
  rewrite <- (Z.div_opp_opp (-n) d) by lia.
  assert (H: - q <= (- - n) / (- d)) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

(* ================= band lemmas for truncated division (z>0) ================= *)
(* tymin v z = min y with Z.quot y z >= v ; tymax v z = max y with Z.quot y z <= v *)

Lemma leq_zinf_max_zinf_r : forall a b, leq_zinf b (max_zinf a b).
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.
Lemma min_zinf_leq_zinf_r : forall a b, leq_zinf (min_zinf a b) b.
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.
Lemma leq_zinf_trans' : forall a b c, leq_zinf a b -> leq_zinf b c -> leq_zinf a c.
Proof. exact leq_zinf_trans. Qed.

(* ===== corner bracket lemmas for the X step ===== *)
Lemma mem3_narrow_hi : forall lo hi B v,
  leq_zinf lo (Fin v) -> leq_zinf (Fin v) hi -> leq_zinf (Fin v) B ->
  mem3 (Itv lo (min_zinf hi B)) v.
Proof. intros; unfold mem3; cbn [lb ub]; split; [assumption | apply leq_zinf_min_zinf_glb; assumption]. Qed.
Lemma mem3_narrow_lo : forall lo hi B v,
  leq_zinf lo (Fin v) -> leq_zinf (Fin v) hi -> leq_zinf B (Fin v) ->
  mem3 (Itv (max_zinf lo B) hi) v.
Proof. intros; unfold mem3; cbn [lb ub]; split; [apply max_zinf_lub; assumption | assumption]. Qed.

(* ===== Z-step obligations ===== *)
(* Z1: tymin(x.lb,z) <= y.ub  --> refine z *)
Lemma mul_zinf_fp : forall a, 0 < a -> mul_zinf (Fin a) Pinf = Pinf.
Proof. intros a Ha. cbn. rewrite (proj2 (Z.eqb_neq a 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 a) Ha). reflexivity. Qed.
Lemma mul_zinf_fn : forall a, a < 0 -> mul_zinf (Fin a) Pinf = Ninf.
Proof. intros a Ha. cbn. rewrite (proj2 (Z.eqb_neq a 0) ltac:(lia)), (proj2 (Z.ltb_ge 0 a) ltac:(lia)). reflexivity. Qed.
Lemma mul_zinf_ninf_fp : forall z, 0 < z -> mul_zinf Ninf (Fin z) = Ninf.
Proof. intros z Hz. cbn. rewrite (proj2 (Z.eqb_neq z 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 z) Hz). reflexivity. Qed.
Lemma mul_zinf_pinf_fp : forall z, 0 < z -> mul_zinf Pinf (Fin z) = Pinf.
Proof. intros z Hz. cbn. rewrite (proj2 (Z.eqb_neq z 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 z) Hz). reflexivity. Qed.

(* ===== Y-step obligations (abstract over the narrowed z-interval iz) ===== *)
Lemma mem3_narrow_both : forall lo hi Bl Bh v,
  leq_zinf lo (Fin v) -> leq_zinf (Fin v) hi -> leq_zinf Bl (Fin v) -> leq_zinf (Fin v) Bh ->
  mem3 (Itv (max_zinf lo Bl) (min_zinf hi Bh)) v.
Proof.
  intros; unfold mem3; cbn [lb ub]; split;
    [apply max_zinf_lub; assumption | apply leq_zinf_min_zinf_glb; assumption].
Qed.

Lemma floor_lb : forall v y z, 0 < z -> v <= y / z -> v * z <= y.
Proof. intros v y z Hz Hv. pose proof (Z.mul_div_le y z ltac:(lia)). nia. Qed.
Lemma floor_ub : forall v y z, 0 < z -> y / z <= v -> y <= (v+1)*z - 1.
Proof.
  intros v y z Hz Hv.
  pose proof (Z.div_mod y z ltac:(lia)). pose proof (Z.mod_pos_bound y z ltac:(lia)). nia.
Qed.

(* ===== floor monotonicity in the divisor (z>=1) ===== *)
Lemma div_mono_z_ge0 : forall y z1 z2, 0 <= y -> 0 < z1 -> z1 <= z2 -> y / z2 <= y / z1.
Proof. intros; apply Z.div_le_compat_l; lia. Qed.
Lemma div_mono_z_le0 : forall y z1 z2, y <= 0 -> 0 < z1 -> z1 <= z2 -> y / z1 <= y / z2.
Proof.
  intros y z1 z2 Hy Hz1 Hz2.
  assert (Hle0 : y / z1 <= 0) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.mul_div_le y z1 ltac:(lia)).
  apply Z.div_le_lower_bound; [lia | nia].
Qed.

(* ===== X corner brackets for floor ===== *)
Lemma flo_xlo : forall yb zl zu vy vz,
  leq_zinf yb (Fin vy) -> leq_zinf (Fin 1) zl -> leq_zinf zl (Fin vz) -> leq_zinf (Fin vz) zu ->
  leq_zinf (min_zinf (fdiv_zinf yb zl) (fdiv_zinf yb zu)) (Fin (vy / vz)).
Proof.
  intros yb zl zu vy vz Hyb Hz1 Hzl Hzu.
  destruct zl as [zlv| |]; cbn in Hz1, Hzl; try contradiction.
  destruct yb as [ylv| |]; cbn in Hyb; try contradiction.
  - assert (Hvz : 0 < vz) by lia.
    assert (Hmy : ylv / vz <= vy / vz) by (apply Z.div_le_mono; lia).
    destruct zu as [zuv| |]; cbn in Hzu; try contradiction.
    + cbn.
      assert (Hzb : Z.min (ylv / zlv) (ylv / zuv) <= ylv / vz).
      { destruct (Z.le_gt_cases 0 ylv) as [Hp|Hn].
        - pose proof (div_mono_z_ge0 ylv vz zuv Hp ltac:(lia) ltac:(lia)).
          pose proof (Z.le_min_r (ylv / zlv) (ylv / zuv)). lia.
        - pose proof (div_mono_z_le0 ylv zlv vz ltac:(lia) ltac:(lia) ltac:(lia)).
          pose proof (Z.le_min_l (ylv / zlv) (ylv / zuv)). lia. }
      lia.
    + (* zu = Pinf : fdiv_zinf (Fin ylv) Pinf = Fin (if ylv<?0 then -1 else 0) *)
      cbn.
      destruct (Z.ltb_spec ylv 0) as [Hn|Hp].
      * (* ylv<0 : corner -1 *)
        assert (Hzb : Z.min (ylv / zlv) (-1) <= ylv / vz).
        { pose proof (div_mono_z_le0 ylv zlv vz ltac:(lia) ltac:(lia) ltac:(lia)).
          pose proof (Z.le_min_l (ylv / zlv) (-1)). lia. }
        lia.
      * (* ylv>=0 : corner 0 *)
        assert (Hzb : Z.min (ylv / zlv) 0 <= ylv / vz).
        { pose proof (Z.div_pos ylv vz Hp Hvz).
          pose proof (Z.le_min_r (ylv / zlv) 0). lia. }
        lia.
  - cbn [fdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 zlv) ltac:(lia)). destruct zu; cbn; exact I.
Qed.

Lemma flo_xhi : forall yb zl zu vy vz,
  leq_zinf (Fin vy) yb -> leq_zinf (Fin 1) zl -> leq_zinf zl (Fin vz) -> leq_zinf (Fin vz) zu ->
  leq_zinf (Fin (vy / vz)) (max_zinf (fdiv_zinf yb zl) (fdiv_zinf yb zu)).
Proof.
  intros yb zl zu vy vz Hyb Hz1 Hzl Hzu.
  destruct zl as [zlv| |]; cbn in Hz1, Hzl; try contradiction.
  destruct yb as [yuv| |]; cbn in Hyb; try contradiction.
  - assert (Hvz : 0 < vz) by lia.
    assert (Hmy : vy / vz <= yuv / vz) by (apply Z.div_le_mono; lia).
    destruct zu as [zuv| |]; cbn in Hzu; try contradiction.
    + cbn.
      assert (Hzb : yuv / vz <= Z.max (yuv / zlv) (yuv / zuv)).
      { destruct (Z.le_gt_cases 0 yuv) as [Hp|Hn].
        - pose proof (div_mono_z_ge0 yuv zlv vz Hp ltac:(lia) ltac:(lia)).
          pose proof (Z.le_max_l (yuv / zlv) (yuv / zuv)). lia.
        - pose proof (div_mono_z_le0 yuv vz zuv ltac:(lia) ltac:(lia) ltac:(lia)).
          pose proof (Z.le_max_r (yuv / zlv) (yuv / zuv)). lia. }
      lia.
    + cbn.
      destruct (Z.ltb_spec yuv 0) as [Hn|Hp].
      * (* yuv<0 : corner -1, and vy/vz<=yuv/vz<=-1 *)
        pose proof (Z.mul_div_le yuv vz ltac:(lia)).
        assert (yuv / vz <= -1) by nia.
        pose proof (Z.le_max_r (yuv / zlv) (-1)). lia.
      * (* yuv>=0 : corner 0 *)
        assert (Hzb : yuv / vz <= Z.max (yuv / zlv) 0).
        { pose proof (div_mono_z_ge0 yuv zlv vz Hp ltac:(lia) ltac:(lia)).
          pose proof (Z.le_max_l (yuv / zlv) 0). lia. }
        lia.
  - cbn [fdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 zlv) ltac:(lia)). destruct zu; cbn; exact I.
Qed.

(* ===== Y corner brackets for floor (uniform over the sign of x) ===== *)
Lemma flo_ylo : forall s vy vz iz,
  1 <= vz -> leq_zinf (Fin 1) (lb iz) -> leq_zinf (lb iz) (Fin vz) -> leq_zinf (Fin vz) (ub iz) ->
  leq_zinf (lb (sx3 s)) (Fin (vy / vz)) ->
  leq_zinf (min_zinf (mul_zinf (lb (sx3 s)) (lb iz)) (mul_zinf (lb (sx3 s)) (ub iz))) (Fin vy).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxl.
  destruct (lb iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (lb (sx3 s)) as [a| |] eqn:Ex; cbn in Hxl; try contradiction.
  - pose proof (floor_lb a vy vz ltac:(lia) Hxl) as Hb.  (* a*vz <= vy *)
    destruct (ub iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn. destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
      * pose proof (Z.le_min_l (a*zl) (a*zu)). nia.
      * pose proof (Z.le_min_r (a*zl) (a*zu)). nia.
    + destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
      * rewrite mul_zinf_fn by lia. cbn. exact I.
      * subst a. cbn. nia.
      * rewrite mul_zinf_fp by lia. cbn. nia.
  - rewrite mul_zinf_ninf_fp by lia. cbn. exact I.
Qed.

Lemma flo_yhi : forall s vy vz iz,
  1 <= vz -> leq_zinf (Fin 1) (lb iz) -> leq_zinf (lb iz) (Fin vz) -> leq_zinf (Fin vz) (ub iz) ->
  leq_zinf (Fin (vy / vz)) (ub (sx3 s)) ->
  leq_zinf (Fin vy) (max_zinf (addk_zinf (mul_zinf (addk_zinf (ub (sx3 s)) 1) (lb iz)) (-1))
                     (addk_zinf (mul_zinf (addk_zinf (ub (sx3 s)) 1) (ub iz)) (-1))).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxu.
  destruct (lb iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (ub (sx3 s)) as [b| |] eqn:Ex; cbn in Hxu; try contradiction.
  - pose proof (floor_ub b vy vz ltac:(lia) Hxu) as Hb.  (* vy <= (b+1)*vz-1 *)
    destruct (ub iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn [addk_zinf mul_zinf]. cbn. destruct (Z.le_gt_cases 0 (b+1)) as [Hk|Hk].
      * pose proof (Z.le_max_r (b + 1 * zl + -1)%Z (b + 1 * zu + -1)%Z). nia.
      * pose proof (Z.le_max_l (b + 1 * zl + -1)%Z (b + 1 * zu + -1)%Z). nia.
    + cbn [addk_zinf]. destruct (Z.lt_trichotomy (b+1) 0) as [Hk|[Hk|Hk]].
      * rewrite mul_zinf_fn by lia. cbn [addk_zinf]. cbn. nia.
      * replace (b + 1) with 0 by lia. cbn. nia.
      * rewrite mul_zinf_fp by lia. cbn [addk_zinf]. cbn. exact I.
  - cbn [addk_zinf]. rewrite mul_zinf_pinf_fp by lia. cbn [addk_zinf]. cbn. exact I.
Qed.

(* ===== floor Z-step membership (whole 4-way if, botitv => contradiction) ===== *)
Lemma flo_z1_mem : forall s vy vz z0,
  1 <= vz -> leq_zinf (lb z0) (Fin vz) -> leq_zinf (Fin vz) (ub z0) ->
  leq_zinf (lb (sx3 s)) (Fin (vy / vz)) -> leq_zinf (Fin vy) (ub (sy3 s)) ->
  mem3 (if ispos_zinf (lb (sx3 s))
        then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (ub (sy3 s)) (lb (sx3 s))))
        else if negb (iszero_zinf (lb (sx3 s)))
             then Itv (max_zinf (lb z0) (cdiv_zinf (ub (sy3 s)) (lb (sx3 s)))) (ub z0)
             else if isneg_zinf (ub (sy3 s)) then botitv else z0) vz.
Proof.
  intros s vy vz z0 Hvz Hz0l Hz0u Hxl Hyu.
  destruct (ispos_zinf (lb (sx3 s))) eqn:Ezp.
  - (* hi-narrow *)
    apply mem3_narrow_hi; [exact Hz0l | exact Hz0u | ].
    destruct (lb (sx3 s)) as [a| |] eqn:Ex; cbn in Ezp, Hxl; try discriminate; try contradiction.
    apply Z.ltb_lt in Ezp. pose proof (floor_lb a vy vz ltac:(lia) Hxl) as Hb.
    destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
    + cbn [fdiv_zinf]. cbn. apply F1; lia.
    + cbn [fdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 a) Ezp). exact I.
  - destruct (iszero_zinf (lb (sx3 s))) eqn:Ez; cbn [negb].
    + (* iszero_zinf true : lo x = 0 *)
      destruct (lb (sx3 s)) as [a| |] eqn:Ex; cbn in Ez; try discriminate.
      apply Z.eqb_eq in Ez. subst a. cbn in Hxl. (* 0 <= vy/vz *)
      destruct (isneg_zinf (ub (sy3 s))) eqn:Eyn.
      * (* botitv : no solution *)
        exfalso.
        destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Eyn, Hyu; try discriminate; try contradiction.
        apply Z.ltb_lt in Eyn. (* u < 0, vy <= u *)
        pose proof (Z.mul_div_le vy vz ltac:(lia)). nia.
      * exact (conj Hz0l Hz0u).
    + (* lo-narrow : lo x < 0 or Ninf *)
      apply mem3_narrow_lo; [exact Hz0l | exact Hz0u | ].
      destruct (lb (sx3 s)) as [a| |] eqn:Ex; cbn in Ezp, Ez, Hxl; try discriminate.
      * (* Fin a, a < 0 *)
        apply Z.ltb_ge in Ezp. apply Z.eqb_neq in Ez.
        pose proof (floor_lb a vy vz ltac:(lia) Hxl) as Hb.
        destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
        -- cbn [cdiv_zinf]. cbn. apply C1; [lia | nia].
        -- cbn [cdiv_zinf]. rewrite (proj2 (Z.ltb_ge 0 a) ltac:(lia)). exact I.
      * (* Ninf : bound 0 or 1 <= vz *)
        destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
        -- cbn [cdiv_zinf]. destruct (u <? 0); cbn; lia.
        -- cbn [cdiv_zinf]. cbn; lia.
Qed.

Lemma flo_z2_mem : forall s vy vz z0,
  1 <= vz -> leq_zinf (lb z0) (Fin vz) -> leq_zinf (Fin vz) (ub z0) ->
  leq_zinf (Fin (vy / vz)) (ub (sx3 s)) -> leq_zinf (lb (sy3 s)) (Fin vy) ->
  mem3 (if geq0_zinf (ub (sx3 s))
        then Itv (max_zinf (lb z0) (cdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1))) (ub z0)
        else if negb (zeqm1 (ub (sx3 s)))
             then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1)))
             else if geq0_zinf (lb (sy3 s)) then botitv else z0) vz.
Proof.
  intros s vy vz z0 Hvz Hz0l Hz0u Hxu Hyl.
  destruct (geq0_zinf (ub (sx3 s))) eqn:Ezg.
  - (* lo-narrow *)
    apply mem3_narrow_lo; [exact Hz0l | exact Hz0u | ].
    destruct (ub (sx3 s)) as [b| |] eqn:Ex; cbn in Ezg, Hxu; try discriminate; try contradiction.
    + apply Z.leb_le in Ezg. pose proof (floor_ub b vy vz ltac:(lia) Hxu) as Hb.
      destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
      * cbn [addk_zinf cdiv_zinf]. cbn. apply CC1; lia.
      * cbn [addk_zinf cdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 (b+1)) ltac:(lia)). exact I.
    + (* Pinf *)
      cbn [addk_zinf].
      destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
      * cbn [addk_zinf cdiv_zinf]. destruct (0 <? l + 1); cbn; lia.
      * cbn [addk_zinf cdiv_zinf]. cbn; lia.
  - destruct (zeqm1 (ub (sx3 s))) eqn:Ee; cbn [negb].
    + (* zeqm1 true : hi x = -1 *)
      destruct (ub (sx3 s)) as [b| |] eqn:Ex; cbn in Ee; try discriminate.
      apply Z.eqb_eq in Ee. subst b. cbn in Hxu. (* vy/vz <= -1 *)
      destruct (geq0_zinf (lb (sy3 s))) eqn:Eyl.
      * (* botitv : no solution *)
        exfalso.
        destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Eyl, Hyl; try discriminate; try contradiction.
        apply Z.leb_le in Eyl. (* 0 <= l <= vy *)
        pose proof (Z.div_pos vy vz ltac:(lia) ltac:(lia)). lia.
      * exact (conj Hz0l Hz0u).
    + (* hi-narrow : hi x < 0, != -1, or Ninf *)
      apply mem3_narrow_hi; [exact Hz0l | exact Hz0u | ].
      destruct (ub (sx3 s)) as [b| |] eqn:Ex; cbn in Ezg, Ee, Hxu; try discriminate; try contradiction.
      * (* Fin b, b < 0, b <> -1 *)
        apply Z.leb_gt in Ezg. apply Z.eqb_neq in Ee.
        pose proof (floor_ub b vy vz ltac:(lia) Hxu) as Hb.
        destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
        -- cbn [addk_zinf fdiv_zinf]. cbn. apply FN1; [lia | nia].
        -- cbn [addk_zinf fdiv_zinf]. rewrite (proj2 (Z.ltb_ge 0 (b+1)) ltac:(lia)). exact I.
Qed.

(* ===== positivity of the narrowed z (lo stays >= 1) ===== *)
Lemma flo_z1_pos : forall s z0, leq_zinf (Fin 1) (lb z0) ->
  leq_zinf (Fin 1) (lb (if ispos_zinf (lb (sx3 s))
        then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (ub (sy3 s)) (lb (sx3 s))))
        else if negb (iszero_zinf (lb (sx3 s)))
             then Itv (max_zinf (lb z0) (cdiv_zinf (ub (sy3 s)) (lb (sx3 s)))) (ub z0)
             else if isneg_zinf (ub (sy3 s)) then botitv else z0)).
Proof.
  intros s z0 H.
  destruct (ispos_zinf (lb (sx3 s))); [cbn [lb]; exact H | ].
  destruct (iszero_zinf (lb (sx3 s))); cbn [negb].
  - destruct (isneg_zinf (ub (sy3 s))); [cbn; exact I | cbn [lb]; exact H].
  - cbn [lb]. eapply leq_zinf_trans; [exact H | apply leq_zinf_max_zinf_l].
Qed.

Lemma flo_z2_pos : forall s z0, leq_zinf (Fin 1) (lb z0) ->
  leq_zinf (Fin 1) (lb (if geq0_zinf (ub (sx3 s))
        then Itv (max_zinf (lb z0) (cdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1))) (ub z0)
        else if negb (zeqm1 (ub (sx3 s)))
             then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1)))
             else if geq0_zinf (lb (sy3 s)) then botitv else z0)).
Proof.
  intros s z0 H.
  destruct (geq0_zinf (ub (sx3 s))); [cbn [lb]; eapply leq_zinf_trans; [exact H | apply leq_zinf_max_zinf_l] | ].
  destruct (zeqm1 (ub (sx3 s))); cbn [negb].
  - destruct (geq0_zinf (lb (sy3 s))); [cbn; exact I | cbn [lb]; exact H].
  - cbn [lb]; exact H.
Qed.

Theorem fpos_sound : forall s vx vy vz,
  in_store3 s vx vy vz -> is_fdiv_asn vx vy vz -> 1 <= vz ->
  in_store3 (zfdiv_pos3 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hsol Hvz1.
  destruct Hin as (Hmx & Hmy & Hmz).
  destruct Hsol as [Hnz Hq]. subst vx.
  destruct Hmx as [Hxl Hxu]; destruct Hmy as [Hyl Hyu]; destruct Hmz as [Hzl0 Hzu0].
  unfold zfdiv_pos3; cbv zeta.
  match goal with |- context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hmz0l : leq_zinf (lb z0) (Fin vz)) by (rewrite Hz0; cbn [lb]; apply max_zinf_lub; [exact Hzl0 | cbn; lia]).
  assert (Hmz0u : leq_zinf (Fin vz) (ub z0)) by (rewrite Hz0; cbn [ub]; exact Hzu0).
  assert (Hlz0 : leq_zinf (Fin 1) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_r).
  destruct (negb (nonempty3b z0)) eqn:E0.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj Hyl Hyu) | exact (conj Hmz0l Hmz0u)]]. }
  match goal with |- context[if ispos_zinf (lb (sx3 s)) then ?A else ?B] =>
    remember (if ispos_zinf (lb (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hmz1 : mem3 z1 vz) by
    (rewrite Hz1; apply (flo_z1_mem s vy vz z0); [exact Hvz1|exact Hmz0l|exact Hmz0u|exact Hxl|exact Hyu]).
  assert (Hlz1 : leq_zinf (Fin 1) (lb z1)) by (rewrite Hz1; apply flo_z1_pos; exact Hlz0).
  destruct Hmz1 as [Hmz1l Hmz1u].
  match goal with |- context[if geq0_zinf (ub (sx3 s)) then ?A else ?B] =>
    remember (if geq0_zinf (ub (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hmz2 : mem3 z2 vz) by
    (rewrite Hz2; apply (flo_z2_mem s vy vz z1); [exact Hvz1|exact Hmz1l|exact Hmz1u|exact Hxu|exact Hyl]).
  assert (Hlz2 : leq_zinf (Fin 1) (lb z2)) by (rewrite Hz2; apply flo_z2_pos; exact Hlz1).
  destruct Hmz2 as [Hmz2l Hmz2u].
  destruct (negb (nonempty3b z2)) eqn:E2.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj Hyl Hyu) | exact (conj Hmz2l Hmz2u)]]. }
  match goal with |- context[nonempty3b ?Y] => remember Y as yF eqn:HyF end.
  assert (Hmy : mem3 yF vy).
  { rewrite HyF. apply mem3_narrow_both.
    - exact Hyl.
    - exact Hyu.
    - apply (flo_ylo s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxl].
    - apply (flo_yhi s vy vz z2); [exact Hvz1|exact Hlz2|exact Hmz2l|exact Hmz2u|exact Hxu]. }
  destruct Hmy as [HmyL HmyU].
  destruct (negb (nonempty3b yF)) eqn:EY.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj HmyL HmyU) | exact (conj Hmz2l Hmz2u)]]. }
  split.
  - apply mem3_narrow_both.
    + exact Hxl.
    + exact Hxu.
    + eapply leq_zinf_trans; [apply min_zinf_leq_zinf_l | ].
      apply (flo_xlo (lb yF) (lb z2) (ub z2)); [exact HmyL|exact Hlz2|exact Hmz2l|exact Hmz2u].
    + eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ].
      apply (flo_xhi (ub yF) (lb z2) (ub z2)); [exact HmyU|exact Hlz2|exact Hmz2l|exact Hmz2u].
  - split; [exact (conj HmyL HmyU) | exact (conj Hmz2l Hmz2u)].
Qed.


Lemma mul_le_div : forall n a q, 0 < a -> q <= n / a -> a * q <= n.
Proof. intros n a q Ha H. pose proof (Z.mul_div_le n a Ha). nia. Qed.

Lemma mul_ge_div_neg : forall n m q, m < 0 -> q <= n / m -> n <= m * q.
Proof.
  intros n m q Hm H.
  pose proof (Z.div_mod n m ltac:(lia)).
  pose proof (Z.mod_neg_bound n m Hm). nia.
Qed.

Lemma RC1 : forall n m q, m < 0 -> cdiv n m <= q -> m * q <= n.
Proof.
  intros n m q Hm H. unfold cdiv in H.
  assert (E : (- n) / m = n / (- m)).
  { replace m with (- - m) at 1 by lia. rewrite (Z.div_opp_opp n (- m)) by lia. reflexivity. }
  rewrite E in H.
  pose proof (Z.mul_div_le n (- m) ltac:(lia)). nia.
Qed.

Lemma RCC1 : forall n m q, 0 < m -> cdiv n m <= q -> n <= m * q.
Proof.
  intros n m q Hm H. unfold cdiv in H.
  pose proof (Z.mul_div_le (- n) m Hm). nia.
Qed.

(* ===== Zinf band bounds and their soundness for the witness ===== *)
Lemma z1band_pos : forall yu vz a, 0 < a -> yu <> Ninf ->
  leq_zinf (Fin vz) (fdiv_zinf yu (Fin a)) -> leq_zinf (Fin (a * vz)) yu.
Proof.
  intros yu vz a Ha Hyn H.
  destruct yu as [u| |]; try congruence.
  - cbn [fdiv_zinf] in H. cbn in H. cbn. apply mul_le_div; lia.
  - cbn. exact I.
Qed.

Lemma z2band_pos : forall yl vz b, 0 <= b -> yl <> Pinf ->
  leq_zinf (cdiv_zinf (addk_zinf yl 1) (addk_zinf (Fin b) 1)) (Fin vz) ->
  leq_zinf yl (Fin ((b + 1) * vz - 1)).
Proof.
  intros yl vz b Hb Hyp H. cbn [addk_zinf] in H.
  destruct yl as [l| |]; try congruence.
  - cbn [addk_zinf cdiv_zinf] in H. cbn in H.
    assert (Hle : l + 1 <= (b + 1) * vz) by (apply RCC1; [lia | exact H]). cbn. nia.
  - cbn. exact I.
Qed.

Lemma nonempty_bounds : forall i, nonempty3b i = true -> lb i <> Pinf /\ ub i <> Ninf.
Proof. intros [[a| |] [b| |]]; cbn; intro H; try discriminate; split; discriminate. Qed.

Lemma ne_leq_zinf : forall i, nonempty3b i = true -> leq_zinf (lb i) (ub i).
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; try exact I. apply Z.leb_le; exact H.
Qed.

Definition pickf (L U : Zinf) : Z :=
  match L with Fin l => l | _ => match U with Fin u => u | _ => 0 end end.

Lemma pickf_mem : forall L U, leq_zinf L U -> L <> Pinf -> U <> Ninf ->
  leq_zinf L (Fin (pickf L U)) /\ leq_zinf (Fin (pickf L U)) U.
Proof.
  intros [l| |] [u| |] H Hl Hu; cbn in *; try congruence; split; try exact I; lia.
Qed.

(* ===== step monotonicity (lo does not decrease, hi does not increase) ===== *)
Lemma leq_zinf_Pinf : forall a, leq_zinf a Pinf.
Proof. intros [v| |]; cbn; exact I. Qed.

Lemma fin_of_ge1 : forall a, leq_zinf (Fin 1) a -> a <> Pinf -> exists v, a = Fin v /\ 1 <= v.
Proof.
  intros [v| |] H Hp; cbn in *; [exists v; split; [reflexivity | lia] | congruence | contradiction].
Qed.

(* ===== the propagator-reconstruction core ===== *)
Lemma max_zinf_not_Pinf : forall a b, a <> Pinf -> b <> Pinf -> max_zinf a b <> Pinf.
Proof. intros [x| |] [y| |] Ha Hb; cbn; congruence. Qed.
Lemma min_zinf_not_Ninf : forall a b, a <> Ninf -> b <> Ninf -> min_zinf a b <> Ninf.
Proof. intros [x| |] [y| |] Ha Hb; cbn; congruence. Qed.
Lemma leq_zinf_ineg3_r : forall a v, leq_zinf a (Fin v) -> leq_zinf (Fin (- v)) (ineg3 a).
Proof. intros [x| |] v H; cbn in *; try exact I; try contradiction; lia. Qed.
Lemma leq_zinf_ineg3_l : forall a v, leq_zinf (Fin v) a -> leq_zinf (ineg3 a) (Fin (- v)).
Proof. intros [x| |] v H; cbn in *; try exact I; try contradiction; lia. Qed.

Lemma mem3_mirror : forall i v, mem3 i v -> mem3 (mirror_i i) (- v).
Proof.
  intros i v [Hlo Hhi]. unfold mirror_i, mem3; cbn [lb ub].
  split; [apply leq_zinf_ineg3_l; exact Hhi | apply leq_zinf_ineg3_r; exact Hlo].
Qed.

Lemma in_mir_xz : forall t a b c, in_store3 t a b c -> in_store3 (mir_xz t) (- a) b (- c).
Proof.
  intros t a b c (Hx & Hy & Hz).
  unfold mir_xz, in_store3; cbn [sx3 sy3 sz3].
  split; [apply mem3_mirror; exact Hx | split; [exact Hy | apply mem3_mirror; exact Hz]].
Qed.

(* ---- non-emptiness from membership ---- *)
Lemma nonempty3b_true : forall i v, mem3 i v -> nonempty3b i = true.
Proof.
  intros i v [Hlo Hhi]. unfold nonempty3b.
  destruct (lb i) as [a| |]; destruct (ub i) as [b| |]; cbn in *;
    try reflexivity; try contradiction. apply Z.leb_le; lia.
Qed.
Lemma ne_store3_true : forall s a b c, in_store3 s a b c -> ne_store3 s = true.
Proof.
  intros s a b c (Hx & Hy & Hz). unfold ne_store3.
  rewrite (nonempty3b_true _ _ Hx), (nonempty3b_true _ _ Hy), (nonempty3b_true _ _ Hz).
  reflexivity.
Qed.

(* ---- join preserves membership ---- *)
Lemma mem3_ijoin_l : forall i j v, mem3 i v -> mem3 (ijoin3 i j) v.
Proof.
  intros i j v [Hlo Hhi]. unfold ijoin3, mem3; cbn [lb ub]. split.
  - eapply leq_zinf_trans; [apply min_zinf_leq_zinf_l | exact Hlo].
  - eapply leq_zinf_trans; [exact Hhi | apply leq_zinf_max_zinf_l].
Qed.
Lemma mem3_ijoin_r : forall i j v, mem3 j v -> mem3 (ijoin3 i j) v.
Proof.
  intros i j v [Hlo Hhi]. unfold ijoin3, mem3; cbn [lb ub]. split.
  - eapply leq_zinf_trans; [apply min_zinf_leq_zinf_r | exact Hlo].
  - eapply leq_zinf_trans; [exact Hhi | apply leq_zinf_max_zinf_r].
Qed.
Lemma in_sjoin3_l : forall a b vx vy vz, in_store3 a vx vy vz -> in_store3 (sjoin3 a b) vx vy vz.
Proof.
  intros a b vx vy vz (Hx & Hy & Hz). unfold sjoin3, in_store3; cbn [sx3 sy3 sz3].
  split; [apply mem3_ijoin_l; exact Hx | split; apply mem3_ijoin_l; assumption].
Qed.
Lemma in_sjoin3_r : forall a b vx vy vz, in_store3 b vx vy vz -> in_store3 (sjoin3 a b) vx vy vz.
Proof.
  intros a b vx vy vz (Hx & Hy & Hz). unfold sjoin3, in_store3; cbn [sx3 sy3 sz3].
  split; [apply mem3_ijoin_r; exact Hx | split; apply mem3_ijoin_r; assumption].
Qed.

Lemma in_join4_l : forall pos neg vx vy vz,
  in_store3 pos vx vy vz -> in_store3 (join4 pos neg) vx vy vz.
Proof.
  intros pos neg vx vy vz H. unfold join4.
  rewrite (ne_store3_true _ _ _ _ H). cbn [negb].
  destruct (ne_store3 neg); cbn [negb].
  - apply in_sjoin3_l; exact H.
  - exact H.
Qed.
Lemma in_join4_r : forall pos neg vx vy vz,
  in_store3 neg vx vy vz -> in_store3 (join4 pos neg) vx vy vz.
Proof.
  intros pos neg vx vy vz H. unfold join4.
  destruct (negb (ne_store3 pos)) eqn:Ep.
  - exact H.
  - rewrite (ne_store3_true _ _ _ _ H). cbn [negb]. apply in_sjoin3_r; exact H.
Qed.

Lemma in_mir_yz : forall t a b c, in_store3 t a b c -> in_store3 (mir_yz t) a (- b) (- c).
Proof.
  intros t a b c (Hx & Hy & Hz).
  unfold mir_yz, in_store3; cbn [sx3 sy3 sz3].
  split; [exact Hx | split; [apply mem3_mirror; exact Hy | apply mem3_mirror; exact Hz]].
Qed.

Theorem zfdiv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> is_fdiv_asn vx vy vz -> in_store3 (zfdiv4 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hsol.
  assert (Hne : ne_store3 s = true) by (eapply ne_store3_true; exact Hin).
  unfold zfdiv4. rewrite Hne. cbn [negb].
  destruct Hsol as [Hnz Hq].
  destruct (Z.lt_total vz 0) as [Hisneg_zinf | [Hz0 | Hispos_zinf]].
  - (* vz <= -1 : negative slice via mir_yz *)
    apply in_join4_r.
    assert (Hmir : in_store3 (mir_yz s) vx (- vy) (- vz)) by (apply in_mir_yz; exact Hin).
    assert (Hsmir : is_fdiv_asn vx (- vy) (- vz)).
    { split; [lia | ]. rewrite Hq. rewrite Z.div_opp_opp by lia. reflexivity. }
    pose proof (fpos_sound (mir_yz s) vx (- vy) (- vz) Hmir Hsmir ltac:(lia)) as Hp.
    pose proof (in_mir_yz (zfdiv_pos3 (mir_yz s)) vx (- vy) (- vz) Hp) as Hback.
    rewrite !Z.opp_involutive in Hback. exact Hback.
  - exfalso; apply Hnz; exact Hz0.
  - (* vz >= 1 : positive slice directly *)
    apply in_join4_l.
    apply fpos_sound; [exact Hin | split; [exact Hnz | exact Hq] | lia].
Qed.

(* ================================================================== *)
(** Support lemmas for the ceiling / Euclidean soundness proofs:
    [mir_xy] membership and the floor identity (-a)/b = a/(-b) *)
(* ================================================================== *)

Lemma in_mir_xy : forall t a b c, in_store3 t a b c -> in_store3 (mir_xy t) (- a) (- b) c.
Proof.
  intros t a b c (Hx & Hy & Hz).
  unfold mir_xy, in_store3; cbn [sx3 sy3 sz3].
  split; [apply mem3_mirror; exact Hx | split; [apply mem3_mirror; exact Hy | exact Hz]].
Qed.

(* floor: (-a)/b = a/(-b) *)
Lemma div_opp_num_den : forall a b, b <> 0 -> (- a) / b = a / (- b).
Proof.
  intros a b Hb.
  replace b with (- - b) at 1 by lia.
  rewrite (Z.div_opp_opp a (- b)) by lia.
  reflexivity.
Qed.

Theorem zcdiv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> csol vx vy vz -> in_store3 (zcdiv4 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hcsol.
  assert (Hne : ne_store3 s = true) by (eapply ne_store3_true; exact Hin).
  unfold zcdiv4. rewrite Hne. cbn [negb].
  destruct Hcsol as [Hnz Hq]. unfold cdiv in Hq.
  destruct (Z.lt_total vz 0) as [Hisneg_zinf | [Hz0 | Hispos_zinf]].
  - (* vz <= -1 : ceil(y/z) = -floor(y/(-z)) via mir_xz *)
    apply in_join4_r.
    assert (Hmir : in_store3 (mir_xz s) (- vx) vy (- vz)) by (apply in_mir_xz; exact Hin).
    assert (Hsmir : is_fdiv_asn (- vx) vy (- vz)).
    { split; [lia | ]. rewrite Hq. rewrite Z.opp_involutive. apply div_opp_num_den; lia. }
    pose proof (fpos_sound (mir_xz s) (- vx) vy (- vz) Hmir Hsmir ltac:(lia)) as Hp.
    pose proof (in_mir_xz (zfdiv_pos3 (mir_xz s)) (- vx) vy (- vz) Hp) as Hb.
    rewrite !Z.opp_involutive in Hb. exact Hb.
  - exfalso; apply Hnz; exact Hz0.
  - (* vz >= 1 : ceil(y/z) = -floor((-y)/z) via mir_xy *)
    apply in_join4_l.
    assert (Hmir : in_store3 (mir_xy s) (- vx) (- vy) vz) by (apply in_mir_xy; exact Hin).
    assert (Hsmir : is_fdiv_asn (- vx) (- vy) vz).
    { split; [lia | ]. rewrite Hq. lia. }
    pose proof (fpos_sound (mir_xy s) (- vx) (- vy) vz Hmir Hsmir ltac:(lia)) as Hp.
    pose proof (in_mir_xy (zfdiv_pos3 (mir_xy s)) (- vx) (- vy) vz Hp) as Hb.
    rewrite !Z.opp_involutive in Hb. exact Hb.
Qed.

Theorem zediv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> esol vx vy vz -> in_store3 (zediv4 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hesol.
  assert (Hne : ne_store3 s = true) by (eapply ne_store3_true; exact Hin).
  unfold zediv4. rewrite Hne. cbn [negb].
  destruct Hesol as [Hnz Hq].
  destruct (Z.lt_total vz 0) as [Hisneg_zinf | [Hz0 | Hispos_zinf]].
  - (* vz <= -1 : ediv = ceil = -floor(y/(-z)) via mir_xz *)
    rewrite (proj2 (Z.ltb_ge 0 vz) ltac:(lia)) in Hq.  (* 0<?vz = false -> vx = cdiv vy vz *)
    unfold cdiv in Hq.
    apply in_join4_r.
    assert (Hmir : in_store3 (mir_xz s) (- vx) vy (- vz)) by (apply in_mir_xz; exact Hin).
    assert (Hsmir : is_fdiv_asn (- vx) vy (- vz)).
    { split; [lia | ]. rewrite Hq. rewrite Z.opp_involutive. apply div_opp_num_den; lia. }
    pose proof (fpos_sound (mir_xz s) (- vx) vy (- vz) Hmir Hsmir ltac:(lia)) as Hp.
    pose proof (in_mir_xz (zfdiv_pos3 (mir_xz s)) (- vx) vy (- vz) Hp) as Hb.
    rewrite !Z.opp_involutive in Hb. exact Hb.
  - exfalso; apply Hnz; exact Hz0.
  - (* vz >= 1 : ediv = floor = y/z, positive slice directly *)
    rewrite (proj2 (Z.ltb_lt 0 vz) ltac:(lia)) in Hq.  (* 0<?vz = true -> vx = vy/vz *)
    apply in_join4_l.
    apply fpos_sound; [exact Hin | split; [exact Hnz | exact Hq] | lia].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Completeness (best abstract transformer)                        *)
(* ------------------------------------------------------------------ *)

(* ================================================================== *)
(** Support lemmas for the completeness / feasibility theorems:
    mirroring on the interval order, the bottom-absorbing join as a
    lub, and the reductions to the positive-slice bricks. *)
(* ================================================================== *)

(* ===== mirroring on the interval order and non-emptiness ===== *)
Lemma ineg3_le : forall a b, leq_zinf (ineg3 a) (ineg3 b) <-> leq_zinf b a.
Proof. intros [x| |] [y| |]; cbn; try tauto; lia. Qed.

Lemma nonempty3b_mirror : forall i, nonempty3b (mirror_i i) = nonempty3b i.
Proof.
  intros [[x| |] [y| |]]; cbn; try reflexivity;
    destruct (Z.leb_spec (- y) (- x)); destruct (Z.leb_spec x y);
    first [ reflexivity | exfalso; lia ].
Qed.

Lemma ne_mir_xz : forall s, ne_store3 (mir_xz s) = ne_store3 s.
Proof.
  intros s. unfold ne_store3, mir_xz; cbn [sx3 sy3 sz3].
  rewrite !nonempty3b_mirror. reflexivity.
Qed.

Lemma ile3_mirror : forall i j, ile3 (mirror_i i) (mirror_i j) <-> ile3 i j.
Proof.
  intros i j. unfold ile3. rewrite (nonempty3b_mirror i).
  unfold mirror_i; cbn [lb ub]. rewrite !ineg3_le. tauto.
Qed.

Lemma sle3_mir_xz : forall a b, sle3 (mir_xz a) (mir_xz b) <-> sle3 a b.
Proof.
  intros a b. unfold sle3. rewrite (ne_mir_xz a).
  unfold mir_xz; cbn [sx3 sy3 sz3]. rewrite !ile3_mirror. tauto.
Qed.

Lemma ineg3_invol : forall a, ineg3 (ineg3 a) = a.
Proof. intros [v| |]; cbn; try reflexivity; f_equal; lia. Qed.

Lemma mirror_i_invol : forall i, mirror_i (mirror_i i) = i.
Proof.
  intros i. unfold mirror_i; cbn [lb ub]. rewrite !ineg3_invol. destruct i; reflexivity.
Qed.

Lemma mir_xz_invol : forall s, mir_xz (mir_xz s) = s.
Proof.
  intros [ix iy iz]. unfold mir_xz; cbn [sx3 sy3 sz3].
  rewrite !mirror_i_invol. reflexivity.
Qed.

(* ===== join4 = the bottom-absorbing lub; case lemma for sle ===== *)

(* the naive join is a LUB only when both inputs are non-empty (quotient order) *)
Lemma sjoin3_lub : forall a b t,
  ne_store3 a = true -> ne_store3 b = true ->
  sle3 a t -> sle3 b t -> sle3 (sjoin3 a b) t.
Proof.
  intros a b t Ea Eb Ha Hb.
  destruct (ne_store3_parts a Ea) as (Eax & Eay & Eaz).
  destruct (ne_store3_parts b Eb) as (Ebx & Eby & Ebz).
  apply (sle3_ne_inv a t Ea) in Ha as (Hax & Hay & Haz).
  apply (sle3_ne_inv b t Eb) in Hb as (Hbx & Hby & Hbz).
  apply sle3_intro; unfold sjoin3; cbn [sx3 sy3 sz3]; apply ijoin3_ile3; assumption.
Qed.

Lemma join4_sle_cases : forall pos neg t,
  (ne_store3 pos = true -> sle3 pos t) ->
  (ne_store3 neg = true -> sle3 neg t) ->
  ne_store3 (join4 pos neg) = true ->
  sle3 (join4 pos neg) t.
Proof.
  intros pos neg t Hp Hn Hne. unfold join4 in *.
  destruct (ne_store3 pos) eqn:Ep; cbn [negb] in *.
  - destruct (ne_store3 neg) eqn:En; cbn [negb] in *.
    + apply sjoin3_lub; [exact Ep | exact En | apply Hp; reflexivity | apply Hn; reflexivity].
    + apply Hp; reflexivity.
  - apply Hn; exact Hne.
Qed.

(* ===== mirror relations for solutions ===== *)
Lemma in_mir_xz_inv : forall s vx vy vz,
  in_store3 (mir_xz s) vx vy vz -> in_store3 s (- vx) vy (- vz).
Proof.
  intros s vx vy vz H. pose proof (in_mir_xz (mir_xz s) vx vy vz H) as H2.
  rewrite mir_xz_invol in H2. exact H2.
Qed.

Lemma ne_store3_parts : forall s, ne_store3 s = true ->
  nonempty3b (sx3 s) = true /\ nonempty3b (sy3 s) = true /\ nonempty3b (sz3 s) = true.
Proof.
  intros s H. unfold ne_store3 in H.
  apply andb_true_iff in H as [H Hz]. apply andb_true_iff in H as [Hx Hy]. auto.
Qed.

Lemma ne_mir_yz : forall s, ne_store3 (mir_yz s) = ne_store3 s.
Proof.
  intros s. unfold ne_store3, mir_yz; cbn [sx3 sy3 sz3].
  rewrite !nonempty3b_mirror. reflexivity.
Qed.

Lemma sle3_mir_yz : forall a b, sle3 (mir_yz a) (mir_yz b) <-> sle3 a b.
Proof.
  intros a b. unfold sle3. rewrite (ne_mir_yz a).
  unfold mir_yz; cbn [sx3 sy3 sz3]. rewrite !ile3_mirror. tauto.
Qed.

Lemma mir_yz_invol : forall s, mir_yz (mir_yz s) = s.
Proof.
  intros [ix iy iz]. unfold mir_yz; cbn [sx3 sy3 sz3]. rewrite !mirror_i_invol. reflexivity.
Qed.

Lemma in_mir_yz_inv : forall s vx vy vz,
  in_store3 (mir_yz s) vx vy vz -> in_store3 s vx (- vy) (- vz).
Proof.
  intros s vx vy vz H. pose proof (in_mir_yz (mir_yz s) vx vy vz H) as H2.
  rewrite mir_yz_invol in H2. exact H2.
Qed.

Lemma sol_mir : forall vx vy vz, is_fdiv_asn vx vy vz -> is_fdiv_asn vx (- vy) (- vz).
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  rewrite Z.div_opp_opp by lia. exact Hq.
Qed.

(* ===== truncated best transformer (positive slice), transplanted ===== *)
Lemma mem3_lo : forall i v, mem3 i v -> leq_zinf (lb i) (Fin v).
Proof. intros i v [H _]; exact H. Qed.
Lemma mem3_hi : forall i v, mem3 i v -> leq_zinf (Fin v) (ub i).
Proof. intros i v [_ H]; exact H. Qed.

(* For any x-target v in [xl,xu] and vz>0, vy = tymin-numerator(v,vz) lies in the
   band and has quotient exactly v. *)
Definition fyminZ (xl : Zinf) (vz : Z) : Zinf :=
  match xl with Fin a => Fin (a * vz) | Ninf => Ninf | Pinf => Pinf end.
Definition fymaxZ (xu : Zinf) (vz : Z) : Zinf :=
  match xu with Fin b => Fin ((b+1) * vz - 1) | Pinf => Pinf | Ninf => Ninf end.

Lemma fdiv_ge : forall xl vy vz, 1 <= vz ->
  leq_zinf (fyminZ xl vz) (Fin vy) -> leq_zinf xl (Fin (vy / vz)).
Proof.
  intros [a| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  apply F1; [lia | nia].
Qed.

Lemma fdiv_le : forall xu vy vz, 1 <= vz ->
  leq_zinf (Fin vy) (fymaxZ xu vz) -> leq_zinf (Fin (vy / vz)) xu.
Proof.
  intros [b| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  assert (vy / vz < b + 1) by (apply Z.div_lt_upper_bound; [lia | nia]). lia.
Qed.

Lemma fband_ne : forall xl xu vz, 1 <= vz -> leq_zinf xl xu ->
  leq_zinf (fyminZ xl vz) (fymaxZ xu vz).
Proof.
  intros [a| |] [b| |] vz Hvz H; cbn in *; try exact I; try contradiction. nia.
Qed.

Lemma fyminZ_not_Pinf : forall xl vz, xl <> Pinf -> fyminZ xl vz <> Pinf.
Proof. intros [a| |] vz H; cbn; congruence. Qed.
Lemma fymaxZ_not_Ninf : forall xu vz, xu <> Ninf -> fymaxZ xu vz <> Ninf.
Proof. intros [b| |] vz H; cbn; congruence. Qed.

Lemma fdiv_zinf_mono_pos : forall n1 n2 w, leq_zinf n1 n2 -> 0 < w ->
  leq_zinf (fdiv_zinf n1 (Fin w)) (fdiv_zinf n2 (Fin w)).
Proof.
  intros [a| |] [b| |] w Hn Hw; cbn [fdiv_zinf] in *;
    try rewrite (proj2 (Z.ltb_lt 0 w) Hw); cbn in *;
    try exact I; try contradiction.
  apply Z.div_le_mono; lia.
Qed.

Lemma fattain_vx : forall xl xu vz v, 0 < vz -> leq_zinf xl (Fin v) -> leq_zinf (Fin v) xu ->
  leq_zinf (fyminZ xl vz) (Fin (v * vz)) /\
  leq_zinf (Fin (v * vz)) (fymaxZ xu vz) /\
  (v * vz) / vz = v.
Proof.
  intros xl xu vz v Hvz Hxl Hxu. split; [ | split ].
  - destruct xl as [a| |]; cbn in Hxl |- *; [ nia | contradiction | exact I ].
  - destruct xu as [b| |]; cbn in Hxu |- *; [ nia | exact I | contradiction ].
  - apply Z.div_mul; lia.
Qed.

Lemma fattain_vx_hi : forall xl xu vz v, 0 < vz -> leq_zinf xl (Fin v) -> leq_zinf (Fin v) xu ->
  leq_zinf (fyminZ xl vz) (Fin ((v + 1) * vz - 1)) /\
  leq_zinf (Fin ((v + 1) * vz - 1)) (fymaxZ xu vz) /\
  ((v + 1) * vz - 1) / vz = v.
Proof.
  intros xl xu vz v Hvz Hxl Hxu. split; [ | split ].
  - destruct xl as [a| |]; cbn in Hxl |- *; [ nia | contradiction | exact I ].
  - destruct xu as [b| |]; cbn in Hxu |- *; [ nia | exact I | contradiction ].
  - replace ((v + 1) * vz - 1) with (v * vz + (vz - 1)) by ring.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (vz - 1) vz) by lia. lia.
Qed.

Lemma fwit_in_t : forall s t vz vy,
  slice_contains is_fdiv_asn s t -> 1 <= vz -> mem3 (sz3 s) vz -> mem3 (sy3 s) vy ->
  leq_zinf (fyminZ (lb (sx3 s)) vz) (Fin vy) -> leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) vz) ->
  mem3 (sx3 t) (vy / vz) /\ mem3 (sy3 t) vy /\ mem3 (sz3 t) vz.
Proof.
  intros s t vz vy Hct Hvz1 Hmz Hmy Hb1 Hb2.
  assert (Hin : in_store3 s (vy / vz) vy vz).
  { split; [ split | split; [exact Hmy | exact Hmz]].
    - apply fdiv_ge; [exact Hvz1 | exact Hb1].
    - apply fdiv_le; [exact Hvz1 | exact Hb2]. }
  assert (Hsol : is_fdiv_asn (vy / vz) vy vz) by (split; [lia | reflexivity]).
  exact (Hct _ _ _ Hin Hsol Hvz1).
Qed.

Lemma flo_z1band_neg : forall yu vz a, a < 0 -> yu <> Ninf ->
  leq_zinf (cdiv_zinf yu (Fin a)) (Fin vz) -> leq_zinf (Fin (a * vz)) yu.
Proof.
  intros yu vz a Ha Hyn H.
  destruct yu as [u| |]; try congruence.
  - cbn [cdiv_zinf] in H. cbn in H. cbn. apply RC1; [lia | exact H].
  - cbn. exact I.
Qed.

Lemma flo_z2band_neg : forall yl vz b, b < -1 -> yl <> Pinf ->
  leq_zinf (Fin vz) (fdiv_zinf (addk_zinf yl 1) (addk_zinf (Fin b) 1)) ->
  leq_zinf yl (Fin ((b + 1) * vz - 1)).
Proof.
  intros yl vz b Hb Hyp H. cbn [addk_zinf] in H.
  destruct yl as [l| |]; try congruence.
  - cbn [addk_zinf fdiv_zinf] in H. cbn in H.
    assert (Hle : l + 1 <= (b + 1) * vz) by (apply mul_ge_div_neg; [lia | exact H]).
    cbn. lia.
  - cbn. exact I.
Qed.

Lemma flo_z1_lo : forall s z0,
  leq_zinf (lb z0) (lb (if ispos_zinf (lb (sx3 s))
        then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (ub (sy3 s)) (lb (sx3 s))))
        else if negb (iszero_zinf (lb (sx3 s)))
             then Itv (max_zinf (lb z0) (cdiv_zinf (ub (sy3 s)) (lb (sx3 s)))) (ub z0)
             else if isneg_zinf (ub (sy3 s)) then botitv else z0)).
Proof.
  intros s z0.
  destruct (ispos_zinf (lb (sx3 s))); [cbn [lb]; apply leq_zinf_refl | ].
  destruct (iszero_zinf (lb (sx3 s))); cbn [negb].
  - destruct (isneg_zinf (ub (sy3 s))); [cbn; apply leq_zinf_Pinf | cbn [lb]; apply leq_zinf_refl].
  - cbn [lb]; apply leq_zinf_max_zinf_l.
Qed.

Lemma flo_z1_hi : forall s z0,
  leq_zinf (ub (if ispos_zinf (lb (sx3 s))
        then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (ub (sy3 s)) (lb (sx3 s))))
        else if negb (iszero_zinf (lb (sx3 s)))
             then Itv (max_zinf (lb z0) (cdiv_zinf (ub (sy3 s)) (lb (sx3 s)))) (ub z0)
             else if isneg_zinf (ub (sy3 s)) then botitv else z0)) (ub z0).
Proof.
  intros s z0.
  destruct (ispos_zinf (lb (sx3 s))); [cbn [ub]; apply min_zinf_leq_zinf_l | ].
  destruct (iszero_zinf (lb (sx3 s))); cbn [negb].
  - destruct (isneg_zinf (ub (sy3 s))); [cbn | cbn [ub]; apply leq_zinf_refl].
    destruct (ub z0); exact I.
  - cbn [ub]; apply leq_zinf_refl.
Qed.

Lemma flo_z2_lo : forall s z0,
  leq_zinf (lb z0) (lb (if geq0_zinf (ub (sx3 s))
        then Itv (max_zinf (lb z0) (cdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1))) (ub z0)
        else if negb (zeqm1 (ub (sx3 s)))
             then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1)))
             else if geq0_zinf (lb (sy3 s)) then botitv else z0)).
Proof.
  intros s z0.
  destruct (geq0_zinf (ub (sx3 s))); [cbn [lb]; apply leq_zinf_max_zinf_l | ].
  destruct (zeqm1 (ub (sx3 s))); cbn [negb].
  - destruct (geq0_zinf (lb (sy3 s))); [cbn; apply leq_zinf_Pinf | cbn [lb]; apply leq_zinf_refl].
  - cbn [lb]; apply leq_zinf_refl.
Qed.

Lemma flo_z2_hi : forall s z0,
  leq_zinf (ub (if geq0_zinf (ub (sx3 s))
        then Itv (max_zinf (lb z0) (cdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1))) (ub z0)
        else if negb (zeqm1 (ub (sx3 s)))
             then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1)))
             else if geq0_zinf (lb (sy3 s)) then botitv else z0)) (ub z0).
Proof.
  intros s z0.
  destruct (geq0_zinf (ub (sx3 s))); [cbn [ub]; apply leq_zinf_refl | ].
  destruct (zeqm1 (ub (sx3 s))); cbn [negb].
  - destruct (geq0_zinf (lb (sy3 s))); [cbn | cbn [ub]; apply leq_zinf_refl].
    destruct (ub z0); exact I.
  - cbn [ub]; apply min_zinf_leq_zinf_l.
Qed.

Lemma flo_ycorner_lo : forall xl zl zu vz,
  leq_zinf (Fin 1) zl -> leq_zinf zl (Fin vz) -> leq_zinf (Fin vz) zu ->
  leq_zinf (min_zinf (mul_zinf xl zl) (mul_zinf xl zu)) (fyminZ xl vz).
Proof.
  intros xl zl zu vz Hz1 Hzl Hzu.
  destruct xl as [a| |]; cbn [fyminZ]; [ | apply leq_zinf_Pinf | ].
  - destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
    + eapply leq_zinf_trans; [apply min_zinf_leq_zinf_l | ]. cbn [mul_zinf]. cbn. nia.
    + eapply leq_zinf_trans; [apply min_zinf_leq_zinf_r | ].
      destruct zu as [u| |]; cbn in Hzu; try contradiction.
      * cbn [mul_zinf]. cbn. nia.
      * rewrite mul_zinf_fn by lia. exact I.
  - destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    eapply leq_zinf_trans; [apply min_zinf_leq_zinf_l | ]. rewrite mul_zinf_ninf_fp by lia. exact I.
Qed.

Lemma flo_ycorner_hi : forall xu zl zu vz,
  leq_zinf (Fin 1) zl -> leq_zinf zl (Fin vz) -> leq_zinf (Fin vz) zu ->
  leq_zinf (fymaxZ xu vz) (max_zinf (addk_zinf (mul_zinf (addk_zinf xu 1) zl) (-1))
                          (addk_zinf (mul_zinf (addk_zinf xu 1) zu) (-1))).
Proof.
  intros xu zl zu vz Hz1 Hzl Hzu.
  destruct xu as [b| |]; cbn [fymaxZ].
  - cbn [addk_zinf]. destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    destruct (Z.lt_trichotomy (b+1) 0) as [Hb|[Hb|Hb]].
    + eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ]. cbn [mul_zinf addk_zinf]. cbn. nia.
    + eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ]. rewrite Hb. cbn [mul_zinf addk_zinf]. cbn. nia.
    + eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ].
      destruct zu as [u| |]; cbn in Hzu; try contradiction.
      * cbn [mul_zinf addk_zinf]. cbn. nia.
      * rewrite mul_zinf_fp by lia. exact I.
  - cbn [addk_zinf]. destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ].
    rewrite mul_zinf_pinf_fp by lia. exact I.
  - exact I.
Qed.

Lemma fdiv_zinf_mono_num_pinf : forall n1 n2, leq_zinf n1 n2 -> leq_zinf (fdiv_zinf n1 Pinf) (fdiv_zinf n2 Pinf).
Proof.
  intros [a| |] [b| |] Hn; cbn in Hn |- *; try contradiction; try exact I;
    try (destruct (Z.ltb_spec a 0)); try (destruct (Z.ltb_spec b 0)); cbn; lia.
Qed.

Lemma flo_Hband : forall s z0 z1 z2,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  z1 = (if ispos_zinf (lb (sx3 s)) then Itv (lb z0) (min_zinf (ub z0) (fdiv_zinf (ub (sy3 s)) (lb (sx3 s))))
        else if negb (iszero_zinf (lb (sx3 s)))
             then Itv (max_zinf (lb z0) (cdiv_zinf (ub (sy3 s)) (lb (sx3 s)))) (ub z0)
             else if isneg_zinf (ub (sy3 s)) then botitv else z0) ->
  z2 = (if geq0_zinf (ub (sx3 s)) then Itv (max_zinf (lb z1) (cdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1))) (ub z1)
        else if negb (zeqm1 (ub (sx3 s)))
             then Itv (lb z1) (min_zinf (ub z1) (fdiv_zinf (addk_zinf (lb (sy3 s)) 1) (addk_zinf (ub (sx3 s)) 1)))
             else if geq0_zinf (lb (sy3 s)) then botitv else z1) ->
  nonempty3b z2 = true ->
  forall vz, 1 <= vz -> leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
  leq_zinf (fyminZ (lb (sx3 s)) vz) (ub (sy3 s)) /\ leq_zinf (lb (sy3 s)) (fymaxZ (ub (sx3 s)) vz).
Proof.
  intros s z0 z1 z2 Hx Hy Hz1 Hz2 E2 vz Hvz1 Hvlo Hvhi.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  assert (Hlo12 : leq_zinf (lb z1) (lb z2)) by (rewrite Hz2; apply (flo_z2_lo s z1)).
  assert (Hhi12 : leq_zinf (ub z2) (ub z1)) by (rewrite Hz2; apply (flo_z2_hi s z1)).
  split.
  - destruct (lb (sx3 s)) as [a| |] eqn:Exl; [ | congruence | ].
    2:{ cbn [fyminZ]. destruct (ub (sy3 s)); exact I. }
    cbn [fyminZ].
    destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
    + assert (Hzp : ispos_zinf (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
      assert (Hzz : iszero_zinf (Fin a) = false) by (cbn; apply Z.eqb_neq; lia).
      rewrite Hzp, Hzz in Hz1. cbn [negb] in Hz1.
      apply (flo_z1band_neg (ub (sy3 s)) vz a Ha Hyun).
      eapply leq_zinf_trans; [ | eapply leq_zinf_trans; [exact Hlo12 | exact Hvlo] ].
      rewrite Hz1; cbn [lb]. apply leq_zinf_max_zinf_r.
    + subst a. assert (Hzp : ispos_zinf (Fin 0) = false) by reflexivity.
      assert (Hzz : iszero_zinf (Fin 0) = true) by reflexivity.
      rewrite Hzp, Hzz in Hz1. cbn [negb] in Hz1.
      destruct (isneg_zinf (ub (sy3 s))) eqn:Eyn.
      * rewrite Hz1 in Hlo12. cbn [lb] in Hlo12.
        destruct (lb z2) as [m| |] eqn:Em; cbn in Hlo12; try contradiction; congruence.
      * destruct (ub (sy3 s)) as [u| |] eqn:Ey; cbn in Eyn |- *.
        -- apply Z.ltb_ge in Eyn. lia.
        -- exact I.
        -- congruence.
    + assert (Hzp : ispos_zinf (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
      rewrite Hzp in Hz1.
      apply (z1band_pos (ub (sy3 s)) vz a Ha Hyun).
      eapply leq_zinf_trans; [exact Hvhi | ]. eapply leq_zinf_trans; [exact Hhi12 | ].
      rewrite Hz1; cbn [ub]. apply min_zinf_leq_zinf_r.
  - destruct (ub (sx3 s)) as [b| |] eqn:Exu; [ | | congruence ].
    2:{ cbn [fymaxZ]. destruct (lb (sy3 s)); exact I. }
    cbn [fymaxZ].
    destruct (Z.lt_trichotomy b (-1)) as [Hb|[Hb|Hb]].
    + assert (Hzg : geq0_zinf (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
      assert (Hze : zeqm1 (Fin b) = false) by (cbn; apply Z.eqb_neq; lia).
      rewrite Hzg, Hze in Hz2. cbn [negb] in Hz2.
      apply (flo_z2band_neg (lb (sy3 s)) vz b Hb Hylp).
      eapply leq_zinf_trans; [exact Hvhi | ].
      rewrite Hz2; cbn [ub]. apply min_zinf_leq_zinf_r.
    + subst b. assert (Hzg : geq0_zinf (Fin (-1)) = false) by reflexivity.
      assert (Hze : zeqm1 (Fin (-1)) = true) by reflexivity.
      rewrite Hzg, Hze in Hz2. cbn [negb] in Hz2.
      destruct (geq0_zinf (lb (sy3 s))) eqn:Eyl.
      * exfalso. rewrite Hz2 in E2. discriminate.
      * destruct (lb (sy3 s)) as [l| |] eqn:Ey; cbn in Eyl |- *.
        -- apply Z.leb_gt in Eyl. lia.
        -- congruence.
        -- exact I.
    + assert (Hzg : geq0_zinf (Fin b) = true) by (cbn; apply Z.leb_le; lia).
      rewrite Hzg in Hz2.
      apply (z2band_pos (lb (sy3 s)) vz b ltac:(lia) Hylp).
      eapply leq_zinf_trans; [ | exact Hvlo ].
      rewrite Hz2; cbn [lb]. apply leq_zinf_max_zinf_r.
Qed.

Lemma zfpos3_band : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (zfdiv_pos3 s) = true ->
  exists vz, 1 <= vz /\ mem3 (sz3 s) vz
    /\ leq_zinf (fyminZ (lb (sx3 s)) vz) (ub (sy3 s))
    /\ leq_zinf (lb (sy3 s)) (fymaxZ (ub (sx3 s)) vz).
Proof.
  intros s Hx Hy Hne.
  unfold zfdiv_pos3 in Hne; cbv zeta in Hne.
  match type of Hne with context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : leq_zinf (Fin 1) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_r).
  assert (Hz0hi : ub z0 = ub (sz3 s)) by (rewrite Hz0; cbn [ub]; reflexivity).
  assert (Hz0lo : leq_zinf (lb (sz3 s)) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_l).
  destruct (nonempty3b z0) eqn:E0; cbn [negb] in Hne;
    [ | unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne;
        rewrite E0, !andb_false_r in Hne; discriminate ].
  match type of Hne with context[if ispos_zinf (lb (sx3 s)) then ?A else ?B] =>
    remember (if ispos_zinf (lb (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : leq_zinf (Fin 1) (lb z1)) by (rewrite Hz1; apply flo_z1_pos; exact Hz0l1).
  assert (Hlo01 : leq_zinf (lb z0) (lb z1)) by (rewrite Hz1; apply (flo_z1_lo s z0)).
  assert (Hhi01 : leq_zinf (ub z1) (ub z0)) by (rewrite Hz1; apply (flo_z1_hi s z0)).
  match type of Hne with context[if geq0_zinf (ub (sx3 s)) then ?A else ?B] =>
    remember (if geq0_zinf (ub (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : leq_zinf (Fin 1) (lb z2)) by (rewrite Hz2; apply flo_z2_pos; exact Hz1l1).
  assert (Hlo12 : leq_zinf (lb z1) (lb z2)) by (rewrite Hz2; apply (flo_z2_lo s z1)).
  assert (Hhi12 : leq_zinf (ub z2) (ub z1)) by (rewrite Hz2; apply (flo_z2_hi s z1)).
  destruct (nonempty3b z2) eqn:E2; cbn [negb] in Hne;
    [ | unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne;
        rewrite E2, !andb_false_r in Hne; discriminate ].
  clear Hne.
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  pose proof (ne_leq_zinf _ E2) as Hz2ne.
  destruct (fin_of_ge1 (lb z2) Hz2l1 Hz2lp) as [zv [Ez2lo Hvz1]].
  exists zv. split; [exact Hvz1 | ].
  assert (Hzvhi : leq_zinf (Fin zv) (ub (sz3 s))).
  { rewrite <- Hz0hi. eapply leq_zinf_trans; [ | exact Hhi01].
    eapply leq_zinf_trans; [ | exact Hhi12]. rewrite <- Ez2lo. exact Hz2ne. }
  assert (Hzvlo : leq_zinf (lb (sz3 s)) (Fin zv)).
  { rewrite <- Ez2lo. eapply leq_zinf_trans; [exact Hz0lo | ].
    eapply leq_zinf_trans; [exact Hlo01 | exact Hlo12]. }
  split; [ split; [exact Hzvlo | exact Hzvhi] | ].
  assert (Hzvlo2 : leq_zinf (lb z2) (Fin zv)) by (rewrite Ez2lo; apply leq_zinf_refl).
  assert (Hzvhi2 : leq_zinf (Fin zv) (ub z2)) by (rewrite <- Ez2lo; exact Hz2ne).
  apply (flo_Hband s z0 z1 z2 Hx Hy Hz1 Hz2 E2 zv Hvz1 Hzvlo2 Hzvhi2).
Qed.

Theorem fpos_ne_feasible : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (zfdiv_pos3 s) = true -> slice_feasible is_fdiv_asn s.
Proof.
  intros s Hx Hy Hne.
  destruct (zfpos3_band s Hx Hy Hne) as [vz [Hvz1 [Hmz [Hb1 Hb2]]]].
  pose proof (ne_leq_zinf _ Hx) as Hxle.
  pose proof (ne_leq_zinf _ Hy) as Hyle.
  pose proof (fband_ne (lb (sx3 s)) (ub (sx3 s)) vz Hvz1 Hxle) as Hbn.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  set (L := max_zinf (fyminZ (lb (sx3 s)) vz) (lb (sy3 s))).
  set (U := min_zinf (fymaxZ (ub (sx3 s)) vz) (ub (sy3 s))).
  assert (HLU : leq_zinf L U).
  { unfold L, U. apply leq_zinf_min_zinf_glb.
    - apply max_zinf_lub; [exact Hbn | exact Hb2].
    - apply max_zinf_lub; [exact Hb1 | exact Hyle]. }
  assert (HLp : L <> Pinf)
    by (unfold L; apply max_zinf_not_Pinf; [apply fyminZ_not_Pinf; exact Hxlp | exact Hylp]).
  assert (HUn : U <> Ninf)
    by (unfold U; apply min_zinf_not_Ninf; [apply fymaxZ_not_Ninf; exact Hxun | exact Hyun]).
  destruct (pickf_mem L U HLU HLp HUn) as [HLvy HvyU].
  unfold L in HLvy. unfold U in HvyU.
  set (vy := pickf L U) in *.
  exists (vy / vz), vy, vz.
  split.
  - split; [ | split ].
    + split.
      * apply fdiv_ge; [exact Hvz1 | eapply leq_zinf_trans; [apply leq_zinf_max_zinf_l | exact HLvy]].
      * apply fdiv_le; [exact Hvz1 | eapply leq_zinf_trans; [exact HvyU | apply min_zinf_leq_zinf_l]].
    + split.
      * eapply leq_zinf_trans; [apply leq_zinf_max_zinf_r | exact HLvy].
      * eapply leq_zinf_trans; [exact HvyU | apply min_zinf_leq_zinf_r].
    + exact Hmz.
  - split; [ split; [lia | reflexivity] | exact Hvz1 ].
Qed.

Theorem fpos_best : forall s, slice_feasible is_fdiv_asn s ->
  forall t, slice_contains is_fdiv_asn s t -> sle3 (zfdiv_pos3 s) t.
Proof.
  intros s Hfeas t Hct.
  destruct Hfeas as (fx & fy & fz & Hfin & Hfts & Hfz1).
  assert (HneO : ne_store3 (zfdiv_pos3 s) = true).
  { eapply ne_store3_true. apply fpos_sound; [exact Hfin | exact Hfts | exact Hfz1]. }
  destruct Hfin as (Hfxm & Hfym & Hfzm).
  assert (Hx : nonempty3b (sx3 s) = true) by (eapply nonempty3b_true; exact Hfxm).
  assert (Hy : nonempty3b (sy3 s) = true) by (eapply nonempty3b_true; exact Hfym).
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  pose proof (ne_leq_zinf _ Hx) as Hxle.
  pose proof (ne_leq_zinf _ Hy) as Hyle.
  unfold zfdiv_pos3 in HneO |- *; cbv zeta in HneO |- *.
  match goal with |- context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : leq_zinf (Fin 1) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_r).
  assert (Hz0hi : ub z0 = ub (sz3 s)) by (rewrite Hz0; cbn [ub]; reflexivity).
  assert (Hz0lo : leq_zinf (lb (sz3 s)) (lb z0)) by (rewrite Hz0; cbn [lb]; apply leq_zinf_max_zinf_l).
  destruct (nonempty3b z0) eqn:E0; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite E0, !andb_false_r in HneO; discriminate ].
  match goal with |- context[if ispos_zinf (lb (sx3 s)) then ?A else ?B] =>
    remember (if ispos_zinf (lb (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : leq_zinf (Fin 1) (lb z1)) by (rewrite Hz1; apply flo_z1_pos; exact Hz0l1).
  assert (Hlo01 : leq_zinf (lb z0) (lb z1)) by (rewrite Hz1; apply (flo_z1_lo s z0)).
  assert (Hhi01 : leq_zinf (ub z1) (ub z0)) by (rewrite Hz1; apply (flo_z1_hi s z0)).
  match goal with |- context[if geq0_zinf (ub (sx3 s)) then ?A else ?B] =>
    remember (if geq0_zinf (ub (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : leq_zinf (Fin 1) (lb z2)) by (rewrite Hz2; apply flo_z2_pos; exact Hz1l1).
  assert (Hlo12 : leq_zinf (lb z1) (lb z2)) by (rewrite Hz2; apply (flo_z2_lo s z1)).
  assert (Hhi12 : leq_zinf (ub z2) (ub z1)) by (rewrite Hz2; apply (flo_z2_hi s z1)).
  destruct (nonempty3b z2) eqn:E2; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite E2, !andb_false_r in HneO; discriminate ].
  match goal with |- context[nonempty3b ?Y] => remember Y as yF eqn:HyF end.
  destruct (nonempty3b yF) eqn:EY; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite EY, !andb_false_r in HneO; discriminate ].
  assert (Hv1 : forall vz, leq_zinf (lb z2) (Fin vz) -> 1 <= vz).
  { intros vz Hvlo. assert (HH : leq_zinf (Fin 1) (Fin vz)) by (eapply leq_zinf_trans; [exact Hz2l1 | exact Hvlo]).
    cbn in HH. lia. }
  assert (Hband : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (fyminZ (lb (sx3 s)) vz) (ub (sy3 s)) /\ leq_zinf (lb (sy3 s)) (fymaxZ (ub (sx3 s)) vz)).
  { intros vz Hvlo Hvhi. apply (flo_Hband s z0 z1 z2 Hx Hy Hz1 Hz2 E2 vz (Hv1 vz Hvlo) Hvlo Hvhi). }
  assert (Hmemz : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) -> mem3 (sz3 s) vz).
  { intros vz Hvlo Hvhi. unfold mem3. split.
    - eapply leq_zinf_trans; [exact Hz0lo | ]. eapply leq_zinf_trans; [exact Hlo01 | ].
      eapply leq_zinf_trans; [exact Hlo12 | exact Hvlo].
    - rewrite <- Hz0hi. eapply leq_zinf_trans; [exact Hvhi | ].
      eapply leq_zinf_trans; [exact Hhi12 | exact Hhi01]. }
  assert (Hwit : forall vz vy, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    mem3 (sy3 s) vy -> leq_zinf (fyminZ (lb (sx3 s)) vz) (Fin vy) -> leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) vz) ->
    mem3 (sx3 t) (vy / vz) /\ mem3 (sy3 t) vy /\ mem3 (sz3 t) vz).
  { intros vz vy Hvlo Hvhi Hmy Hby1 Hby2.
    apply (fwit_in_t s t vz vy Hct (Hv1 vz Hvlo) (Hmemz vz Hvlo Hvhi) Hmy Hby1 Hby2). }
  assert (Hpickvy : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    exists vy, mem3 (sy3 s) vy /\ leq_zinf (fyminZ (lb (sx3 s)) vz) (Fin vy) /\ leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) vz)).
  { intros vz Hvlo Hvhi.
    destruct (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (fband_ne (lb (sx3 s)) (ub (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    set (L := max_zinf (fyminZ (lb (sx3 s)) vz) (lb (sy3 s))).
    set (U := min_zinf (fymaxZ (ub (sx3 s)) vz) (ub (sy3 s))).
    assert (HLU : leq_zinf L U).
    { unfold L, U. apply leq_zinf_min_zinf_glb.
      - apply max_zinf_lub; [exact Hbn | exact Hb2].
      - apply max_zinf_lub; [exact Hb1 | exact Hyle]. }
    assert (HLp : L <> Pinf) by (unfold L; apply max_zinf_not_Pinf; [apply fyminZ_not_Pinf; exact Hxlp | exact Hylp]).
    assert (HUn : U <> Ninf) by (unfold U; apply min_zinf_not_Ninf; [apply fymaxZ_not_Ninf; exact Hxun | exact Hyun]).
    destruct (pickf_mem L U HLU HLp HUn) as [HLvy HvyU].
    unfold L in HLvy. unfold U in HvyU.
    exists (pickf L U). split; [ | split].
    - split; [ eapply leq_zinf_trans; [apply leq_zinf_max_zinf_r | exact HLvy] | eapply leq_zinf_trans; [exact HvyU | apply min_zinf_leq_zinf_r] ].
    - eapply leq_zinf_trans; [apply leq_zinf_max_zinf_l | exact HLvy].
    - eapply leq_zinf_trans; [exact HvyU | apply min_zinf_leq_zinf_l]. }
  assert (Hft : in_store3 t fx fy fz)
    by (apply Hct; [split; [exact Hfxm | split; [exact Hfym | exact Hfzm]] | exact Hfts | exact Hfz1]).
  destruct Hft as (Hftx & Hfty & Hftz).
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  pose proof (ne_leq_zinf _ E2) as Hz2ne.
  destruct (fin_of_ge1 (lb z2) Hz2l1 Hz2lp) as [zlo2 [Hzlo2 Hzlo21]].
  assert (Hzlo2lo : leq_zinf (lb z2) (Fin zlo2)) by (rewrite Hzlo2; apply leq_zinf_refl).
  assert (Hzlo2hi : leq_zinf (Fin zlo2) (ub z2)) by (rewrite <- Hzlo2; exact Hz2ne).
  assert (Hatt : forall vz vy, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (lb (sy3 s)) (Fin vy) -> leq_zinf (Fin vy) (ub (sy3 s)) ->
    leq_zinf (fyminZ (lb (sx3 s)) vz) (Fin vy) -> leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) vz) ->
    leq_zinf (lb (sy3 t)) (Fin vy) /\ leq_zinf (Fin vy) (ub (sy3 t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (_ & Hmyt & _).
    split; [apply (mem3_lo _ _ Hmyt) | apply (mem3_hi _ _ Hmyt)]. }
  assert (Hattx : forall vz vy, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (lb (sy3 s)) (Fin vy) -> leq_zinf (Fin vy) (ub (sy3 s)) ->
    leq_zinf (fyminZ (lb (sx3 s)) vz) (Fin vy) -> leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) vz) ->
    leq_zinf (lb (sx3 t)) (Fin (vy / vz)) /\ leq_zinf (Fin (vy / vz)) (ub (sx3 t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (Hmxt & _ & _).
    split; [apply (mem3_lo _ _ Hmxt) | apply (mem3_hi _ _ Hmxt)]. }
  pose proof (ne_leq_zinf _ EY) as Hyfne.
  assert (Hyfyl : leq_zinf (lb (sy3 s)) (lb yF)) by (rewrite HyF; cbn [lb]; apply leq_zinf_max_zinf_l).
  assert (Hyfyh : leq_zinf (ub yF) (ub (sy3 s))) by (rewrite HyF; cbn [ub]; apply min_zinf_leq_zinf_l).
  assert (Hyflo_hi : leq_zinf (lb yF) (ub (sy3 s))) by (eapply leq_zinf_trans; [exact Hyfne | exact Hyfyh]).
  assert (Hyfhi_lo : leq_zinf (lb (sy3 s)) (ub yF)) by (eapply leq_zinf_trans; [exact Hyfyl | exact Hyfne]).
  apply sle3_intro; cbn [sx3 sy3 sz3].
  assert (Hlyf : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (lb yF) (fymaxZ (ub (sx3 s)) vz)).
  { intros vz Hvlo Hvhi.
    pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (fband_ne (lb (sx3 s)) (ub (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    rewrite HyF; cbn [lb]. apply max_zinf_lub; [exact Hb2 | ].
    eapply leq_zinf_trans; [ | exact Hbn ].
    apply (flo_ycorner_lo (lb (sx3 s)) (lb z2) (ub z2) vz Hz2l1 Hvlo Hvhi). }
  assert (Hhyf : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
    leq_zinf (fyminZ (lb (sx3 s)) vz) (ub yF)).
  { intros vz Hvlo Hvhi.
    pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (fband_ne (lb (sx3 s)) (ub (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    rewrite HyF; cbn [ub]. apply leq_zinf_min_zinf_glb; [exact Hb1 | ].
    eapply leq_zinf_trans; [ exact Hbn | ].
    apply (flo_ycorner_hi (ub (sx3 s)) (lb z2) (ub z2) vz Hz2l1 Hvlo Hvhi). }
  assert (Hbf : forall X a, leqb_zinf (Fin a) X = false -> leq_zinf X (Fin (a - 1))).
  { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | discriminate | exact I ]. }
  apply ile3_intro; cbn [lb ub].
  { assert (Hcx : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
      forall ylv, lb yF = Fin ylv -> leq_zinf (lb (sx3 s)) (Fin (ylv / vz)) ->
      leq_zinf (lb (sx3 t)) (Fin (ylv / vz))).
    { intros vz Hvlo Hvhi ylv Eyl Hxc.
      assert (Hbl : leq_zinf (fyminZ (lb (sx3 s)) vz) (Fin ylv)).
      { destruct (lb (sx3 s)) as [a| |] eqn:Exl; cbn [fyminZ].
        - cbn in Hxc. cbn. apply (floor_lb a ylv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
        - cbn in Hxc. contradiction.
        - exact I. }
      assert (Hbu : leq_zinf (Fin ylv) (fymaxZ (ub (sx3 s)) vz)) by (rewrite <- Eyl; apply (Hlyf vz Hvlo Hvhi)).
      assert (Hy1 : leq_zinf (lb (sy3 s)) (Fin ylv)) by (rewrite <- Eyl; exact Hyfyl).
      assert (Hy2 : leq_zinf (Fin ylv) (ub (sy3 s))) by (rewrite <- Eyl; exact Hyflo_hi).
      destruct (Hattx vz ylv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [HH _]. exact HH. }
    destruct (leqb_zinf (lb (sx3 s)) (min_zinf (min_zinf (fdiv_zinf (lb yF) (lb z2)) (fdiv_zinf (lb yF) (ub z2)))
       (min_zinf (fdiv_zinf (ub yF) (lb z2)) (fdiv_zinf (ub yF) (ub z2))))) eqn:Hclip.
    - apply leq_zinf_prop_bool_equiv in Hclip.
      eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ].
      destruct (lb yF) as [ylv| |] eqn:Eyl.
      + assert (Hcll : leq_zinf (lb (sx3 s)) (fdiv_zinf (Fin ylv) (lb z2))).
        { eapply leq_zinf_trans; [exact Hclip | ]. eapply leq_zinf_trans; [apply min_zinf_leq_zinf_l | apply min_zinf_leq_zinf_l]. }
        assert (Hclh : leq_zinf (lb (sx3 s)) (fdiv_zinf (Fin ylv) (ub z2))).
        { eapply leq_zinf_trans; [exact Hclip | ]. eapply leq_zinf_trans; [apply min_zinf_leq_zinf_l | apply min_zinf_leq_zinf_r]. }
        assert (HA : leq_zinf (lb (sx3 t)) (min_zinf (fdiv_zinf (Fin ylv) (lb z2)) (fdiv_zinf (Fin ylv) (ub z2)))).
        { apply leq_zinf_min_zinf_glb.
          - rewrite Hzlo2 in Hcll |- *. cbn [fdiv_zinf] in Hcll |- *. apply (Hcx zlo2 Hzlo2lo Hzlo2hi ylv eq_refl Hcll).
          - destruct (ub z2) as [zh| |] eqn:Eh.
            + cbn [fdiv_zinf] in Hclh |- *. apply (Hcx zh Hz2ne (leq_zinf_refl _) ylv eq_refl Hclh).
            + cbn [fdiv_zinf] in Hclh |- *.
              assert (Hq0 : ylv / (Z.max zlo2 (Z.abs ylv + 1)) = (if ylv <? 0 then -1 else 0)).
              { destruct (Z.ltb_spec ylv 0) as [Hn|Hp].
                - assert (HL0 : 0 < Z.max zlo2 (Z.abs ylv + 1)) by lia.
                  assert (ylv / (Z.max zlo2 (Z.abs ylv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                  assert (-1 <= ylv / (Z.max zlo2 (Z.abs ylv + 1))) by (apply Z.div_le_lower_bound; lia).
                  lia.
                - apply Z.div_small. lia. }
              rewrite <- Hq0. apply (Hcx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _) ylv eq_refl).
              rewrite Hq0. exact Hclh.
            + congruence. }
        apply leq_zinf_min_zinf_glb; [exact HA | ].
        eapply leq_zinf_trans; [exact HA | ].
        apply leq_zinf_min_zinf_glb.
        * eapply leq_zinf_trans; [apply min_zinf_leq_zinf_l | rewrite Hzlo2; apply fdiv_zinf_mono_pos; [exact Hyfne | lia] ].
        * eapply leq_zinf_trans; [apply min_zinf_leq_zinf_r | ].
          destruct (ub z2) as [zh| |] eqn:Eh.
          { apply fdiv_zinf_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia]. }
          { destruct (ub yF) as [yhv| |] eqn:Eyh; cbn in Hyfne.
            - cbn [fdiv_zinf]. destruct (Z.ltb_spec ylv 0); destruct (Z.ltb_spec yhv 0); cbn; lia.
            - cbn [fdiv_zinf]. destruct (ylv <? 0); cbn; lia.
            - contradiction. }
          { congruence. }
      + pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
      + assert (En : fdiv_zinf Ninf (Fin zlo2) = Ninf) by (cbn [fdiv_zinf]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
        rewrite Hzlo2, En. cbn [min_zinf].
        assert (Hxn : lb (sx3 s) = Ninf).
        { pose proof Hclip as HC. rewrite Hzlo2, En in HC. cbn [min_zinf] in HC. destruct (lb (sx3 s)) eqn:E; try reflexivity; cbn in HC; contradiction. }
        assert (Hyn : lb (sy3 s) = Ninf).
        { pose proof Hyfyl as HH. destruct (lb (sy3 s)) eqn:E; try reflexivity; cbn in HH; contradiction. }
        destruct (lb (sx3 t)) as [M| |] eqn:EtL; [ | | exact I ].
        2:{ exfalso. pose proof (mem3_lo (sx3 t) fx Hftx) as HH. rewrite EtL in HH. cbn in HH. exact HH. }
        exfalso.
        destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy0 [Hmy0 [Hby1 Hby2]]].
        set (vy := Z.min vy0 ((M-1) * zlo2)).
        assert (Hmemy : mem3 (sy3 s) vy).
        { split; [rewrite Hyn; exact I | eapply leq_zinf_trans; [ | apply (mem3_hi _ _ Hmy0)]; cbn; unfold vy; lia]. }
        assert (Hbl : leq_zinf (fyminZ (lb (sx3 s)) zlo2) (Fin vy)) by (rewrite Hxn; cbn; exact I).
        assert (Hbu : leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) zlo2)) by (eapply leq_zinf_trans; [ | exact Hby2]; cbn; unfold vy; lia).
        destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
        pose proof (mem3_lo (sx3 t) _ Hmxt) as HH. rewrite EtL in HH. cbn in HH.
        assert (Hqle : vy / zlo2 <= ((M-1) * zlo2) / zlo2) by (apply Z.div_le_mono; [lia | unfold vy; lia]).
        rewrite Z.div_mul in Hqle by lia. lia.
    - eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ].
      destruct (lb (sx3 s)) as [xl| |] eqn:Exl; [ | congruence | cbn [leqb_zinf] in Hclip; discriminate ].
      assert (Hclipx : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
        leq_zinf (fdiv_zinf (lb yF) (Fin vz)) (Fin (xl - 1)) -> leq_zinf (lb (sx3 t)) (Fin xl)).
      { intros vz Hvlo Hvhi Hcorner.
        pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
        destruct (fattain_vx (Fin xl) (ub (sx3 s)) vz xl ltac:(pose proof (Hv1 vz Hvlo); lia) (leq_zinf_refl _) Hxle) as (Hbl & Hbu & Hqeq).
        set (vy := xl * vz) in *.
        assert (Hvyhi : leq_zinf (Fin vy) (ub (sy3 s))) by (unfold vy; cbn [fyminZ] in Hb1; exact Hb1).
        assert (Hvylo : leq_zinf (lb (sy3 s)) (Fin vy)).
        { eapply leq_zinf_trans; [exact Hyfyl | ].
          destruct (lb yF) as [ylv| |] eqn:Eyl.
          - cbn [fdiv_zinf] in Hcorner. cbn in Hcorner. cbn.
            destruct (Z.lt_ge_cases ylv vy) as [H|H]; [lia | exfalso].
            pose proof (Z.div_le_mono vy ylv vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
          - pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
          - exact I. }
        destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [HH _]. rewrite Hqeq in HH. exact HH. }
      destruct (leqb_zinf (Fin xl) (fdiv_zinf (lb yF) (lb z2))) eqn:Ell.
      + destruct (ub z2) as [zh| |] eqn:Eh.
        * apply (Hclipx zh Hz2ne (leq_zinf_refl _)).
          destruct (leqb_zinf (Fin xl) (fdiv_zinf (lb yF) (Fin zh))) eqn:Elh.
          -- exfalso. apply leq_zinf_prop_bool_equiv in Ell, Elh.
             assert (Hge : leq_zinf (Fin xl) (min_zinf (min_zinf (fdiv_zinf (lb yF) (lb z2)) (fdiv_zinf (lb yF) (Fin zh)))
               (min_zinf (fdiv_zinf (ub yF) (lb z2)) (fdiv_zinf (ub yF) (Fin zh))))).
             { apply leq_zinf_min_zinf_glb; apply leq_zinf_min_zinf_glb; try assumption.
               - eapply leq_zinf_trans; [exact Ell | rewrite Hzlo2; apply fdiv_zinf_mono_pos; [exact Hyfne | lia] ].
               - eapply leq_zinf_trans; [exact Elh | apply fdiv_zinf_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia] ]. }
             apply leq_zinf_prop_bool_equiv in Hge. rewrite Hge in Hclip. discriminate.
          -- apply Hbf. exact Elh.
        * destruct (Z.le_gt_cases xl 0) as [Hxl0|Hxl0].
          -- exfalso. apply leq_zinf_prop_bool_equiv in Ell. rewrite Hzlo2 in Ell.
             assert (Hcp : forall yb, leq_zinf (Fin xl) (fdiv_zinf yb (Fin zlo2)) -> leq_zinf (Fin xl) (fdiv_zinf yb Pinf)).
             { intros yb Hyb. destruct yb as [v| |]; cbn [fdiv_zinf] in Hyb |- *.
               - destruct (Z.ltb_spec v 0) as [Hn|Hp]; cbn in Hyb |- *.
                 + assert (v / zlo2 < 0) by (apply Z.div_lt_upper_bound; lia). lia.
                 + lia.
               - cbn; lia.
               - rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)) in Hyb. cbn in Hyb. contradiction. }
             assert (Hge : leq_zinf (Fin xl) (min_zinf (min_zinf (fdiv_zinf (lb yF) (lb z2)) (fdiv_zinf (lb yF) Pinf))
               (min_zinf (fdiv_zinf (ub yF) (lb z2)) (fdiv_zinf (ub yF) Pinf)))).
             { apply leq_zinf_min_zinf_glb; apply leq_zinf_min_zinf_glb.
               - rewrite Hzlo2. exact Ell.
               - apply Hcp. exact Ell.
               - rewrite Hzlo2. eapply leq_zinf_trans; [exact Ell | apply fdiv_zinf_mono_pos; [exact Hyfne | lia] ].
               - apply Hcp. eapply leq_zinf_trans; [exact Ell | apply fdiv_zinf_mono_pos; [exact Hyfne | lia] ]. }
             apply leq_zinf_prop_bool_equiv in Hge. rewrite Hge in Hclip. discriminate.
          -- destruct (lb yF) as [ylv| |] eqn:Eyl.
             ++ apply (Hclipx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                cbn [fdiv_zinf].
                assert (Hq0 : ylv / (Z.max zlo2 (Z.abs ylv + 1)) = (if ylv <? 0 then -1 else 0)).
                { destruct (Z.ltb_spec ylv 0) as [Hn|Hp].
                  - assert (HL0 : 0 < Z.max zlo2 (Z.abs ylv + 1)) by lia.
                    assert (ylv / (Z.max zlo2 (Z.abs ylv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                    assert (-1 <= ylv / (Z.max zlo2 (Z.abs ylv + 1))) by (apply Z.div_le_lower_bound; lia).
                    lia.
                  - apply Z.div_small. lia. }
                rewrite Hq0. destruct (ylv <? 0); cbn; lia.
             ++ pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
             ++ apply (Hclipx (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                cbn [fdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). cbn. lia.
        * congruence.
      + apply (Hclipx zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ell. apply Hbf. exact Ell. }
  { assert (Hcxu : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
      forall yhv, ub yF = Fin yhv -> leq_zinf (Fin (yhv / vz)) (ub (sx3 s)) ->
      leq_zinf (Fin (yhv / vz)) (ub (sx3 t))).
    { intros vz Hvlo Hvhi yhv Eyh Hxc.
      assert (Hbu : leq_zinf (Fin yhv) (fymaxZ (ub (sx3 s)) vz)).
      { destruct (ub (sx3 s)) as [b| |] eqn:Exu; cbn [fymaxZ].
        - cbn in Hxc. cbn. apply (floor_ub b yhv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
        - exact I.
        - cbn in Hxc. contradiction. }
      assert (Hbl : leq_zinf (fyminZ (lb (sx3 s)) vz) (Fin yhv)) by (rewrite <- Eyh; apply (Hhyf vz Hvlo Hvhi)).
      assert (Hy1 : leq_zinf (lb (sy3 s)) (Fin yhv)) by (rewrite <- Eyh; exact Hyfhi_lo).
      assert (Hy2 : leq_zinf (Fin yhv) (ub (sy3 s))) by (rewrite <- Eyh; exact Hyfyh).
      destruct (Hattx vz yhv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [_ HH]. exact HH. }
    destruct (leqb_zinf (max_zinf (max_zinf (fdiv_zinf (lb yF) (lb z2)) (fdiv_zinf (lb yF) (ub z2)))
       (max_zinf (fdiv_zinf (ub yF) (lb z2)) (fdiv_zinf (ub yF) (ub z2)))) (ub (sx3 s))) eqn:Hclip.
    - apply leq_zinf_prop_bool_equiv in Hclip.
      eapply leq_zinf_trans; [ apply min_zinf_leq_zinf_r | ].
      destruct (ub yF) as [yhv| |] eqn:Eyh.
      + assert (Hchl : leq_zinf (fdiv_zinf (Fin yhv) (lb z2)) (ub (sx3 s))).
        { eapply leq_zinf_trans; [ | exact Hclip ]. eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r]. apply leq_zinf_max_zinf_l. }
        assert (Hchh : leq_zinf (fdiv_zinf (Fin yhv) (ub z2)) (ub (sx3 s))).
        { eapply leq_zinf_trans; [ | exact Hclip ]. eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r]. apply leq_zinf_max_zinf_r. }
        assert (HA : leq_zinf (max_zinf (fdiv_zinf (Fin yhv) (lb z2)) (fdiv_zinf (Fin yhv) (ub z2))) (ub (sx3 t))).
        { apply max_zinf_lub.
          - rewrite Hzlo2 in Hchl |- *. cbn [fdiv_zinf] in Hchl |- *. apply (Hcxu zlo2 Hzlo2lo Hzlo2hi yhv eq_refl Hchl).
          - destruct (ub z2) as [zh| |] eqn:Eh.
            + cbn [fdiv_zinf] in Hchh |- *. apply (Hcxu zh Hz2ne (leq_zinf_refl _) yhv eq_refl Hchh).
            + cbn [fdiv_zinf] in Hchh |- *.
              assert (Hq0 : yhv / (Z.max zlo2 (Z.abs yhv + 1)) = (if yhv <? 0 then -1 else 0)).
              { destruct (Z.ltb_spec yhv 0) as [Hn|Hp].
                - assert (HL0 : 0 < Z.max zlo2 (Z.abs yhv + 1)) by lia.
                  assert (yhv / (Z.max zlo2 (Z.abs yhv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                  assert (-1 <= yhv / (Z.max zlo2 (Z.abs yhv + 1))) by (apply Z.div_le_lower_bound; lia).
                  lia.
                - apply Z.div_small. lia. }
              rewrite <- Hq0. apply (Hcxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _) yhv eq_refl).
              rewrite Hq0. exact Hchh.
            + congruence. }
        apply max_zinf_lub; [ | exact HA ].
        eapply leq_zinf_trans; [ | exact HA ].
        apply max_zinf_lub.
        * eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_l ]. rewrite Hzlo2. apply fdiv_zinf_mono_pos; [exact Hyfne | lia].
        * eapply leq_zinf_trans; [ | apply leq_zinf_max_zinf_r ].
          destruct (ub z2) as [zh| |] eqn:Eh.
          { apply fdiv_zinf_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia]. }
          { apply fdiv_zinf_mono_num_pinf. exact Hyfne. }
          { congruence. }
      + assert (Ep : fdiv_zinf Pinf (Fin zlo2) = Pinf) by (cbn [fdiv_zinf]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
        assert (Hzp : forall x, max_zinf x Pinf = Pinf) by (intros [?| |]; reflexivity).
        rewrite Hzlo2, Ep. cbn [max_zinf]. rewrite Hzp.
        assert (Hxp : ub (sx3 s) = Pinf).
        { pose proof Hclip as HC. rewrite Hzlo2, Ep in HC. cbn [max_zinf] in HC. rewrite Hzp in HC. destruct (ub (sx3 s)) eqn:E; try reflexivity; cbn in HC; contradiction. }
        assert (Hyp : ub (sy3 s) = Pinf).
        { pose proof Hyfyh as HH. destruct (ub (sy3 s)) eqn:E; try reflexivity; cbn in HH; contradiction. }
        destruct (ub (sx3 t)) as [M| |] eqn:EtH; [ | exact I | ].
        2:{ exfalso. pose proof (mem3_hi (sx3 t) fx Hftx) as HH. rewrite EtH in HH. cbn in HH. exact HH. }
        exfalso.
        destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy0 [Hmy0 [Hby1 Hby2]]].
        set (vy := Z.max vy0 ((M+1) * zlo2)).
        assert (Hmemy : mem3 (sy3 s) vy).
        { split; [eapply leq_zinf_trans; [apply (mem3_lo _ _ Hmy0) | ]; cbn; unfold vy; lia | rewrite Hyp; exact I]. }
        assert (Hbl : leq_zinf (fyminZ (lb (sx3 s)) zlo2) (Fin vy)) by (eapply leq_zinf_trans; [exact Hby1 | ]; cbn; unfold vy; lia).
        assert (Hbu : leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) zlo2)) by (rewrite Hxp; cbn; exact I).
        destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
        pose proof (mem3_hi (sx3 t) _ Hmxt) as HH. rewrite EtH in HH. cbn in HH.
        assert (Hqge : ((M+1) * zlo2) / zlo2 <= vy / zlo2) by (apply Z.div_le_mono; [lia | unfold vy; lia]).
        rewrite Z.div_mul in Hqge by lia. lia.
      + pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
    - eapply leq_zinf_trans; [ apply min_zinf_leq_zinf_l | ].
      assert (Hzlp : forall x, leqb_zinf x Pinf = true) by (intros [?| |]; reflexivity).
      destruct (ub (sx3 s)) as [xu| |] eqn:Exu; [ | rewrite Hzlp in Hclip; discriminate | congruence ].
      assert (Hclipxu : forall vz, leq_zinf (lb z2) (Fin vz) -> leq_zinf (Fin vz) (ub z2) ->
        leq_zinf (Fin (xu + 1)) (fdiv_zinf (ub yF) (Fin vz)) -> leq_zinf (Fin xu) (ub (sx3 t))).
      { intros vz Hvlo Hvhi Hcorner.
        pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
        destruct (fattain_vx_hi (lb (sx3 s)) (Fin xu) vz xu ltac:(pose proof (Hv1 vz Hvlo); lia) Hxle (leq_zinf_refl _)) as (Hbl & Hbu & Hqeq).
        set (vy := (xu + 1) * vz - 1) in *.
        assert (Hvylo : leq_zinf (lb (sy3 s)) (Fin vy)) by (unfold vy; cbn [fymaxZ] in Hb2; exact Hb2).
        assert (Hvyhi : leq_zinf (Fin vy) (ub (sy3 s))).
        { eapply leq_zinf_trans; [ | exact Hyfyh ].
          destruct (ub yF) as [yhv| |] eqn:Eyh.
          - cbn [fdiv_zinf] in Hcorner. cbn in Hcorner. cbn.
            destruct (Z.lt_ge_cases vy yhv) as [H|H]; [lia | exfalso].
            pose proof (Z.div_le_mono yhv vy vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
          - exact I.
          - pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
        destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [_ HH]. rewrite Hqeq in HH. exact HH. }
      assert (Hbfu : forall X a, leqb_zinf X (Fin a) = false -> leq_zinf (Fin (a + 1)) X).
      { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | exact I | discriminate ]. }
      destruct (leqb_zinf (fdiv_zinf (ub yF) (lb z2)) (Fin xu)) eqn:Ehl.
      + destruct (ub z2) as [zh| |] eqn:Eh.
        * apply (Hclipxu zh Hz2ne (leq_zinf_refl _)).
          destruct (leqb_zinf (fdiv_zinf (ub yF) (Fin zh)) (Fin xu)) eqn:Ehh.
          -- exfalso. apply leq_zinf_prop_bool_equiv in Ehl, Ehh.
             assert (Hle : leq_zinf (max_zinf (max_zinf (fdiv_zinf (lb yF) (lb z2)) (fdiv_zinf (lb yF) (Fin zh)))
               (max_zinf (fdiv_zinf (ub yF) (lb z2)) (fdiv_zinf (ub yF) (Fin zh)))) (Fin xu)).
             { apply max_zinf_lub; apply max_zinf_lub.
               - eapply leq_zinf_trans; [ | exact Ehl ]. rewrite Hzlo2. apply fdiv_zinf_mono_pos; [exact Hyfne | lia].
               - eapply leq_zinf_trans; [ | exact Ehh ]. apply fdiv_zinf_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia].
               - exact Ehl.
               - exact Ehh. }
             apply leq_zinf_prop_bool_equiv in Hle. rewrite Hle in Hclip. discriminate.
          -- apply Hbfu. exact Ehh.
        * destruct (leqb_zinf (fdiv_zinf (ub yF) Pinf) (Fin xu)) eqn:Ehh.
          -- exfalso. apply leq_zinf_prop_bool_equiv in Ehl, Ehh.
             assert (Hle : leq_zinf (max_zinf (max_zinf (fdiv_zinf (lb yF) (lb z2)) (fdiv_zinf (lb yF) Pinf))
               (max_zinf (fdiv_zinf (ub yF) (lb z2)) (fdiv_zinf (ub yF) Pinf))) (Fin xu)).
             { apply max_zinf_lub; apply max_zinf_lub.
               - eapply leq_zinf_trans; [ | exact Ehl ]. rewrite Hzlo2. apply fdiv_zinf_mono_pos; [exact Hyfne | lia].
               - eapply leq_zinf_trans; [ | exact Ehh ]. apply fdiv_zinf_mono_num_pinf. exact Hyfne.
               - exact Ehl.
               - exact Ehh. }
             apply leq_zinf_prop_bool_equiv in Hle. rewrite Hle in Hclip. discriminate.
          -- apply Hbfu in Ehh.
             destruct (ub yF) as [yhv| |] eqn:Eyh.
             ++ apply (Hclipxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                cbn [fdiv_zinf] in Ehh |- *.
                assert (Hq0 : yhv / (Z.max zlo2 (Z.abs yhv + 1)) = (if yhv <? 0 then -1 else 0)).
                { destruct (Z.ltb_spec yhv 0) as [Hn|Hp].
                  - assert (HL0 : 0 < Z.max zlo2 (Z.abs yhv + 1)) by lia.
                    assert (yhv / (Z.max zlo2 (Z.abs yhv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                    assert (-1 <= yhv / (Z.max zlo2 (Z.abs yhv + 1))) by (apply Z.div_le_lower_bound; lia).
                    lia.
                  - apply Z.div_small. lia. }
                rewrite Hq0. exact Ehh.
             ++ apply (Hclipxu (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (leq_zinf_Pinf _)).
                cbn [fdiv_zinf]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). exact I.
             ++ pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
        * congruence.
      + apply (Hclipxu zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ehl. apply Hbfu. exact Ehl. }
  apply ile3_intro; cbn [lb ub].
  { destruct (lb yF) as [vlo| |] eqn:Eylo.
    - assert (Hex : exists vzs, leq_zinf (lb z2) (Fin vzs) /\ leq_zinf (Fin vzs) (ub z2) /\
        leq_zinf (fyminZ (lb (sx3 s)) vzs) (Fin vlo) /\ leq_zinf (Fin vlo) (fymaxZ (ub (sx3 s)) vzs)).
      { destruct (lb (sx3 s)) as [a| |] eqn:Exl.
        - destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
          + exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
            pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
            pose proof (fband_ne (Fin a) (ub (sx3 s)) zlo2 Hzlo21 Hxle) as Hbn.
            assert (Hmin_zinf : min_zinf (mul_zinf (Fin a) (lb z2)) (mul_zinf (Fin a) (ub z2)) = Fin (a*zlo2)).
            { rewrite Hzlo2. destruct (ub z2) as [zhi2| |] eqn:Eh; [ | | congruence ].
              - cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.min_l by nia; reflexivity.
              - destruct (Z.eq_dec a 0) as [->|Han].
                + cbn. reflexivity.
                + cbn. rewrite (proj2 (Z.eqb_neq a 0) Han), (proj2 (Z.ltb_lt 0 a) ltac:(lia)). reflexivity. }
            split.
            * rewrite <- Eylo, HyF; cbn [lb]; rewrite Hmin_zinf; cbn [fyminZ]. apply leq_zinf_max_zinf_r.
            * rewrite <- Eylo, HyF; cbn [lb]; rewrite Hmin_zinf.
              apply max_zinf_lub; [exact Hb2 | ]. change (Fin (a*zlo2)) with (fyminZ (Fin a) zlo2). exact Hbn.
          + destruct (ub z2) as [zhi2| |] eqn:Eh.
            * exists zhi2. split; [exact Hz2ne | split; [apply leq_zinf_refl | ]].
              pose proof (Hband zhi2 Hz2ne (leq_zinf_refl _)) as [Hb1 Hb2].
              pose proof (fband_ne (Fin a) (ub (sx3 s)) zhi2 (Hv1 zhi2 Hz2ne) Hxle) as Hbn.
              assert (Hmin_zinf : min_zinf (mul_zinf (Fin a) (lb z2)) (mul_zinf (Fin a) (Fin zhi2)) = Fin (a*zhi2)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.min_r by nia; reflexivity. }
              split.
              -- rewrite <- Eylo, HyF; cbn [lb]; rewrite Hmin_zinf; cbn [fyminZ]. apply leq_zinf_max_zinf_r.
              -- rewrite <- Eylo, HyF; cbn [lb]; rewrite Hmin_zinf.
                 apply max_zinf_lub; [exact Hb2 | ]. change (Fin (a*zhi2)) with (fyminZ (Fin a) zhi2). exact Hbn.
            * assert (Hlbyf : lb yF = lb (sy3 s)).
              { rewrite HyF; cbn [lb]; rewrite Hzlo2; rewrite mul_zinf_fn by lia; cbn; destruct (lb (sy3 s)); reflexivity. }
              assert (Hyleq : lb (sy3 s) = Fin vlo) by (rewrite <- Hlbyf; exact Eylo).
              set (vzs := Z.max zlo2 (Z.max 1 (1 - vlo))).
              assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
              assert (Hgev : 1 - vlo <= vzs) by (unfold vzs; lia).
              assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
              clearbody vzs.
              assert (HB1 : leq_zinf (lb z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
              exists vzs. split; [exact HB1 | split; [apply leq_zinf_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply leq_zinf_Pinf)) as [Hb1 Hb2].
              split.
              -- cbn [fyminZ]. cbn. nia.
              -- rewrite Hyleq in Hb2. exact Hb2.
            * congruence.
        - congruence.
        - exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          assert (Hlbyf : lb yF = lb (sy3 s)).
          { rewrite HyF; cbn [lb]; rewrite Hzlo2; rewrite mul_zinf_ninf_fp by lia; cbn; destruct (lb (sy3 s)); reflexivity. }
          assert (Hyleq : lb (sy3 s) = Fin vlo) by (rewrite <- Hlbyf; exact Eylo).
          split; [ cbn [fyminZ]; exact I | rewrite Hyleq in Hb2; exact Hb2 ]. }
      destruct Hex as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vlo A B Hyfyl Hyflo_hi C D) as [HH _]. exact HH.
    - pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
    - assert (Hlo0 : lb (sy3 s) = Ninf) by (destruct (lb (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyl; contradiction).
      destruct (lb (sy3 t)) as [M| |] eqn:EtL; [ | | exact I ].
      2:{ exfalso. pose proof (mem3_lo (sy3 t) fy Hfty) as HH. rewrite EtL in HH. cbn in HH. exact HH. }
      exfalso.
      assert (HMfy : M <= fy) by (pose proof (mem3_lo (sy3 t) fy Hfty) as HH; rewrite EtL in HH; cbn in HH; exact HH).
      assert (Hfyhi : leq_zinf (Fin fy) (ub (sy3 s))) by (apply (mem3_hi _ _ Hfym)).
      destruct (lb (sx3 s)) as [a| |] eqn:Exl.
      + destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
        * exfalso. rewrite HyF in Eylo; cbn [lb] in Eylo; rewrite Hlo0 in Eylo.
          rewrite Hzlo2 in Eylo. destruct (ub z2) as [zh| |] eqn:Eh.
          -- cbn in Eylo. discriminate.
          -- destruct (Z.eq_dec a 0) as [->|Han]; cbn in Eylo; try discriminate.
             rewrite (proj2 (Z.eqb_neq a 0) Han), (proj2 (Z.ltb_lt 0 a) ltac:(lia)) in Eylo. cbn in Eylo. discriminate.
          -- congruence.
        * destruct (ub z2) as [zh| |] eqn:Eh.
          -- exfalso. rewrite HyF in Eylo; cbn [lb] in Eylo; rewrite Hlo0, Hzlo2 in Eylo; cbn in Eylo; discriminate.
          -- destruct (ub (sy3 s)) as [hh| |] eqn:Ehy.
             ++ set (vzs := Z.max zlo2 (Z.max 1 (Z.max (1-M) (1-hh)))).
                assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
                assert (HgeM : 1 - M <= vzs) by (unfold vzs; lia).
                assert (Ggehh : 1 - hh <= vzs) by (unfold vzs; lia).
                assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
                clearbody vzs.
                assert (HB1 : leq_zinf (lb z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
                assert (Hmemy : mem3 (sy3 s) (a * vzs)).
                { split; [rewrite Hlo0; exact I | rewrite Ehy; cbn; nia]. }
                assert (Hbl : leq_zinf (fyminZ (Fin a) vzs) (Fin (a * vzs))) by (cbn [fyminZ]; cbn; lia).
                assert (Hbu : leq_zinf (Fin (a * vzs)) (fymaxZ (ub (sx3 s)) vzs)).
                { pose proof (fband_ne (Fin a) (ub (sx3 s)) vzs Hz1v Hxle) as Hbn.
                  assert (Efym : fyminZ (Fin a) vzs = Fin (a * vzs)) by reflexivity.
                  rewrite Efym in Hbn. exact Hbn. }
                destruct (Hwit vzs (a * vzs) HB1 (leq_zinf_Pinf _) Hmemy Hbl Hbu) as (_ & Hmyt & _).
                pose proof (mem3_lo (sy3 t) (a * vzs) Hmyt) as HH. rewrite EtL in HH. cbn in HH. nia.
             ++ set (vzs := Z.max zlo2 (Z.max 1 (1-M))).
                assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
                assert (HgeM : 1 - M <= vzs) by (unfold vzs; lia).
                assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
                clearbody vzs.
                assert (HB1 : leq_zinf (lb z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
                assert (Hmemy : mem3 (sy3 s) (a * vzs)).
                { split; [rewrite Hlo0; exact I | rewrite Ehy; exact I]. }
                assert (Hbl : leq_zinf (fyminZ (Fin a) vzs) (Fin (a * vzs))) by (cbn [fyminZ]; cbn; lia).
                assert (Hbu : leq_zinf (Fin (a * vzs)) (fymaxZ (ub (sx3 s)) vzs)).
                { pose proof (fband_ne (Fin a) (ub (sx3 s)) vzs Hz1v Hxle) as Hbn.
                  assert (Efym : fyminZ (Fin a) vzs = Fin (a * vzs)) by reflexivity.
                  rewrite Efym in Hbn. exact Hbn. }
                destruct (Hwit vzs (a * vzs) HB1 (leq_zinf_Pinf _) Hmemy Hbl Hbu) as (_ & Hmyt & _).
                pose proof (mem3_lo (sy3 t) (a * vzs) Hmyt) as HH. rewrite EtL in HH. cbn in HH. nia.
             ++ congruence.
          -- congruence.
      + congruence.
      + destruct (fymaxZ (ub (sx3 s)) zlo2) as [tm| |] eqn:Etm.
        * set (vy := Z.min (M-1) tm).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [rewrite Hlo0; exact I | eapply leq_zinf_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
          assert (Hbl : leq_zinf (fyminZ Ninf zlo2) (Fin vy)) by (cbn [fyminZ]; exact I).
          assert (Hbu : leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) zlo2)) by (rewrite Etm; cbn; unfold vy; lia).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
        * set (vy := M-1).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [rewrite Hlo0; exact I | eapply leq_zinf_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
          assert (Hbl : leq_zinf (fyminZ Ninf zlo2) (Fin vy)) by (cbn [fyminZ]; exact I).
          assert (Hbu : leq_zinf (Fin vy) (fymaxZ (ub (sx3 s)) zlo2)) by (rewrite Etm; apply leq_zinf_Pinf).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
        * exfalso. apply (fymaxZ_not_Ninf (ub (sx3 s)) zlo2 Hxun). exact Etm. }
  { destruct (ub yF) as [vhi| |] eqn:Eyhi.
    - assert (Hexu : exists vzs, leq_zinf (lb z2) (Fin vzs) /\ leq_zinf (Fin vzs) (ub z2) /\
        leq_zinf (fyminZ (lb (sx3 s)) vzs) (Fin vhi) /\ leq_zinf (Fin vhi) (fymaxZ (ub (sx3 s)) vzs)).
      { destruct (ub (sx3 s)) as [xu| |] eqn:Exu.
        - destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
          + destruct (ub z2) as [zhi2| |] eqn:Eh.
            * exists zhi2. split; [exact Hz2ne | split; [apply leq_zinf_refl | ]].
              pose proof (Hband zhi2 Hz2ne (leq_zinf_refl _)) as [Hb1 Hb2].
              pose proof (fband_ne (lb (sx3 s)) (Fin xu) zhi2 (Hv1 zhi2 Hz2ne) Hxle) as Hbn.
              assert (Hmax_zinf : max_zinf (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) (lb z2)) (-1)) (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) (Fin zhi2)) (-1)) = Fin ((xu+1)*zhi2-1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.max_r by nia; nia. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hmax_zinf.
                 apply leq_zinf_min_zinf_glb; [exact Hb1 | ]. change (Fin ((xu+1)*zhi2-1)) with (fymaxZ (Fin xu) zhi2). exact Hbn.
              -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hmax_zinf; cbn [fymaxZ]. apply min_zinf_leq_zinf_r.
            * assert (Hhi0 : ub yF = ub (sy3 s)).
              { rewrite HyF; cbn [ub]; rewrite Hzlo2; cbn [addk_zinf]; rewrite mul_zinf_fp by lia; cbn; destruct (ub (sy3 s)); reflexivity. }
              assert (Hyheq : ub (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
              set (vzs := Z.max zlo2 (Z.max 1 (vhi + 2))).
              assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
              assert (Hvge : vhi + 2 <= vzs) by (unfold vzs; lia).
              assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
              clearbody vzs.
              assert (HB1 : leq_zinf (lb z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
              exists vzs. split; [exact HB1 | split; [apply leq_zinf_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply leq_zinf_Pinf)) as [Hb1 Hb2].
              split.
              -- rewrite <- Hyheq. exact Hb1.
              -- cbn [fymaxZ]. cbn. nia.
            * congruence.
          + destruct (ub z2) as [zhi2| |] eqn:Eh.
            * exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
              pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
              pose proof (fband_ne (lb (sx3 s)) (Fin xu) zlo2 Hzlo21 Hxle) as Hbn.
              assert (Hmax_zinf : max_zinf (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) (lb z2)) (-1)) (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) (Fin zhi2)) (-1)) = Fin ((xu+1)*zlo2-1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.max_l by nia; nia. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hmax_zinf.
                 apply leq_zinf_min_zinf_glb; [exact Hb1 | ]. change (Fin ((xu+1)*zlo2-1)) with (fymaxZ (Fin xu) zlo2). exact Hbn.
              -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hmax_zinf; cbn [fymaxZ]. apply min_zinf_leq_zinf_r.
            * exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
              pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
              pose proof (fband_ne (lb (sx3 s)) (Fin xu) zlo2 Hzlo21 Hxle) as Hbn.
              assert (Hmax_zinf : max_zinf (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) (lb z2)) (-1)) (addk_zinf (mul_zinf (addk_zinf (Fin xu) 1) Pinf) (-1)) = Fin ((xu+1)*zlo2-1)).
              { rewrite Hzlo2. cbn [addk_zinf]. destruct (Z.eq_dec (xu+1) 0) as [Hx1|Hx1].
                - rewrite Hx1. cbn. reflexivity.
                - rewrite mul_zinf_fn by lia. cbn. reflexivity. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hmax_zinf.
                 apply leq_zinf_min_zinf_glb; [exact Hb1 | ]. change (Fin ((xu+1)*zlo2-1)) with (fymaxZ (Fin xu) zlo2). exact Hbn.
              -- rewrite <- Eyhi, HyF; cbn [ub]; rewrite Hmax_zinf; cbn [fymaxZ]. apply min_zinf_leq_zinf_r.
            * congruence.
        - assert (Hhi0 : ub yF = ub (sy3 s)).
          { rewrite HyF; cbn [ub]; rewrite Hzlo2; cbn [addk_zinf]; rewrite mul_zinf_pinf_fp by lia; cbn; destruct (ub (sy3 s)); reflexivity. }
          assert (Hyheq : ub (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
          exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          split.
          -- rewrite <- Hyheq. exact Hb1.
          -- cbn [fymaxZ]. apply leq_zinf_Pinf.
        - congruence. }
      destruct Hexu as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vhi A B Hyfhi_lo Hyfyh C D) as [_ HH]. exact HH.
    - assert (Hhi0 : ub (sy3 s) = Pinf) by (destruct (ub (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyh; contradiction).
      destruct (ub (sy3 t)) as [M| |] eqn:EtH; [ | exact I | ].
      2:{ exfalso. pose proof (mem3_hi (sy3 t) fy Hfty) as HH. rewrite EtH in HH. cbn in HH. exact HH. }
      exfalso.
      assert (HfyM : fy <= M) by (pose proof (mem3_hi (sy3 t) fy Hfty) as HH; rewrite EtH in HH; cbn in HH; exact HH).
      assert (Hfylo : leq_zinf (lb (sy3 s)) (Fin fy)) by (apply (mem3_lo _ _ Hfym)).
      destruct (ub (sx3 s)) as [xu| |] eqn:Exu.
      + destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
        * destruct (ub z2) as [zh| |] eqn:Eh.
          -- exfalso. rewrite HyF in Eyhi; cbn [ub] in Eyhi; rewrite Hhi0, Hzlo2 in Eyhi; cbn in Eyhi; discriminate.
          -- set (vzs := Z.max zlo2 (Z.max 1 (M + 2))).
             assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
             assert (HgeM : M + 2 <= vzs) by (unfold vzs; lia).
             assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
             clearbody vzs.
             assert (HB1 : leq_zinf (lb z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
             assert (Hmemy : mem3 (sy3 s) ((xu+1)*vzs-1)).
             { split; [eapply leq_zinf_trans'; [exact Hfylo | ]; cbn; nia | rewrite Hhi0; exact I]. }
             assert (Hbu : leq_zinf (Fin ((xu+1)*vzs-1)) (fymaxZ (Fin xu) vzs)) by (cbn [fymaxZ]; cbn; lia).
             assert (Hbl : leq_zinf (fyminZ (lb (sx3 s)) vzs) (Fin ((xu+1)*vzs-1))).
             { pose proof (fband_ne (lb (sx3 s)) (Fin xu) vzs Hz1v Hxle) as Hbn.
               assert (Efym : fymaxZ (Fin xu) vzs = Fin ((xu+1)*vzs-1)) by reflexivity.
               rewrite Efym in Hbn. exact Hbn. }
             destruct (Hwit vzs ((xu+1)*vzs-1) HB1 (leq_zinf_Pinf _) Hmemy Hbl Hbu) as (_ & Hmyt & _).
             pose proof (mem3_hi (sy3 t) ((xu+1)*vzs-1) Hmyt) as HH. rewrite EtH in HH. cbn in HH. nia.
          -- congruence.
        * exfalso. rewrite HyF in Eyhi; cbn [ub] in Eyhi; rewrite Hhi0, Hzlo2 in Eyhi.
          destruct (ub z2) as [zh| |] eqn:Eh; cbn [addk_zinf] in Eyhi.
          -- cbn in Eyhi. discriminate.
          -- destruct (Z.eq_dec (xu+1) 0) as [Hx1|Hx1].
             ++ rewrite Hx1 in Eyhi. cbn in Eyhi. discriminate.
             ++ rewrite mul_zinf_fn in Eyhi by lia. cbn in Eyhi. discriminate.
          -- congruence.
      + destruct (fyminZ (lb (sx3 s)) zlo2) as [tmn| |] eqn:Etm.
        * set (vy := Z.max (M+1) tmn).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [eapply leq_zinf_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
          assert (Hbu : leq_zinf (Fin vy) (fymaxZ Pinf zlo2)) by (cbn [fymaxZ]; apply leq_zinf_Pinf).
          assert (Hbl : leq_zinf (fyminZ (lb (sx3 s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; unfold vy; lia).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
        * exfalso. apply (fyminZ_not_Pinf (lb (sx3 s)) zlo2 Hxlp). exact Etm.
        * set (vy := M+1).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [eapply leq_zinf_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
          assert (Hbu : leq_zinf (Fin vy) (fymaxZ Pinf zlo2)) by (cbn [fymaxZ]; apply leq_zinf_Pinf).
          assert (Hbl : leq_zinf (fyminZ (lb (sx3 s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; exact I).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
      + congruence.
    - pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
  apply ile3_intro; cbn [lb ub].
  + destruct (Hpickvy zlo2 Hzlo2lo Hzlo2hi) as [vy [Hmy [Hby1 Hby2]]].
    destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmy Hby1 Hby2) as (_ & _ & Hmzt).
    rewrite Hzlo2. apply (mem3_lo (sz3 t) zlo2 Hmzt).
  + destruct (ub z2) as [zhi2| |] eqn:Ehz2.
    * assert (Hlo : leq_zinf (lb z2) (Fin zhi2)) by exact Hz2ne.
      destruct (Hpickvy zhi2 Hlo (leq_zinf_refl _)) as [vy [Hmy [Hby1 Hby2]]].
      destruct (Hwit zhi2 vy Hlo (leq_zinf_refl _) Hmy Hby1 Hby2) as (_ & _ & Hmzt).
      apply (mem3_hi (sz3 t) zhi2 Hmzt).
    * destruct (ub (sz3 t)) as [M| |] eqn:Eht.
      -- exfalso.
         assert (Hvzlo : leq_zinf (lb z2) (Fin (Z.max zlo2 (M+1)))) by (rewrite Hzlo2; cbn; lia).
         assert (Hvzhi : leq_zinf (Fin (Z.max zlo2 (M+1))) Pinf) by apply leq_zinf_Pinf.
         destruct (Hpickvy (Z.max zlo2 (M+1)) Hvzlo Hvzhi) as [vy [Hmy [Hby1 Hby2]]].
         destruct (Hwit (Z.max zlo2 (M+1)) vy Hvzlo Hvzhi Hmy Hby1 Hby2) as (_ & _ & Hmzt).
         pose proof (mem3_hi (sz3 t) _ Hmzt) as HH. rewrite Eht in HH. cbn in HH. lia.
      -- apply leq_zinf_Pinf.
      -- exfalso. pose proof (mem3_hi (sz3 t) fz Hftz) as HH. rewrite Eht in HH. cbn in HH. exact HH.
    * congruence.
Qed.


Lemma zfdiv4_best_feasible : forall s,
  feasible3 is_fdiv_asn s -> forall t, contains3 is_fdiv_asn s t -> sle3 (zfdiv4 s) t.
Proof.
  intros s Hf t Hct.
  destruct Hf as (fx & fy & fz & Hfin & Hfsol).
  assert (Es : ne_store3 s = true) by (eapply ne_store3_true; exact Hfin).
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  assert (HneOut : ne_store3 (zfdiv4 s) = true)
    by (eapply ne_store3_true; apply zfdiv4_soundness; [exact Hfin | exact Hfsol]).
  unfold zfdiv4 in *. rewrite Es in *. cbn [negb] in *.
  apply join4_sle_cases; [ | | exact HneOut ].
  - intro Ep. apply fpos_best.
    + apply (fpos_ne_feasible s Esx Esy Ep).
    + intros vx vy vz Hin Hsol Hvz. apply Hct; assumption.
  - intro En.
    rewrite <- (mir_yz_invol t).
    apply (proj2 (sle3_mir_yz (zfdiv_pos3 (mir_yz s)) (mir_yz t))).
    apply fpos_best.
    + rewrite ne_mir_yz in En.
      assert (Esx' : nonempty3b (sx3 (mir_yz s)) = true) by (unfold mir_yz; cbn [sx3]; exact Esx).
      assert (Esy' : nonempty3b (sy3 (mir_yz s)) = true)
        by (unfold mir_yz; cbn [sy3]; rewrite nonempty3b_mirror; exact Esy).
      apply (fpos_ne_feasible (mir_yz s) Esx' Esy' En).
    + intros vx vy vz Hin Hsol Hvz.
      pose proof (in_mir_yz_inv s vx vy vz Hin) as Hins.
      pose proof (sol_mir vx vy vz Hsol) as Hsols.
      pose proof (Hct vx (- vy) (- vz) Hins Hsols) as Hint.
      pose proof (in_mir_yz t vx (- vy) (- vz) Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
Qed.

(* ---- mir_xy plumbing + ceiling/floor solution correspondence ---- *)
Lemma mir_xy_invol : forall s, mir_xy (mir_xy s) = s.
Proof.
  intros [ix iy iz]. unfold mir_xy; cbn [sx3 sy3 sz3].
  rewrite !mirror_i_invol. reflexivity.
Qed.

Lemma ne_mir_xy : forall s, ne_store3 (mir_xy s) = ne_store3 s.
Proof.
  intros s. unfold ne_store3, mir_xy; cbn [sx3 sy3 sz3].
  rewrite !nonempty3b_mirror. reflexivity.
Qed.

Lemma sle3_mir_xy : forall a b, sle3 (mir_xy a) (mir_xy b) <-> sle3 a b.
Proof.
  intros a b. unfold sle3. rewrite (ne_mir_xy a).
  unfold mir_xy; cbn [sx3 sy3 sz3]. rewrite !ile3_mirror. tauto.
Qed.

Lemma in_mir_xy_inv : forall s vx vy vz,
  in_store3 (mir_xy s) vx vy vz -> in_store3 s (- vx) (- vy) vz.
Proof.
  intros s vx vy vz H. pose proof (in_mir_xy (mir_xy s) vx vy vz H) as H2.
  rewrite mir_xy_invol in H2. exact H2.
Qed.

Lemma csol_of_sol_xy : forall vx vy vz, is_fdiv_asn vx vy vz -> csol (- vx) (- vy) vz.
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  unfold cdiv. rewrite Z.opp_involutive. lia.
Qed.

Lemma csol_of_sol_xz : forall vx vy vz, is_fdiv_asn vx vy vz -> csol (- vx) vy (- vz).
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  unfold cdiv. rewrite Z.div_opp_opp by lia. lia.
Qed.

Lemma zcdiv4_best_feasible : forall s,
  feasible3 csol s -> forall t, contains3 csol s t -> sle3 (zcdiv4 s) t.
Proof.
  intros s Hf t Hct.
  destruct Hf as (fx & fy & fz & Hfin & Hfcs).
  assert (Es : ne_store3 s = true) by (eapply ne_store3_true; exact Hfin).
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  assert (HneOut : ne_store3 (zcdiv4 s) = true)
    by (eapply ne_store3_true; apply zcdiv4_soundness; [exact Hfin | exact Hfcs]).
  unfold zcdiv4 in *. rewrite Es in *. cbn [negb] in *.
  apply join4_sle_cases; [ | | exact HneOut ].
  - intro Ep. rewrite ne_mir_xy in Ep.
    rewrite <- (mir_xy_invol t).
    apply (proj2 (sle3_mir_xy (zfdiv_pos3 (mir_xy s)) (mir_xy t))).
    apply fpos_best.
    + assert (Esx' : nonempty3b (sx3 (mir_xy s)) = true)
        by (unfold mir_xy; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
      assert (Esy' : nonempty3b (sy3 (mir_xy s)) = true)
        by (unfold mir_xy; cbn [sy3]; rewrite nonempty3b_mirror; exact Esy).
      apply (fpos_ne_feasible (mir_xy s) Esx' Esy' Ep).
    + intros vx vy vz Hin Hsol Hvz.
      pose proof (in_mir_xy_inv s vx vy vz Hin) as Hins.
      pose proof (csol_of_sol_xy vx vy vz Hsol) as Hcs.
      pose proof (Hct (- vx) (- vy) vz Hins Hcs) as Hint.
      pose proof (in_mir_xy t (- vx) (- vy) vz Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
  - intro En. rewrite ne_mir_xz in En.
    rewrite <- (mir_xz_invol t).
    apply (proj2 (sle3_mir_xz (zfdiv_pos3 (mir_xz s)) (mir_xz t))).
    apply fpos_best.
    + assert (Esx' : nonempty3b (sx3 (mir_xz s)) = true)
        by (unfold mir_xz; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
      assert (Esy' : nonempty3b (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
      apply (fpos_ne_feasible (mir_xz s) Esx' Esy' En).
    + intros vx vy vz Hin Hsol Hvz.
      pose proof (in_mir_xz_inv s vx vy vz Hin) as Hins.
      pose proof (csol_of_sol_xz vx vy vz Hsol) as Hcs.
      pose proof (Hct (- vx) vy (- vz) Hins Hcs) as Hint.
      pose proof (in_mir_xz t (- vx) vy (- vz) Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
Qed.

(* ---- euclidean/floor solution correspondence ---- *)
Lemma esol_of_sol_pos : forall vx vy vz, is_fdiv_asn vx vy vz -> 0 < vz -> esol vx vy vz.
Proof.
  intros vx vy vz [Hnz Hq] Hpos. split; [lia | ].
  rewrite (proj2 (Z.ltb_lt 0 vz) Hpos). exact Hq.
Qed.

Lemma esol_of_sol_xz_neg : forall vx vy vz, is_fdiv_asn vx vy vz -> 0 < vz -> esol (- vx) vy (- vz).
Proof.
  intros vx vy vz Hsol Hpos. destruct (csol_of_sol_xz vx vy vz Hsol) as [Hnz Hq].
  split; [lia | ]. rewrite (proj2 (Z.ltb_ge 0 (- vz)) ltac:(lia)). exact Hq.
Qed.

Lemma zediv4_best_feasible : forall s,
  feasible3 esol s -> forall t, contains3 esol s t -> sle3 (zediv4 s) t.
Proof.
  intros s Hf t Hct.
  destruct Hf as (fx & fy & fz & Hfin & Hfes).
  assert (Es : ne_store3 s = true) by (eapply ne_store3_true; exact Hfin).
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  assert (HneOut : ne_store3 (zediv4 s) = true)
    by (eapply ne_store3_true; apply zediv4_soundness; [exact Hfin | exact Hfes]).
  unfold zediv4 in *. rewrite Es in *. cbn [negb] in *.
  apply join4_sle_cases; [ | | exact HneOut ].
  - intro Ep. apply fpos_best.
    + apply (fpos_ne_feasible s Esx Esy Ep).
    + intros vx vy vz Hin Hsol Hvz.
      apply Hct; [exact Hin | apply esol_of_sol_pos; [exact Hsol | lia]].
  - intro En. rewrite ne_mir_xz in En.
    rewrite <- (mir_xz_invol t).
    apply (proj2 (sle3_mir_xz (zfdiv_pos3 (mir_xz s)) (mir_xz t))).
    apply fpos_best.
    + assert (Esx' : nonempty3b (sx3 (mir_xz s)) = true)
        by (unfold mir_xz; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
      assert (Esy' : nonempty3b (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
      apply (fpos_ne_feasible (mir_xz s) Esx' Esy' En).
    + intros vx vy vz Hin Hsol Hvz.
      pose proof (in_mir_xz_inv s vx vy vz Hin) as Hins.
      pose proof (esol_of_sol_xz_neg vx vy vz Hsol ltac:(lia)) as Hes.
      pose proof (Hct (- vx) vy (- vz) Hins Hes) as Hint.
      pose proof (in_mir_xz t (- vx) vy (- vz) Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
Qed.

(* completeness on infeasible inputs: a non-empty output implies a solution
   (contrapositive: no solution in s => the output is empty = bottom) *)

Theorem zfdiv4_ne_feasible : forall s,
  ne_store3 (zfdiv4 s) = true -> feasible3 is_fdiv_asn s.
Proof.
  intros s Hne. unfold zfdiv4 in Hne.
  destruct (ne_store3 s) eqn:Es; [ | cbn in Hne; congruence ].
  cbn [negb] in Hne.
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  unfold join4 in Hne.
  destruct (ne_store3 (zfdiv_pos3 s)) eqn:Ep; cbn [negb] in Hne.
  - destruct (fpos_ne_feasible s Esx Esy Ep) as (vx & vy & vz & Hin & Hsol & Hvz).
    exists vx, vy, vz. split; assumption.
  - rewrite ne_mir_yz in Hne.
    assert (Esx' : nonempty3b (sx3 (mir_yz s)) = true) by (unfold mir_yz; cbn [sx3]; exact Esx).
    assert (Esy' : nonempty3b (sy3 (mir_yz s)) = true)
      by (unfold mir_yz; cbn [sy3]; rewrite nonempty3b_mirror; exact Esy).
    destruct (fpos_ne_feasible (mir_yz s) Esx' Esy' Hne) as (vx & vy & vz & Hin & Hsol & Hvz).
    exists vx, (- vy), (- vz).
    split; [ apply in_mir_yz_inv; exact Hin | apply sol_mir; exact Hsol ].
Qed.

Theorem zcdiv4_ne_feasible : forall s,
  ne_store3 (zcdiv4 s) = true -> feasible3 csol s.
Proof.
  intros s Hne. unfold zcdiv4 in Hne.
  destruct (ne_store3 s) eqn:Es; [ | cbn in Hne; congruence ].
  cbn [negb] in Hne.
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  unfold join4 in Hne.
  destruct (ne_store3 (mir_xy (zfdiv_pos3 (mir_xy s)))) eqn:Ep; cbn [negb] in Hne.
  - rewrite ne_mir_xy in Ep.
    assert (Esx' : nonempty3b (sx3 (mir_xy s)) = true)
      by (unfold mir_xy; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
    assert (Esy' : nonempty3b (sy3 (mir_xy s)) = true)
      by (unfold mir_xy; cbn [sy3]; rewrite nonempty3b_mirror; exact Esy).
    destruct (fpos_ne_feasible (mir_xy s) Esx' Esy' Ep) as (vx & vy & vz & Hin & Hsol & Hvz).
    exists (- vx), (- vy), vz.
    split; [ apply in_mir_xy_inv; exact Hin | apply csol_of_sol_xy; exact Hsol ].
  - rewrite ne_mir_xz in Hne.
    assert (Esx' : nonempty3b (sx3 (mir_xz s)) = true)
      by (unfold mir_xz; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
    assert (Esy' : nonempty3b (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
    destruct (fpos_ne_feasible (mir_xz s) Esx' Esy' Hne) as (vx & vy & vz & Hin & Hsol & Hvz).
    exists (- vx), vy, (- vz).
    split; [ apply in_mir_xz_inv; exact Hin | apply csol_of_sol_xz; exact Hsol ].
Qed.

Theorem zediv4_ne_feasible : forall s,
  ne_store3 (zediv4 s) = true -> feasible3 esol s.
Proof.
  intros s Hne. unfold zediv4 in Hne.
  destruct (ne_store3 s) eqn:Es; [ | cbn in Hne; congruence ].
  cbn [negb] in Hne.
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  unfold join4 in Hne.
  destruct (ne_store3 (zfdiv_pos3 s)) eqn:Ep; cbn [negb] in Hne.
  - destruct (fpos_ne_feasible s Esx Esy Ep) as (vx & vy & vz & Hin & Hsol & Hvz).
    exists vx, vy, vz. split; [exact Hin | apply esol_of_sol_pos; [exact Hsol | lia]].
  - rewrite ne_mir_xz in Hne.
    assert (Esx' : nonempty3b (sx3 (mir_xz s)) = true)
      by (unfold mir_xz; cbn [sx3]; rewrite nonempty3b_mirror; exact Esx).
    assert (Esy' : nonempty3b (sy3 (mir_xz s)) = true) by (unfold mir_xz; cbn [sy3]; exact Esy).
    destruct (fpos_ne_feasible (mir_xz s) Esx' Esy' Hne) as (vx & vy & vz & Hin & Hsol & Hvz).
    exists (- vx), vy, (- vz).
    split; [ apply in_mir_xz_inv; exact Hin | apply esol_of_sol_xz_neg; [exact Hsol | lia] ].
Qed.

(* ---- best abstract transformer, UNCONDITIONAL (no feasibility hypothesis):
        under the quotient order an empty output is bottom (below every [t]);
        a non-empty one is feasible (via ne-feasibility), so [_best_feasible]
        applies. *)
Theorem zfdiv4_complete : forall s t, contains3 is_fdiv_asn s t -> sle3 (zfdiv4 s) t.
Proof.
  intros s t Hct. destruct (ne_store3 (zfdiv4 s)) eqn:E;
    [ exact (zfdiv4_best_feasible s (zfdiv4_ne_feasible s E) t Hct) | apply sle3_bot; exact E ].
Qed.
Theorem zcdiv4_complete : forall s t, contains3 csol s t -> sle3 (zcdiv4 s) t.
Proof.
  intros s t Hct. destruct (ne_store3 (zcdiv4 s)) eqn:E;
    [ exact (zcdiv4_best_feasible s (zcdiv4_ne_feasible s E) t Hct) | apply sle3_bot; exact E ].
Qed.
Theorem zediv4_complete : forall s t, contains3 esol s t -> sle3 (zediv4 s) t.
Proof.
  intros s t Hct. destruct (ne_store3 (zediv4 s)) eqn:E;
    [ exact (zediv4_best_feasible s (zediv4_ne_feasible s E) t Hct) | apply sle3_bot; exact E ].
Qed.

(* ================================================================== *)
(** ** Closure-operator properties of the four propagators             *)
(*                                                                     *)
(*  A generic derivation ([closure_laws], itv): any propagator that is *)
(*  SOUND, a best abstract transformer, and ne-feasible is an           *)
(*  UNCONDITIONAL lower closure operator over the quotient order --      *)
(*  reductive, monotone, and idempotent up to the bottom equivalence ~. *)
(*  Instantiated for truncated/floor/ceiling/euclidean.                 *)
(* ================================================================== *)

(* Under the QUOTIENT order, soundness + best-transformer + ne-feasibility
   make each propagator an UNCONDITIONAL lower closure operator, via the
   generic [closure_laws] of itv: reductive, monotone, and idempotent up
   to the bottom equivalence ~ (mutual [sle3]).  No feasibility guard. *)

(* Truncated *)
Theorem zfdiv4_reductive : forall s, sle3 (zfdiv4 s) s.
Proof. exact (proj1 (closure_laws is_fdiv_asn zfdiv4 zfdiv4_soundness (fun s _ => zfdiv4_complete s) zfdiv4_ne_feasible)). Qed.
Theorem zfdiv4_monotone : forall s t, sle3 s t -> sle3 (zfdiv4 s) (zfdiv4 t).
Proof. exact (proj1 (proj2 (closure_laws is_fdiv_asn zfdiv4 zfdiv4_soundness (fun s _ => zfdiv4_complete s) zfdiv4_ne_feasible))). Qed.
Theorem zfdiv4_idempotent : forall s,
  sle3 (zfdiv4 (zfdiv4 s)) (zfdiv4 s) /\ sle3 (zfdiv4 s) (zfdiv4 (zfdiv4 s)).
Proof. exact (proj2 (proj2 (closure_laws is_fdiv_asn zfdiv4 zfdiv4_soundness (fun s _ => zfdiv4_complete s) zfdiv4_ne_feasible))). Qed.

(* Ceiling *)
Theorem zcdiv4_reductive : forall s, sle3 (zcdiv4 s) s.
Proof. exact (proj1 (closure_laws csol zcdiv4 zcdiv4_soundness (fun s _ => zcdiv4_complete s) zcdiv4_ne_feasible)). Qed.
Theorem zcdiv4_monotone : forall s t, sle3 s t -> sle3 (zcdiv4 s) (zcdiv4 t).
Proof. exact (proj1 (proj2 (closure_laws csol zcdiv4 zcdiv4_soundness (fun s _ => zcdiv4_complete s) zcdiv4_ne_feasible))). Qed.
Theorem zcdiv4_idempotent : forall s,
  sle3 (zcdiv4 (zcdiv4 s)) (zcdiv4 s) /\ sle3 (zcdiv4 s) (zcdiv4 (zcdiv4 s)).
Proof. exact (proj2 (proj2 (closure_laws csol zcdiv4 zcdiv4_soundness (fun s _ => zcdiv4_complete s) zcdiv4_ne_feasible))). Qed.

(* Euclidean *)
Theorem zediv4_reductive : forall s, sle3 (zediv4 s) s.
Proof. exact (proj1 (closure_laws esol zediv4 zediv4_soundness (fun s _ => zediv4_complete s) zediv4_ne_feasible)). Qed.
Theorem zediv4_monotone : forall s t, sle3 s t -> sle3 (zediv4 s) (zediv4 t).
Proof. exact (proj1 (proj2 (closure_laws esol zediv4 zediv4_soundness (fun s _ => zediv4_complete s) zediv4_ne_feasible))). Qed.
Theorem zediv4_idempotent : forall s,
  sle3 (zediv4 (zediv4 s)) (zediv4 s) /\ sle3 (zediv4 s) (zediv4 (zediv4 s)).
Proof. exact (proj2 (proj2 (closure_laws esol zediv4 zediv4_soundness (fun s _ => zediv4_complete s) zediv4_ne_feasible))). Qed.

(* ================================================================== *)
(** ** Truncated-integer division via the FLOOR solver + disjunction
       composition (moved here from the former tdiv.v).

    Built from the floor positive-slice solver [zfdiv_pos3] and a four-way
    sign-quadrant decomposition (y-sign x z-sign); soundness/completeness
    compose over the disjunction (Prop 4).  The OLD direct tymin/tymax proof
    of the same operation lives in old_tdiv.v ([ztdiv4]). *)
(* ================================================================== *)

Definition tsol (x y z : Z) : Prop := z <> 0 /\ x = Z.quot y z.

Definition pos_y (s : store3) : store3 :=
  St3 (sx3 s) (inter3 (sy3 s) (Itv (Fin 0) Pinf)) (sz3 s).
Definition neg_y (s : store3) : store3 :=
  St3 (sx3 s) (inter3 (sy3 s) (Itv Ninf (Fin 0))) (sz3 s).

Definition ztdivq (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (zfdiv_pos3 (pos_y s))
       (join4 (mir_xz (zfdiv_pos3 (mir_xz (pos_y s))))
       (join4 (mir_xy (zfdiv_pos3 (mir_xy (neg_y s))))
              (mir_yz (zfdiv_pos3 (mir_yz (neg_y s)))))).

(* ================================================================== *)
(** ** (0) quotient/division arithmetic bridges                        *)
(* ================================================================== *)

Lemma quot_eq_div : forall b c, 0 <= b -> 0 < c -> Z.quot b c = Z.div b c.
Proof. intros; apply Z.quot_div_nonneg; lia. Qed.

(* tsol at a point => is_fdiv_asn on the (mirrored) positive slice. *)
Lemma tsol_q1 : forall x y z, tsol x y z -> 0 <= y -> 0 < z -> is_fdiv_asn x y z.
Proof. intros x y z [Hnz Hq] Hy Hz. split; [exact Hnz | rewrite Hq; apply quot_eq_div; lia]. Qed.

Lemma tsol_q2 : forall x y z, tsol x y z -> 0 <= y -> z < 0 -> is_fdiv_asn (- x) y (- z).
Proof.
  intros x y z [Hnz Hq] Hy Hz. split; [lia | ].
  rewrite <- (quot_eq_div y (- z)) by lia.
  rewrite Z.quot_opp_r by lia. rewrite <- Hq. reflexivity.
Qed.

Lemma tsol_q3 : forall x y z, tsol x y z -> y <= 0 -> 0 < z -> is_fdiv_asn (- x) (- y) z.
Proof.
  intros x y z [Hnz Hq] Hy Hz. split; [lia | ].
  rewrite <- (quot_eq_div (- y) z) by lia.
  rewrite Z.quot_opp_l by lia. rewrite <- Hq. reflexivity.
Qed.

Lemma tsol_q4 : forall x y z, tsol x y z -> y <= 0 -> z < 0 -> is_fdiv_asn x (- y) (- z).
Proof.
  intros x y z [Hnz Hq] Hy Hz. split; [lia | ].
  rewrite <- (quot_eq_div (- y) (- z)) by lia.
  rewrite Z.quot_opp_l by lia. rewrite Z.quot_opp_r by lia.
  rewrite <- Hq. lia.
Qed.

(* is_fdiv_asn on the (mirrored) positive slice => tsol at the original point. *)
Lemma sol_q1 : forall a b c, is_fdiv_asn a b c -> 0 <= b -> 1 <= c -> tsol a b c.
Proof. intros a b c [Hnz Hd] Hb Hc. split; [lia | rewrite Hd; symmetry; apply quot_eq_div; lia]. Qed.

Lemma sol_q2 : forall a b c, is_fdiv_asn a b c -> 0 <= b -> 1 <= c -> tsol (- a) b (- c).
Proof.
  intros a b c [Hnz Hd] Hb Hc. split; [lia | ].
  rewrite Z.quot_opp_r by lia. rewrite (quot_eq_div b c) by lia.
  rewrite <- Hd. reflexivity.
Qed.

Lemma sol_q3 : forall a b c, is_fdiv_asn a b c -> 0 <= b -> 1 <= c -> tsol (- a) (- b) c.
Proof.
  intros a b c [Hnz Hd] Hb Hc. split; [lia | ].
  rewrite Z.quot_opp_l by lia. rewrite (quot_eq_div b c) by lia.
  rewrite <- Hd. reflexivity.
Qed.

Lemma sol_q4 : forall a b c, is_fdiv_asn a b c -> 0 <= b -> 1 <= c -> tsol a (- b) (- c).
Proof.
  intros a b c [Hnz Hd] Hb Hc. split; [lia | ].
  rewrite Z.quot_opp_l by lia. rewrite Z.quot_opp_r by lia.
  rewrite (quot_eq_div b c) by lia. rewrite <- Hd. lia.
Qed.

(* ================================================================== *)
(** ** (A) membership helpers for the y-slices                         *)
(* ================================================================== *)

Lemma mem3_pos_y : forall s vx vy vz,
  in_store3 s vx vy vz -> 0 <= vy -> in_store3 (pos_y s) vx vy vz.
Proof.
  intros s vx vy vz (Hmx & Hmy & Hmz) Hy.
  destruct Hmy as [Hyl Hyu].
  unfold pos_y, in_store3, inter3, mem3; cbn [sx3 sy3 sz3 lb ub].
  split; [exact Hmx | split; [ | exact Hmz]].
  split.
  - apply max_zinf_lub; [exact Hyl | cbn; lia].
  - apply leq_zinf_min_zinf_glb; [exact Hyu | apply leq_zinf_Pinf].
Qed.

Lemma mem3_pos_y_inv : forall s vx vy vz,
  in_store3 (pos_y s) vx vy vz -> in_store3 s vx vy vz /\ 0 <= vy.
Proof.
  intros s vx vy vz (Hmx & Hmy & Hmz).
  unfold pos_y, inter3, mem3 in *; cbn [sx3 sy3 sz3 lb ub] in *.
  destruct Hmy as [Hyl Hyu].
  split.
  - unfold in_store3, mem3. split; [exact Hmx | split; [ | exact Hmz]].
    split.
    + eapply leq_zinf_trans; [apply leq_zinf_max_zinf_l | exact Hyl].
    + eapply leq_zinf_trans; [exact Hyu | apply min_zinf_leq_zinf_l].
  - assert (Hz0 : leq_zinf (Fin 0) (Fin vy)) by (eapply leq_zinf_trans; [apply leq_zinf_max_zinf_r | exact Hyl]).
    cbn in Hz0; exact Hz0.
Qed.

Lemma mem3_neg_y : forall s vx vy vz,
  in_store3 s vx vy vz -> vy <= 0 -> in_store3 (neg_y s) vx vy vz.
Proof.
  intros s vx vy vz (Hmx & Hmy & Hmz) Hy.
  destruct Hmy as [Hyl Hyu].
  unfold neg_y, in_store3, inter3, mem3; cbn [sx3 sy3 sz3 lb ub].
  split; [exact Hmx | split; [ | exact Hmz]].
  split.
  - apply max_zinf_lub; [exact Hyl | exact I].
  - apply leq_zinf_min_zinf_glb; [exact Hyu | cbn; lia].
Qed.

Lemma mem3_neg_y_inv : forall s vx vy vz,
  in_store3 (neg_y s) vx vy vz -> in_store3 s vx vy vz /\ vy <= 0.
Proof.
  intros s vx vy vz (Hmx & Hmy & Hmz).
  unfold neg_y, inter3, mem3 in *; cbn [sx3 sy3 sz3 lb ub] in *.
  destruct Hmy as [Hyl Hyu].
  split.
  - unfold in_store3, mem3. split; [exact Hmx | split; [ | exact Hmz]].
    split.
    + eapply leq_zinf_trans; [apply leq_zinf_max_zinf_l | exact Hyl].
    + eapply leq_zinf_trans; [exact Hyu | apply min_zinf_leq_zinf_l].
  - assert (Hz0 : leq_zinf (Fin vy) (Fin 0)) by (eapply leq_zinf_trans; [exact Hyu | apply min_zinf_leq_zinf_r]).
    cbn in Hz0; exact Hz0.
Qed.

(* ================================================================== *)
(** ** (B) [zfdiv_pos3] output non-emptiness reflects to its input      *)
(* ================================================================== *)

Lemma nonempty_sub : forall i j,
  leq_zinf (lb j) (lb i) -> leq_zinf (ub i) (ub j) -> nonempty3b i = true -> nonempty3b j = true.
Proof.
  intros [li ui] [lj uj]; cbn [lb ub]. unfold nonempty3b; cbn [lb ub].
  destruct li as [a1| |], ui as [b1| |], lj as [a2| |], uj as [b2| |];
    intros Hlo Hhi H; cbn in *;
    try congruence; try contradiction; try reflexivity;
    try (apply Z.leb_le in H; apply Z.leb_le; lia); try lia.
Qed.

Lemma zfp_sx_sub : forall s,
  leq_zinf (lb (sx3 s)) (lb (sx3 (zfdiv_pos3 s)))
  /\ leq_zinf (ub (sx3 (zfdiv_pos3 s))) (ub (sx3 s)).
Proof.
  intros s. unfold zfdiv_pos3; cbv zeta.
  destruct (negb (nonempty3b _)); [ cbn [sx3 lb ub]; split; apply leq_zinf_refl | ].
  destruct (negb (nonempty3b _)); [ cbn [sx3 lb ub]; split; apply leq_zinf_refl | ].
  destruct (negb (nonempty3b _)); [ cbn [sx3 lb ub]; split; apply leq_zinf_refl | ].
  cbn [sx3 lb ub]. split; [apply leq_zinf_max_zinf_l | apply min_zinf_leq_zinf_l].
Qed.

Lemma zfp_sy_sub : forall s,
  leq_zinf (lb (sy3 s)) (lb (sy3 (zfdiv_pos3 s)))
  /\ leq_zinf (ub (sy3 (zfdiv_pos3 s))) (ub (sy3 s)).
Proof.
  intros s. unfold zfdiv_pos3; cbv zeta.
  destruct (negb (nonempty3b _)); [ cbn [sy3 lb ub]; split; apply leq_zinf_refl | ].
  destruct (negb (nonempty3b _)); [ cbn [sy3 lb ub]; split; apply leq_zinf_refl | ].
  destruct (negb (nonempty3b _)); cbn [sy3 lb ub]; split;
    solve [ apply leq_zinf_refl | apply leq_zinf_max_zinf_l | apply min_zinf_leq_zinf_l ].
Qed.

Lemma zfdiv_pos3_ne_input : forall s,
  ne_store3 (zfdiv_pos3 s) = true ->
  nonempty3b (sx3 s) = true /\ nonempty3b (sy3 s) = true.
Proof.
  intros s Hne. destruct (ne_store3_parts _ Hne) as (Hx & Hy & _).
  destruct (zfp_sx_sub s) as [Hxl Hxh]. destruct (zfp_sy_sub s) as [Hyl Hyh].
  split.
  - apply (nonempty_sub (sx3 (zfdiv_pos3 s)) (sx3 s) Hxl Hxh Hx).
  - apply (nonempty_sub (sy3 (zfdiv_pos3 s)) (sy3 s) Hyl Hyh Hy).
Qed.

(* ================================================================== *)
(** ** (C) Soundness                                                   *)
(* ================================================================== *)

Theorem ztdivq_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> tsol vx vy vz -> in_store3 (ztdivq s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hts.
  assert (Hne : ne_store3 s = true) by (eapply ne_store3_true; exact Hin).
  unfold ztdivq. rewrite Hne. cbn [negb].
  destruct (Z_le_gt_dec 0 vy) as [Hyp|Hyn];
    destruct (Z.lt_total vz 0) as [Hzn|[Hz0|Hzp]].
  - (* 0<=vy, vz<0 : Q2 *)
    apply in_join4_r. apply in_join4_l.
    replace vx with (- - vx) by lia. replace vz with (- - vz) by lia.
    apply in_mir_xz. apply fpos_sound.
    + apply in_mir_xz. apply mem3_pos_y; [exact Hin | lia].
    + apply tsol_q2; [exact Hts | lia | lia].
    + lia.
  - exfalso. apply (proj1 Hts); exact Hz0.
  - (* 0<=vy, 0<vz : Q1 *)
    apply in_join4_l. apply fpos_sound.
    + apply mem3_pos_y; [exact Hin | lia].
    + apply tsol_q1; [exact Hts | lia | lia].
    + lia.
  - (* vy<0, vz<0 : Q4 *)
    apply in_join4_r. apply in_join4_r. apply in_join4_r.
    replace vy with (- - vy) by lia. replace vz with (- - vz) by lia.
    apply in_mir_yz. apply fpos_sound.
    + apply in_mir_yz. apply mem3_neg_y; [exact Hin | lia].
    + apply tsol_q4; [exact Hts | lia | lia].
    + lia.
  - exfalso. apply (proj1 Hts); exact Hz0.
  - (* vy<0, 0<vz : Q3 *)
    apply in_join4_r. apply in_join4_r. apply in_join4_l.
    replace vx with (- - vx) by lia. replace vy with (- - vy) by lia.
    apply in_mir_xy. apply fpos_sound.
    + apply in_mir_xy. apply mem3_neg_y; [exact Hin | lia].
    + apply tsol_q3; [exact Hts | lia | lia].
    + lia.
Qed.

(* ================================================================== *)
(** ** (D) 4-way join lub combinator                                   *)
(* ================================================================== *)

Lemma join4_4_sle : forall a b c d t,
  (ne_store3 a = true -> sle3 a t) -> (ne_store3 b = true -> sle3 b t) ->
  (ne_store3 c = true -> sle3 c t) -> (ne_store3 d = true -> sle3 d t) ->
  ne_store3 (join4 a (join4 b (join4 c d))) = true ->
  sle3 (join4 a (join4 b (join4 c d))) t.
Proof.
  intros a b c d t Ha Hb Hc Hd Hne.
  apply join4_sle_cases; [exact Ha | | exact Hne].
  intro H1. apply join4_sle_cases; [exact Hb | | exact H1].
  intro H2. apply join4_sle_cases; [exact Hc | exact Hd | exact H2].
Qed.

(* ================================================================== *)
(** ** (E) Best abstract transformer on feasible inputs                *)
(* ================================================================== *)

Theorem ztdivq_best_feasible : forall s,
  feasible3 tsol s -> forall t, contains3 tsol s t -> sle3 (ztdivq s) t.
Proof.
  intros s Hf t Hct.
  destruct Hf as (fx & fy & fz & Hfin & Hfts).
  assert (Es : ne_store3 s = true) by (eapply ne_store3_true; exact Hfin).
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  assert (HneOut : ne_store3 (ztdivq s) = true)
    by (eapply ne_store3_true; apply ztdivq_soundness; [exact Hfin | exact Hfts]).
  unfold ztdivq in *. rewrite Es in *. cbn [negb] in *.
  apply join4_4_sle; [ | | | | exact HneOut ].
  - (* Q1 *)
    intro HneQ. destruct (zfdiv_pos3_ne_input _ HneQ) as [Hsx Hsy].
    apply fpos_best.
    + apply (fpos_ne_feasible (pos_y s) Hsx Hsy HneQ).
    + intros a0 b0 c0 Hinp Hsol Hc1.
      destruct (mem3_pos_y_inv _ _ _ _ Hinp) as [Hins Hb].
      apply Hct; [exact Hins | apply sol_q1; [exact Hsol | exact Hb | exact Hc1]].
  - (* Q2 *)
    intro HneQ. rewrite <- (mir_xz_invol t).
    apply (proj2 (sle3_mir_xz (zfdiv_pos3 (mir_xz (pos_y s))) (mir_xz t))).
    rewrite ne_mir_xz in HneQ.
    destruct (zfdiv_pos3_ne_input _ HneQ) as [Hsx Hsy].
    apply fpos_best.
    + apply (fpos_ne_feasible (mir_xz (pos_y s)) Hsx Hsy HneQ).
    + intros a0 b0 c0 Hinp Hsol Hc1.
      pose proof (in_mir_xz_inv _ _ _ _ Hinp) as Hins0.
      destruct (mem3_pos_y_inv _ _ _ _ Hins0) as [Hins Hb].
      pose proof (sol_q2 a0 b0 c0 Hsol Hb Hc1) as Hts0.
      pose proof (Hct _ _ _ Hins Hts0) as Hint.
      pose proof (in_mir_xz t (- a0) b0 (- c0) Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
  - (* Q3 *)
    intro HneQ. rewrite <- (mir_xy_invol t).
    apply (proj2 (sle3_mir_xy (zfdiv_pos3 (mir_xy (neg_y s))) (mir_xy t))).
    rewrite ne_mir_xy in HneQ.
    destruct (zfdiv_pos3_ne_input _ HneQ) as [Hsx Hsy].
    apply fpos_best.
    + apply (fpos_ne_feasible (mir_xy (neg_y s)) Hsx Hsy HneQ).
    + intros a0 b0 c0 Hinp Hsol Hc1.
      pose proof (in_mir_xy_inv _ _ _ _ Hinp) as Hins0.
      destruct (mem3_neg_y_inv _ _ _ _ Hins0) as [Hins Hb].
      pose proof (sol_q3 a0 b0 c0 Hsol ltac:(lia) Hc1) as Hts0.
      pose proof (Hct _ _ _ Hins Hts0) as Hint.
      pose proof (in_mir_xy t (- a0) (- b0) c0 Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
  - (* Q4 *)
    intro HneQ. rewrite <- (mir_yz_invol t).
    apply (proj2 (sle3_mir_yz (zfdiv_pos3 (mir_yz (neg_y s))) (mir_yz t))).
    rewrite ne_mir_yz in HneQ.
    destruct (zfdiv_pos3_ne_input _ HneQ) as [Hsx Hsy].
    apply fpos_best.
    + apply (fpos_ne_feasible (mir_yz (neg_y s)) Hsx Hsy HneQ).
    + intros a0 b0 c0 Hinp Hsol Hc1.
      pose proof (in_mir_yz_inv _ _ _ _ Hinp) as Hins0.
      destruct (mem3_neg_y_inv _ _ _ _ Hins0) as [Hins Hb].
      pose proof (sol_q4 a0 b0 c0 Hsol ltac:(lia) Hc1) as Hts0.
      pose proof (Hct _ _ _ Hins Hts0) as Hint.
      pose proof (in_mir_yz t a0 (- b0) (- c0) Hint) as Hmt.
      rewrite !Z.opp_involutive in Hmt. exact Hmt.
Qed.

(* ================================================================== *)
(** ** (F) Non-empty output implies feasibility                        *)
(* ================================================================== *)

Lemma ne_join4_split : forall p q,
  ne_store3 (join4 p q) = true -> ne_store3 p = true \/ ne_store3 q = true.
Proof.
  intros p q H. unfold join4 in H.
  destruct (negb (ne_store3 p)) eqn:Ep.
  - right; exact H.
  - left. destruct (ne_store3 p); [reflexivity | discriminate Ep].
Qed.

Theorem ztdivq_ne_feasible : forall s,
  ne_store3 (ztdivq s) = true -> feasible3 tsol s.
Proof.
  intros s Hne. unfold ztdivq in Hne.
  destruct (ne_store3 s) eqn:Es; [ | cbn in Hne; congruence ].
  cbn [negb] in Hne.
  destruct (ne_store3_parts s Es) as (Esx & Esy & Esz).
  destruct (ne_join4_split _ _ Hne) as [H1 | Hne2].
  - (* Q1 *)
    destruct (zfdiv_pos3_ne_input _ H1) as [Hsx Hsy].
    destruct (fpos_ne_feasible (pos_y s) Hsx Hsy H1)
      as (vx & vy & vz & Hin & Hsol & Hvz).
    destruct (mem3_pos_y_inv _ _ _ _ Hin) as [Hins Hb].
    exists vx, vy, vz. split; [exact Hins | apply sol_q1; [exact Hsol | exact Hb | exact Hvz]].
  - destruct (ne_join4_split _ _ Hne2) as [H2 | Hne3].
    + (* Q2 *)
      rewrite ne_mir_xz in H2.
      destruct (zfdiv_pos3_ne_input _ H2) as [Hsx Hsy].
      destruct (fpos_ne_feasible (mir_xz (pos_y s)) Hsx Hsy H2)
        as (vx & vy & vz & Hin & Hsol & Hvz).
      pose proof (in_mir_xz_inv _ _ _ _ Hin) as Hins0.
      destruct (mem3_pos_y_inv _ _ _ _ Hins0) as [Hins Hb].
      exists (- vx), vy, (- vz).
      split; [exact Hins | apply sol_q2; [exact Hsol | exact Hb | exact Hvz]].
    + destruct (ne_join4_split _ _ Hne3) as [H3 | H4].
      * (* Q3 *)
        rewrite ne_mir_xy in H3.
        destruct (zfdiv_pos3_ne_input _ H3) as [Hsx Hsy].
        destruct (fpos_ne_feasible (mir_xy (neg_y s)) Hsx Hsy H3)
          as (vx & vy & vz & Hin & Hsol & Hvz).
        pose proof (in_mir_xy_inv _ _ _ _ Hin) as Hins0.
        destruct (mem3_neg_y_inv _ _ _ _ Hins0) as [Hins Hb].
        exists (- vx), (- vy), vz.
        split; [exact Hins | apply sol_q3; [exact Hsol | lia | exact Hvz]].
      * (* Q4 *)
        rewrite ne_mir_yz in H4.
        destruct (zfdiv_pos3_ne_input _ H4) as [Hsx Hsy].
        destruct (fpos_ne_feasible (mir_yz (neg_y s)) Hsx Hsy H4)
          as (vx & vy & vz & Hin & Hsol & Hvz).
        pose proof (in_mir_yz_inv _ _ _ _ Hin) as Hins0.
        destruct (mem3_neg_y_inv _ _ _ _ Hins0) as [Hins Hb].
        exists vx, (- vy), (- vz).
        split; [exact Hins | apply sol_q4; [exact Hsol | lia | exact Hvz]].
Qed.

(* ================================================================== *)
(** ** (G) Completeness (unconditional, quotient order)                *)
(* ================================================================== *)

Theorem ztdivq_complete : forall s t, contains3 tsol s t -> sle3 (ztdivq s) t.
Proof.
  intros s t Hct. destruct (ne_store3 (ztdivq s)) eqn:E;
    [ exact (ztdivq_best_feasible s (ztdivq_ne_feasible s E) t Hct)
    | apply sle3_bot; exact E ].
Qed.

(* [ztdivq] is a CLOSURE OPERATOR (reductive, monotone, idempotent up to ~):
   for free from soundness + completeness + ne-feasibility via [closure_laws]. *)
Theorem ztdivq_reductive : forall s, sle3 (ztdivq s) s.
Proof. exact (proj1 (closure_laws tsol ztdivq ztdivq_soundness (fun s _ => ztdivq_complete s) ztdivq_ne_feasible)). Qed.
Theorem ztdivq_monotone : forall s t, sle3 s t -> sle3 (ztdivq s) (ztdivq t).
Proof. exact (proj1 (proj2 (closure_laws tsol ztdivq ztdivq_soundness (fun s _ => ztdivq_complete s) ztdivq_ne_feasible))). Qed.
Theorem ztdivq_idempotent : forall s,
  sle3 (ztdivq (ztdivq s)) (ztdivq s) /\ sle3 (ztdivq s) (ztdivq (ztdivq s)).
Proof. exact (proj2 (proj2 (closure_laws tsol ztdivq ztdivq_soundness (fun s _ => ztdivq_complete s) ztdivq_ne_feasible))). Qed.

(* Complete on singleton: on a fully-fixed store, a non-empty output forces the
   assignment to be an actual solution.  Immediate from [ztdivq_ne_feasible]
   (ztdivq is the best propagator): a non-empty output makes the slice feasible,
   and on a singleton the only feasible point is (vx,vy,vz) itself. *)
Theorem ztdivq_singleton_complete : forall s vx vy vz,
  sx3 s = Itv (Fin vx) (Fin vx) ->
  sy3 s = Itv (Fin vy) (Fin vy) ->
  sz3 s = Itv (Fin vz) (Fin vz) ->
  ne_store3 (ztdivq s) = true -> tsol vx vy vz.
Proof.
  intros s vx vy vz Hx Hy Hz Hne.
  destruct (ztdivq_ne_feasible s Hne) as (vx' & vy' & vz' & Hin & Hts).
  destruct Hin as (Hmx & Hmy & Hmz).
  rewrite Hx in Hmx; rewrite Hy in Hmy; rewrite Hz in Hmz.
  unfold mem3 in Hmx, Hmy, Hmz; cbn in Hmx, Hmy, Hmz.
  destruct Hmx as [Hax Hbx]; destruct Hmy as [Hay Hby]; destruct Hmz as [Haz Hbz].
  assert (vx' = vx) by lia; assert (vy' = vy) by lia; assert (vz' = vz) by lia; subst.
  exact Hts.
Qed.
