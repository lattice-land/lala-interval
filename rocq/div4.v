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

    The Zinf interval infrastructure ([Zinf], [itv3], [store3], the
    infinity-aware helpers [sadd3]/[imul3]/[idivf3]/[idivc3]) is reused from
    [fdiv3]; none of that file's admitted theorems is used here. *)

From Stdlib Require Import ZArith Lia Bool.
From LalaInterval Require Import itv fdiv2 fdiv3.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Additional helpers: truncated corner division, mirroring        *)
(* ------------------------------------------------------------------ *)

(* trunc(n/m) with limit semantics (precondition of use: m <> Fin 0);
   mirrors the C++ [idiv_t]. *)
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
Definition ineg3 (a : Zinf) : Zinf :=
  match a with Fin v => Fin (- v) | Pinf => Ninf | Ninf => Pinf end.

(* [l, u] := [-u, -l]; mirrors the C++ [zmirror] (bot maps to bot). *)
Definition mirror_i (i : itv3) : itv3 := Itv3 (ineg3 (hi3 i)) (ineg3 (lo3 i)).

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
Definition botitv3 : itv3 := Itv3 Pinf Ninf.

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
  let z := Itv3 (zmax (lo3 (sz3 s)) (Fin 1)) (hi3 (sz3 s)) in
  if negb (nonempty3b z) then St3 x y z else
  (* Z: x.lb * z <= y.ub *)
  let z :=
    if zpos (lo3 x) then Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (hi3 y) (lo3 x)))
    else if negb (ziszero (lo3 x)) then
      Itv3 (zmax (lo3 z) (idivc3 (hi3 y) (lo3 x))) (hi3 z)
    else if zneg (hi3 y) then botitv3 else z in
  (* Z: (x.ub + 1) * z >= y.lb + 1 *)
  let z :=
    if zge0 (hi3 x) then
      Itv3 (zmax (lo3 z) (idivc3 (sadd3 (lo3 y) 1) (sadd3 (hi3 x) 1))) (hi3 z)
    else if negb (zeqm1 (hi3 x)) then
      Itv3 (lo3 z) (zmin (hi3 z) (idivf3 (sadd3 (lo3 y) 1) (sadd3 (hi3 x) 1)))
    else if zge0 (lo3 y) then botitv3 else z in
  if negb (nonempty3b z) then St3 x y z else
  (* Y: hull of [x.lb*z, (x.ub+1)*z - 1] over the narrowed z *)
  let y := Itv3
    (zmax (lo3 y) (zmin (imul3 (lo3 x) (lo3 z)) (imul3 (lo3 x) (hi3 z))))
    (zmin (hi3 y) (zmax (sadd3 (imul3 (sadd3 (hi3 x) 1) (lo3 z)) (-1))
                        (sadd3 (imul3 (sadd3 (hi3 x) 1) (hi3 z)) (-1)))) in
  if negb (nonempty3b y) then St3 x y z else
  (* X: 4-corner hull of fdiv(y, z) *)
  let x := Itv3
    (zmax (lo3 x) (zmin (zmin (idivf3 (lo3 y) (lo3 z)) (idivf3 (lo3 y) (hi3 z)))
                        (zmin (idivf3 (hi3 y) (lo3 z)) (idivf3 (hi3 y) (hi3 z)))))
    (zmin (hi3 x) (zmax (zmax (idivf3 (lo3 y) (lo3 z)) (idivf3 (lo3 y) (hi3 z)))
                        (zmax (idivf3 (hi3 y) (lo3 z)) (idivf3 (hi3 y) (hi3 z))))) in
  St3 x y z.

(** Contracts x, y, z for x = tdiv(y, z) on the positive slice of z;
    mirrors the C++ [ztdiv_pos]:
      band  tdiv(y, z) in [xl, xu]  <=>  y in [tymin(xl, z), tymax(xu, z)]
      with tymin(v, z) = v > 0 ? v*z : (v-1)*z + 1
      and  tymax(v, z) = v >= 0 ? (v+1)*z - 1 : v*z. *)
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
Definition join4 (pos neg : store3) : store3 :=
  if negb (ne_store3 pos) then neg
  else if negb (ne_store3 neg) then pos
  else sjoin3 pos neg.

Definition ztdiv4 (s : store3) : store3 :=
  if negb (ne_store3 s) then s
  else join4 (ztdiv_pos3 s) (mir_xz (ztdiv_pos3 (mir_xz s))).

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
(** ** Solutions of the four divisions                                 *)
(* ------------------------------------------------------------------ *)

(* floor: fdiv2.sol = z <> 0 /\ x = y / z (Z.div is the floor division) *)
Definition tsol (x y z : Z) : Prop := z <> 0 /\ x = Z.quot y z.
Definition csol (x y z : Z) : Prop := z <> 0 /\ x = cdiv y z.
Definition esol (x y z : Z) : Prop :=
  z <> 0 /\ x = (if 0 <? z then y / z else cdiv y z).

(* generic containment/feasibility, parameterized by the solution predicate *)
Definition contains3 (P : Z -> Z -> Z -> Prop) (s t : store3) : Prop :=
  forall vx vy vz, in_store3 s vx vy vz -> P vx vy vz -> in_store3 t vx vy vz.
Definition feasible3 (P : Z -> Z -> Z -> Prop) (s : store3) : Prop :=
  exists vx vy vz, in_store3 s vx vy vz /\ P vx vy vz.

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
Lemma F2 : forall n d q, 0 < d -> n <= d*q -> n / d <= q.
Proof. intros; apply Z.div_le_upper_bound; auto. Qed.
(* floor, negative divisor *)
Lemma FN1 : forall n d q, d < 0 -> n <= d*q -> q <= n / d.
Proof.
  intros n d q Hd Hle.
  rewrite <- (Z.div_opp_opp n d) by lia.
  apply Z.div_le_lower_bound; lia.
Qed.
Lemma FN2 : forall n d q, d < 0 -> d*q <= n -> n / d <= q.
Proof.
  intros n d q Hd Hle.
  rewrite <- (Z.div_opp_opp n d) by lia.
  apply Z.div_le_upper_bound; lia.
Qed.
(* ceil = cdiv, positive divisor *)
Lemma CC1 : forall n d q, 0 < d -> n <= d*q -> cdiv n d <= q.
Proof.
  intros n d q Hd Hle. unfold cdiv.
  assert (H: - q <= (- n) / d) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.
Lemma CC2 : forall n d q, 0 < d -> d*q <= n -> q <= cdiv n d.
Proof.
  intros n d q Hd Hle. unfold cdiv.
  assert (H: (- n) / d <= - q) by (apply Z.div_le_upper_bound; lia).
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
Lemma C2 : forall n d q, d < 0 -> n <= d*q -> q <= cdiv n d.
Proof.
  intros n d q Hd Hle. unfold cdiv.
  rewrite <- (Z.div_opp_opp (-n) d) by lia.
  assert (H: (- - n) / (- d) <= - q) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

(* ================= band lemmas for truncated division (z>0) ================= *)
(* tymin v z = min y with Z.quot y z >= v ; tymax v z = max y with Z.quot y z <= v *)

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
Lemma zle_zmax_r : forall a b, zle b (zmax a b).
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.
Lemma zmin_zle_r : forall a b, zle (zmin a b) b.
Proof. intros [x| |] [y| |]; cbn; try exact I; lia. Qed.
Lemma zle_trans' : forall a b c, zle a b -> zle b c -> zle a c.
Proof. exact zle_trans. Qed.

(* ===== corner bracket lemmas for the X step ===== *)
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
Lemma mem3_narrow_hi : forall lo hi B v,
  zle lo (Fin v) -> zle (Fin v) hi -> zle (Fin v) B ->
  mem3 (Itv3 lo (zmin hi B)) v.
Proof. intros; unfold mem3; cbn [lo3 hi3]; split; [assumption | apply zle_zmin_glb; assumption]. Qed.
Lemma mem3_narrow_lo : forall lo hi B v,
  zle lo (Fin v) -> zle (Fin v) hi -> zle B (Fin v) ->
  mem3 (Itv3 (zmax lo B) hi) v.
Proof. intros; unfold mem3; cbn [lo3 hi3]; split; [apply zmax_lub; assumption | assumption]. Qed.

(* ===== Z-step obligations ===== *)
(* Z1: tymin(x.lb,z) <= y.ub  --> refine z *)
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
Lemma imul3_fp : forall a, 0 < a -> imul3 (Fin a) Pinf = Pinf.
Proof. intros a Ha. cbn. rewrite (proj2 (Z.eqb_neq a 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 a) Ha). reflexivity. Qed.
Lemma imul3_fn : forall a, a < 0 -> imul3 (Fin a) Pinf = Ninf.
Proof. intros a Ha. cbn. rewrite (proj2 (Z.eqb_neq a 0) ltac:(lia)), (proj2 (Z.ltb_ge 0 a) ltac:(lia)). reflexivity. Qed.
Lemma imul3_ninf_fp : forall z, 0 < z -> imul3 Ninf (Fin z) = Ninf.
Proof. intros z Hz. cbn. rewrite (proj2 (Z.eqb_neq z 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 z) Hz). reflexivity. Qed.
Lemma imul3_pinf_fp : forall z, 0 < z -> imul3 Pinf (Fin z) = Pinf.
Proof. intros z Hz. cbn. rewrite (proj2 (Z.eqb_neq z 0) ltac:(lia)), (proj2 (Z.ltb_lt 0 z) Hz). reflexivity. Qed.

(* ===== Y-step obligations (abstract over the narrowed z-interval iz) ===== *)
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
Lemma mem3_narrow_both : forall lo hi Bl Bh v,
  zle lo (Fin v) -> zle (Fin v) hi -> zle Bl (Fin v) -> zle (Fin v) Bh ->
  mem3 (Itv3 (zmax lo Bl) (zmin hi Bh)) v.
Proof.
  intros; unfold mem3; cbn [lo3 hi3]; split;
    [apply zmax_lub; assumption | apply zle_zmin_glb; assumption].
Qed.

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
  zle yb (Fin vy) -> zle (Fin 1) zl -> zle zl (Fin vz) -> zle (Fin vz) zu ->
  zle (zmin (idivf3 yb zl) (idivf3 yb zu)) (Fin (vy / vz)).
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
    + (* zu = Pinf : idivf3 (Fin ylv) Pinf = Fin (if ylv<?0 then -1 else 0) *)
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
  - cbn [idivf3]. rewrite (proj2 (Z.ltb_lt 0 zlv) ltac:(lia)). destruct zu; cbn; exact I.
Qed.

Lemma flo_xhi : forall yb zl zu vy vz,
  zle (Fin vy) yb -> zle (Fin 1) zl -> zle zl (Fin vz) -> zle (Fin vz) zu ->
  zle (Fin (vy / vz)) (zmax (idivf3 yb zl) (idivf3 yb zu)).
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
  - cbn [idivf3]. rewrite (proj2 (Z.ltb_lt 0 zlv) ltac:(lia)). destruct zu; cbn; exact I.
Qed.

(* ===== Y corner brackets for floor (uniform over the sign of x) ===== *)
Lemma flo_ylo : forall s vy vz iz,
  1 <= vz -> zle (Fin 1) (lo3 iz) -> zle (lo3 iz) (Fin vz) -> zle (Fin vz) (hi3 iz) ->
  zle (lo3 (sx3 s)) (Fin (vy / vz)) ->
  zle (zmin (imul3 (lo3 (sx3 s)) (lo3 iz)) (imul3 (lo3 (sx3 s)) (hi3 iz))) (Fin vy).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxl.
  destruct (lo3 iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Hxl; try contradiction.
  - pose proof (floor_lb a vy vz ltac:(lia) Hxl) as Hb.  (* a*vz <= vy *)
    destruct (hi3 iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn. destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
      * pose proof (Z.le_min_l (a*zl) (a*zu)). nia.
      * pose proof (Z.le_min_r (a*zl) (a*zu)). nia.
    + destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
      * rewrite imul3_fn by lia. cbn. exact I.
      * subst a. cbn. nia.
      * rewrite imul3_fp by lia. cbn. nia.
  - rewrite imul3_ninf_fp by lia. cbn. exact I.
Qed.

Lemma flo_yhi : forall s vy vz iz,
  1 <= vz -> zle (Fin 1) (lo3 iz) -> zle (lo3 iz) (Fin vz) -> zle (Fin vz) (hi3 iz) ->
  zle (Fin (vy / vz)) (hi3 (sx3 s)) ->
  zle (Fin vy) (zmax (sadd3 (imul3 (sadd3 (hi3 (sx3 s)) 1) (lo3 iz)) (-1))
                     (sadd3 (imul3 (sadd3 (hi3 (sx3 s)) 1) (hi3 iz)) (-1))).
Proof.
  intros s vy vz iz Hvz Hz1 Hzl Hzu Hxu.
  destruct (lo3 iz) as [zl| |]; cbn in Hz1, Hzl; try contradiction.
  destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Hxu; try contradiction.
  - pose proof (floor_ub b vy vz ltac:(lia) Hxu) as Hb.  (* vy <= (b+1)*vz-1 *)
    destruct (hi3 iz) as [zu| |]; cbn in Hzu; try contradiction.
    + cbn [sadd3 imul3]. cbn. destruct (Z.le_gt_cases 0 (b+1)) as [Hk|Hk].
      * pose proof (Z.le_max_r (b + 1 * zl + -1)%Z (b + 1 * zu + -1)%Z). nia.
      * pose proof (Z.le_max_l (b + 1 * zl + -1)%Z (b + 1 * zu + -1)%Z). nia.
    + cbn [sadd3]. destruct (Z.lt_trichotomy (b+1) 0) as [Hk|[Hk|Hk]].
      * rewrite imul3_fn by lia. cbn [sadd3]. cbn. nia.
      * replace (b + 1) with 0 by lia. cbn. nia.
      * rewrite imul3_fp by lia. cbn [sadd3]. cbn. exact I.
  - cbn [sadd3]. rewrite imul3_pinf_fp by lia. cbn [sadd3]. cbn. exact I.
Qed.

(* ===== floor Z-step membership (whole 4-way if, botitv3 => contradiction) ===== *)
Lemma flo_z1_mem : forall s vy vz z0,
  1 <= vz -> zle (lo3 z0) (Fin vz) -> zle (Fin vz) (hi3 z0) ->
  zle (lo3 (sx3 s)) (Fin (vy / vz)) -> zle (Fin vy) (hi3 (sy3 s)) ->
  mem3 (if zpos (lo3 (sx3 s))
        then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (hi3 (sy3 s)) (lo3 (sx3 s))))
        else if negb (ziszero (lo3 (sx3 s)))
             then Itv3 (zmax (lo3 z0) (idivc3 (hi3 (sy3 s)) (lo3 (sx3 s)))) (hi3 z0)
             else if zneg (hi3 (sy3 s)) then botitv3 else z0) vz.
Proof.
  intros s vy vz z0 Hvz Hz0l Hz0u Hxl Hyu.
  destruct (zpos (lo3 (sx3 s))) eqn:Ezp.
  - (* hi-narrow *)
    apply mem3_narrow_hi; [exact Hz0l | exact Hz0u | ].
    destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Ezp, Hxl; try discriminate; try contradiction.
    apply Z.ltb_lt in Ezp. pose proof (floor_lb a vy vz ltac:(lia) Hxl) as Hb.
    destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
    + cbn [idivf3]. cbn. apply F1; lia.
    + cbn [idivf3]. rewrite (proj2 (Z.ltb_lt 0 a) Ezp). exact I.
  - destruct (ziszero (lo3 (sx3 s))) eqn:Ez; cbn [negb].
    + (* ziszero true : lo x = 0 *)
      destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Ez; try discriminate.
      apply Z.eqb_eq in Ez. subst a. cbn in Hxl. (* 0 <= vy/vz *)
      destruct (zneg (hi3 (sy3 s))) eqn:Eyn.
      * (* botitv3 : no solution *)
        exfalso.
        destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Eyn, Hyu; try discriminate; try contradiction.
        apply Z.ltb_lt in Eyn. (* u < 0, vy <= u *)
        pose proof (Z.mul_div_le vy vz ltac:(lia)). nia.
      * exact (conj Hz0l Hz0u).
    + (* lo-narrow : lo x < 0 or Ninf *)
      apply mem3_narrow_lo; [exact Hz0l | exact Hz0u | ].
      destruct (lo3 (sx3 s)) as [a| |] eqn:Ex; cbn in Ezp, Ez, Hxl; try discriminate.
      * (* Fin a, a < 0 *)
        apply Z.ltb_ge in Ezp. apply Z.eqb_neq in Ez.
        pose proof (floor_lb a vy vz ltac:(lia) Hxl) as Hb.
        destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
        -- cbn [idivc3]. cbn. apply C1; [lia | nia].
        -- cbn [idivc3]. rewrite (proj2 (Z.ltb_ge 0 a) ltac:(lia)). exact I.
      * (* Ninf : bound 0 or 1 <= vz *)
        destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Hyu; try contradiction.
        -- cbn [idivc3]. destruct (u <? 0); cbn; lia.
        -- cbn [idivc3]. cbn; lia.
Qed.

Lemma flo_z2_mem : forall s vy vz z0,
  1 <= vz -> zle (lo3 z0) (Fin vz) -> zle (Fin vz) (hi3 z0) ->
  zle (Fin (vy / vz)) (hi3 (sx3 s)) -> zle (lo3 (sy3 s)) (Fin vy) ->
  mem3 (if zge0 (hi3 (sx3 s))
        then Itv3 (zmax (lo3 z0) (idivc3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1))) (hi3 z0)
        else if negb (zeqm1 (hi3 (sx3 s)))
             then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1)))
             else if zge0 (lo3 (sy3 s)) then botitv3 else z0) vz.
Proof.
  intros s vy vz z0 Hvz Hz0l Hz0u Hxu Hyl.
  destruct (zge0 (hi3 (sx3 s))) eqn:Ezg.
  - (* lo-narrow *)
    apply mem3_narrow_lo; [exact Hz0l | exact Hz0u | ].
    destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Ezg, Hxu; try discriminate; try contradiction.
    + apply Z.leb_le in Ezg. pose proof (floor_ub b vy vz ltac:(lia) Hxu) as Hb.
      destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
      * cbn [sadd3 idivc3]. cbn. apply CC1; lia.
      * cbn [sadd3 idivc3]. rewrite (proj2 (Z.ltb_lt 0 (b+1)) ltac:(lia)). exact I.
    + (* Pinf *)
      cbn [sadd3].
      destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
      * cbn [sadd3 idivc3]. destruct (0 <? l + 1); cbn; lia.
      * cbn [sadd3 idivc3]. cbn; lia.
  - destruct (zeqm1 (hi3 (sx3 s))) eqn:Ee; cbn [negb].
    + (* zeqm1 true : hi x = -1 *)
      destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Ee; try discriminate.
      apply Z.eqb_eq in Ee. subst b. cbn in Hxu. (* vy/vz <= -1 *)
      destruct (zge0 (lo3 (sy3 s))) eqn:Eyl.
      * (* botitv3 : no solution *)
        exfalso.
        destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Eyl, Hyl; try discriminate; try contradiction.
        apply Z.leb_le in Eyl. (* 0 <= l <= vy *)
        pose proof (Z.div_pos vy vz ltac:(lia) ltac:(lia)). lia.
      * exact (conj Hz0l Hz0u).
    + (* hi-narrow : hi x < 0, != -1, or Ninf *)
      apply mem3_narrow_hi; [exact Hz0l | exact Hz0u | ].
      destruct (hi3 (sx3 s)) as [b| |] eqn:Ex; cbn in Ezg, Ee, Hxu; try discriminate; try contradiction.
      * (* Fin b, b < 0, b <> -1 *)
        apply Z.leb_gt in Ezg. apply Z.eqb_neq in Ee.
        pose proof (floor_ub b vy vz ltac:(lia) Hxu) as Hb.
        destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Hyl; try contradiction.
        -- cbn [sadd3 idivf3]. cbn. apply FN1; [lia | nia].
        -- cbn [sadd3 idivf3]. rewrite (proj2 (Z.ltb_ge 0 (b+1)) ltac:(lia)). exact I.
Qed.

(* ===== positivity of the narrowed z (lo stays >= 1) ===== *)
Lemma flo_z1_pos : forall s z0, zle (Fin 1) (lo3 z0) ->
  zle (Fin 1) (lo3 (if zpos (lo3 (sx3 s))
        then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (hi3 (sy3 s)) (lo3 (sx3 s))))
        else if negb (ziszero (lo3 (sx3 s)))
             then Itv3 (zmax (lo3 z0) (idivc3 (hi3 (sy3 s)) (lo3 (sx3 s)))) (hi3 z0)
             else if zneg (hi3 (sy3 s)) then botitv3 else z0)).
Proof.
  intros s z0 H.
  destruct (zpos (lo3 (sx3 s))); [cbn [lo3]; exact H | ].
  destruct (ziszero (lo3 (sx3 s))); cbn [negb].
  - destruct (zneg (hi3 (sy3 s))); [cbn; exact I | cbn [lo3]; exact H].
  - cbn [lo3]. eapply zle_trans; [exact H | apply zle_zmax_l].
Qed.

Lemma flo_z2_pos : forall s z0, zle (Fin 1) (lo3 z0) ->
  zle (Fin 1) (lo3 (if zge0 (hi3 (sx3 s))
        then Itv3 (zmax (lo3 z0) (idivc3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1))) (hi3 z0)
        else if negb (zeqm1 (hi3 (sx3 s)))
             then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1)))
             else if zge0 (lo3 (sy3 s)) then botitv3 else z0)).
Proof.
  intros s z0 H.
  destruct (zge0 (hi3 (sx3 s))); [cbn [lo3]; eapply zle_trans; [exact H | apply zle_zmax_l] | ].
  destruct (zeqm1 (hi3 (sx3 s))); cbn [negb].
  - destruct (zge0 (lo3 (sy3 s))); [cbn; exact I | cbn [lo3]; exact H].
  - cbn [lo3]; exact H.
Qed.

Theorem fpos_sound : forall s vx vy vz,
  in_store3 s vx vy vz -> sol vx vy vz -> 1 <= vz ->
  in_store3 (zfdiv_pos3 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hsol Hvz1.
  destruct Hin as (Hmx & Hmy & Hmz).
  destruct Hsol as [Hnz Hq]. subst vx.
  destruct Hmx as [Hxl Hxu]; destruct Hmy as [Hyl Hyu]; destruct Hmz as [Hzl0 Hzu0].
  unfold zfdiv_pos3; cbv zeta.
  match goal with |- context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hmz0l : zle (lo3 z0) (Fin vz)) by (rewrite Hz0; cbn [lo3]; apply zmax_lub; [exact Hzl0 | cbn; lia]).
  assert (Hmz0u : zle (Fin vz) (hi3 z0)) by (rewrite Hz0; cbn [hi3]; exact Hzu0).
  assert (Hlz0 : zle (Fin 1) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_r).
  destruct (negb (nonempty3b z0)) eqn:E0.
  { split; [exact (conj Hxl Hxu) | split; [exact (conj Hyl Hyu) | exact (conj Hmz0l Hmz0u)]]. }
  match goal with |- context[if zpos (lo3 (sx3 s)) then ?A else ?B] =>
    remember (if zpos (lo3 (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hmz1 : mem3 z1 vz) by
    (rewrite Hz1; apply (flo_z1_mem s vy vz z0); [exact Hvz1|exact Hmz0l|exact Hmz0u|exact Hxl|exact Hyu]).
  assert (Hlz1 : zle (Fin 1) (lo3 z1)) by (rewrite Hz1; apply flo_z1_pos; exact Hlz0).
  destruct Hmz1 as [Hmz1l Hmz1u].
  match goal with |- context[if zge0 (hi3 (sx3 s)) then ?A else ?B] =>
    remember (if zge0 (hi3 (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hmz2 : mem3 z2 vz) by
    (rewrite Hz2; apply (flo_z2_mem s vy vz z1); [exact Hvz1|exact Hmz1l|exact Hmz1u|exact Hxu|exact Hyl]).
  assert (Hlz2 : zle (Fin 1) (lo3 z2)) by (rewrite Hz2; apply flo_z2_pos; exact Hlz1).
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
    + eapply zle_trans; [apply zmin_zle_l | ].
      apply (flo_xlo (lo3 yF) (lo3 z2) (hi3 z2)); [exact HmyL|exact Hlz2|exact Hmz2l|exact Hmz2u].
    + eapply zle_trans; [ | apply zle_zmax_r ].
      apply (flo_xhi (hi3 yF) (lo3 z2) (hi3 z2)); [exact HmyU|exact Hlz2|exact Hmz2l|exact Hmz2u].
  - split; [exact (conj HmyL HmyU) | exact (conj Hmz2l Hmz2u)].
Qed.


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
Lemma z1band_pos : forall yu vz a, 0 < a -> yu <> Ninf ->
  zle (Fin vz) (idivf3 yu (Fin a)) -> zle (Fin (a * vz)) yu.
Proof.
  intros yu vz a Ha Hyn H.
  destruct yu as [u| |]; try congruence.
  - cbn [idivf3] in H. cbn in H. cbn. apply mul_le_div; lia.
  - cbn. exact I.
Qed.

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

Lemma z2band_pos : forall yl vz b, 0 <= b -> yl <> Pinf ->
  zle (idivc3 (sadd3 yl 1) (sadd3 (Fin b) 1)) (Fin vz) ->
  zle yl (Fin ((b + 1) * vz - 1)).
Proof.
  intros yl vz b Hb Hyp H. cbn [sadd3] in H.
  destruct yl as [l| |]; try congruence.
  - cbn [sadd3 idivc3] in H. cbn in H.
    assert (Hle : l + 1 <= (b + 1) * vz) by (apply RCC1; [lia | exact H]). cbn. nia.
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
Lemma nonempty_bounds : forall i, nonempty3b i = true -> lo3 i <> Pinf /\ hi3 i <> Ninf.
Proof. intros [[a| |] [b| |]]; cbn; intro H; try discriminate; split; discriminate. Qed.

Lemma ne_zle : forall i, nonempty3b i = true -> zle (lo3 i) (hi3 i).
Proof.
  intros [[a| |] [b| |]]; cbn; intro H; try discriminate; try exact I. apply Z.leb_le; exact H.
Qed.

Definition pickf (L U : Zinf) : Z :=
  match L with Fin l => l | _ => match U with Fin u => u | _ => 0 end end.

Lemma pickf_mem : forall L U, zle L U -> L <> Pinf -> U <> Ninf ->
  zle L (Fin (pickf L U)) /\ zle (Fin (pickf L U)) U.
Proof.
  intros [l| |] [u| |] H Hl Hu; cbn in *; try congruence; split; try exact I; lia.
Qed.

(* ===== step monotonicity (lo does not decrease, hi does not increase) ===== *)
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

Lemma zle_Pinf : forall a, zle a Pinf.
Proof. intros [v| |]; cbn; exact I. Qed.

Lemma fin_of_ge1 : forall a, zle (Fin 1) a -> a <> Pinf -> exists v, a = Fin v /\ 1 <= v.
Proof.
  intros [v| |] H Hp; cbn in *; [exists v; split; [reflexivity | lia] | congruence | contradiction].
Qed.

(* ===== the propagator-reconstruction core ===== *)
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
Lemma zmax_not_Pinf : forall a b, a <> Pinf -> b <> Pinf -> zmax a b <> Pinf.
Proof. intros [x| |] [y| |] Ha Hb; cbn; congruence. Qed.
Lemma zmin_not_Ninf : forall a b, a <> Ninf -> b <> Ninf -> zmin a b <> Ninf.
Proof. intros [x| |] [y| |] Ha Hb; cbn; congruence. Qed.
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
Lemma zle_ineg3_r : forall a v, zle a (Fin v) -> zle (Fin (- v)) (ineg3 a).
Proof. intros [x| |] v H; cbn in *; try exact I; try contradiction; lia. Qed.
Lemma zle_ineg3_l : forall a v, zle (Fin v) a -> zle (ineg3 a) (Fin (- v)).
Proof. intros [x| |] v H; cbn in *; try exact I; try contradiction; lia. Qed.

Lemma mem3_mirror : forall i v, mem3 i v -> mem3 (mirror_i i) (- v).
Proof.
  intros i v [Hlo Hhi]. unfold mirror_i, mem3; cbn [lo3 hi3].
  split; [apply zle_ineg3_l; exact Hhi | apply zle_ineg3_r; exact Hlo].
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
  destruct (lo3 i) as [a| |]; destruct (hi3 i) as [b| |]; cbn in *;
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
  intros i j v [Hlo Hhi]. unfold ijoin3, mem3; cbn [lo3 hi3]. split.
  - eapply zle_trans; [apply zmin_zle_l | exact Hlo].
  - eapply zle_trans; [exact Hhi | apply zle_zmax_l].
Qed.
Lemma mem3_ijoin_r : forall i j v, mem3 j v -> mem3 (ijoin3 i j) v.
Proof.
  intros i j v [Hlo Hhi]. unfold ijoin3, mem3; cbn [lo3 hi3]. split.
  - eapply zle_trans; [apply zmin_zle_r | exact Hlo].
  - eapply zle_trans; [exact Hhi | apply zle_zmax_r].
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

Lemma in_mir_yz : forall t a b c, in_store3 t a b c -> in_store3 (mir_yz t) a (- b) (- c).
Proof.
  intros t a b c (Hx & Hy & Hz).
  unfold mir_yz, in_store3; cbn [sx3 sy3 sz3].
  split; [exact Hx | split; [apply mem3_mirror; exact Hy | apply mem3_mirror; exact Hz]].
Qed.

Theorem zfdiv4_soundness : forall s vx vy vz,
  in_store3 s vx vy vz -> sol vx vy vz -> in_store3 (zfdiv4 s) vx vy vz.
Proof.
  intros s vx vy vz Hin Hsol.
  assert (Hne : ne_store3 s = true) by (eapply ne_store3_true; exact Hin).
  unfold zfdiv4. rewrite Hne. cbn [negb].
  destruct Hsol as [Hnz Hq].
  destruct (Z.lt_total vz 0) as [Hzneg | [Hz0 | Hzpos]].
  - (* vz <= -1 : negative slice via mir_yz *)
    apply in_join4_r.
    assert (Hmir : in_store3 (mir_yz s) vx (- vy) (- vz)) by (apply in_mir_yz; exact Hin).
    assert (Hsmir : sol vx (- vy) (- vz)).
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
  destruct (Z.lt_total vz 0) as [Hzneg | [Hz0 | Hzpos]].
  - (* vz <= -1 : ceil(y/z) = -floor(y/(-z)) via mir_xz *)
    apply in_join4_r.
    assert (Hmir : in_store3 (mir_xz s) (- vx) vy (- vz)) by (apply in_mir_xz; exact Hin).
    assert (Hsmir : sol (- vx) vy (- vz)).
    { split; [lia | ]. rewrite Hq. rewrite Z.opp_involutive. apply div_opp_num_den; lia. }
    pose proof (fpos_sound (mir_xz s) (- vx) vy (- vz) Hmir Hsmir ltac:(lia)) as Hp.
    pose proof (in_mir_xz (zfdiv_pos3 (mir_xz s)) (- vx) vy (- vz) Hp) as Hb.
    rewrite !Z.opp_involutive in Hb. exact Hb.
  - exfalso; apply Hnz; exact Hz0.
  - (* vz >= 1 : ceil(y/z) = -floor((-y)/z) via mir_xy *)
    apply in_join4_l.
    assert (Hmir : in_store3 (mir_xy s) (- vx) (- vy) vz) by (apply in_mir_xy; exact Hin).
    assert (Hsmir : sol (- vx) (- vy) vz).
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
  destruct (Z.lt_total vz 0) as [Hzneg | [Hz0 | Hzpos]].
  - (* vz <= -1 : ediv = ceil = -floor(y/(-z)) via mir_xz *)
    rewrite (proj2 (Z.ltb_ge 0 vz) ltac:(lia)) in Hq.  (* 0<?vz = false -> vx = cdiv vy vz *)
    unfold cdiv in Hq.
    apply in_join4_r.
    assert (Hmir : in_store3 (mir_xz s) (- vx) vy (- vz)) by (apply in_mir_xz; exact Hin).
    assert (Hsmir : sol (- vx) vy (- vz)).
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
Lemma ineg3_le : forall a b, zle (ineg3 a) (ineg3 b) <-> zle b a.
Proof. intros [x| |] [y| |]; cbn; try tauto; lia. Qed.

Lemma ile3_mirror : forall i j, ile3 (mirror_i i) (mirror_i j) <-> ile3 i j.
Proof.
  intros i j. unfold ile3, mirror_i; cbn [lo3 hi3].
  rewrite !ineg3_le. tauto.
Qed.

Lemma sle3_mir_xz : forall a b, sle3 (mir_xz a) (mir_xz b) <-> sle3 a b.
Proof.
  intros a b. unfold sle3, mir_xz; cbn [sx3 sy3 sz3].
  rewrite !ile3_mirror. tauto.
Qed.

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

Lemma ineg3_invol : forall a, ineg3 (ineg3 a) = a.
Proof. intros [v| |]; cbn; try reflexivity; f_equal; lia. Qed.

Lemma mirror_i_invol : forall i, mirror_i (mirror_i i) = i.
Proof.
  intros i. unfold mirror_i; cbn [lo3 hi3]. rewrite !ineg3_invol. destruct i; reflexivity.
Qed.

Lemma mir_xz_invol : forall s, mir_xz (mir_xz s) = s.
Proof.
  intros [ix iy iz]. unfold mir_xz; cbn [sx3 sy3 sz3].
  rewrite !mirror_i_invol. reflexivity.
Qed.

(* ===== join4 = the bottom-absorbing lub; case lemma for sle ===== *)
Lemma ile3_ijoin3 : forall i j k, ile3 i k -> ile3 j k -> ile3 (ijoin3 i j) k.
Proof. exact ijoin3_ile3. Qed.

Lemma sjoin3_lub : forall a b t, sle3 a t -> sle3 b t -> sle3 (sjoin3 a b) t.
Proof.
  intros a b t (Hax&Hay&Haz) (Hbx&Hby&Hbz).
  unfold sjoin3, sle3; cbn [sx3 sy3 sz3].
  repeat split; apply ijoin3_ile3; assumption.
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
    + apply sjoin3_lub; [apply Hp; reflexivity | apply Hn; reflexivity].
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

Lemma tsol_mir : forall vx vy vz, tsol vx vy vz -> tsol (- vx) vy (- vz).
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  rewrite Z.quot_opp_r by lia. rewrite Hq. reflexivity.
Qed.

Lemma ne_store3_parts : forall s, ne_store3 s = true ->
  nonempty3b (sx3 s) = true /\ nonempty3b (sy3 s) = true /\ nonempty3b (sz3 s) = true.
Proof.
  intros s H. unfold ne_store3 in H.
  apply andb_true_iff in H as [H Hz]. apply andb_true_iff in H as [Hx Hy]. auto.
Qed.

Lemma sle3_mir_yz : forall a b, sle3 (mir_yz a) (mir_yz b) <-> sle3 a b.
Proof.
  intros a b. unfold sle3, mir_yz; cbn [sx3 sy3 sz3].
  rewrite !ile3_mirror. tauto.
Qed.

Lemma ne_mir_yz : forall s, ne_store3 (mir_yz s) = ne_store3 s.
Proof.
  intros s. unfold ne_store3, mir_yz; cbn [sx3 sy3 sz3].
  rewrite !nonempty3b_mirror. reflexivity.
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

Lemma sol_mir : forall vx vy vz, sol vx vy vz -> sol vx (- vy) (- vz).
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  rewrite Z.div_opp_opp by lia. exact Hq.
Qed.

(* ===== truncated best transformer (positive slice), transplanted ===== *)
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

Lemma mem3_lo : forall i v, mem3 i v -> zle (lo3 i) (Fin v).
Proof. intros i v [H _]; exact H. Qed.
Lemma mem3_hi : forall i v, mem3 i v -> zle (Fin v) (hi3 i).
Proof. intros i v [_ H]; exact H. Qed.

(* For any x-target v in [xl,xu] and vz>0, vy = tymin-numerator(v,vz) lies in the
   band and has quotient exactly v. *)
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
  unfold sle3; cbn [sx3 sy3 sz3].
  split; [ | split ].
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
    unfold ile3. cbn [lo3 hi3]. split.
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
    split.
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
    split.
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

Definition fyminZ (xl : Zinf) (vz : Z) : Zinf :=
  match xl with Fin a => Fin (a * vz) | Ninf => Ninf | Pinf => Pinf end.
Definition fymaxZ (xu : Zinf) (vz : Z) : Zinf :=
  match xu with Fin b => Fin ((b+1) * vz - 1) | Pinf => Pinf | Ninf => Ninf end.

Lemma fdiv_ge : forall xl vy vz, 1 <= vz ->
  zle (fyminZ xl vz) (Fin vy) -> zle xl (Fin (vy / vz)).
Proof.
  intros [a| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  apply F1; [lia | nia].
Qed.

Lemma fdiv_le : forall xu vy vz, 1 <= vz ->
  zle (Fin vy) (fymaxZ xu vz) -> zle (Fin (vy / vz)) xu.
Proof.
  intros [b| |] vy vz Hvz H; cbn in *; try exact I; try contradiction.
  assert (vy / vz < b + 1) by (apply Z.div_lt_upper_bound; [lia | nia]). lia.
Qed.

Lemma fband_ne : forall xl xu vz, 1 <= vz -> zle xl xu ->
  zle (fyminZ xl vz) (fymaxZ xu vz).
Proof.
  intros [a| |] [b| |] vz Hvz H; cbn in *; try exact I; try contradiction. nia.
Qed.

Lemma fyminZ_not_Pinf : forall xl vz, xl <> Pinf -> fyminZ xl vz <> Pinf.
Proof. intros [a| |] vz H; cbn; congruence. Qed.
Lemma fymaxZ_not_Ninf : forall xu vz, xu <> Ninf -> fymaxZ xu vz <> Ninf.
Proof. intros [b| |] vz H; cbn; congruence. Qed.

Lemma idivf3_mono_pos : forall n1 n2 w, zle n1 n2 -> 0 < w ->
  zle (idivf3 n1 (Fin w)) (idivf3 n2 (Fin w)).
Proof.
  intros [a| |] [b| |] w Hn Hw; cbn [idivf3] in *;
    try rewrite (proj2 (Z.ltb_lt 0 w) Hw); cbn in *;
    try exact I; try contradiction.
  apply Z.div_le_mono; lia.
Qed.

Lemma fattain_vx : forall xl xu vz v, 0 < vz -> zle xl (Fin v) -> zle (Fin v) xu ->
  zle (fyminZ xl vz) (Fin (v * vz)) /\
  zle (Fin (v * vz)) (fymaxZ xu vz) /\
  (v * vz) / vz = v.
Proof.
  intros xl xu vz v Hvz Hxl Hxu. split; [ | split ].
  - destruct xl as [a| |]; cbn in Hxl |- *; [ nia | contradiction | exact I ].
  - destruct xu as [b| |]; cbn in Hxu |- *; [ nia | exact I | contradiction ].
  - apply Z.div_mul; lia.
Qed.

Lemma fattain_vx_hi : forall xl xu vz v, 0 < vz -> zle xl (Fin v) -> zle (Fin v) xu ->
  zle (fyminZ xl vz) (Fin ((v + 1) * vz - 1)) /\
  zle (Fin ((v + 1) * vz - 1)) (fymaxZ xu vz) /\
  ((v + 1) * vz - 1) / vz = v.
Proof.
  intros xl xu vz v Hvz Hxl Hxu. split; [ | split ].
  - destruct xl as [a| |]; cbn in Hxl |- *; [ nia | contradiction | exact I ].
  - destruct xu as [b| |]; cbn in Hxu |- *; [ nia | exact I | contradiction ].
  - replace ((v + 1) * vz - 1) with (v * vz + (vz - 1)) by ring.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (vz - 1) vz) by lia. lia.
Qed.

Lemma fwit_in_t : forall s t vz vy,
  slice_contains sol s t -> 1 <= vz -> mem3 (sz3 s) vz -> mem3 (sy3 s) vy ->
  zle (fyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (fymaxZ (hi3 (sx3 s)) vz) ->
  mem3 (sx3 t) (vy / vz) /\ mem3 (sy3 t) vy /\ mem3 (sz3 t) vz.
Proof.
  intros s t vz vy Hct Hvz1 Hmz Hmy Hb1 Hb2.
  assert (Hin : in_store3 s (vy / vz) vy vz).
  { split; [ split | split; [exact Hmy | exact Hmz]].
    - apply fdiv_ge; [exact Hvz1 | exact Hb1].
    - apply fdiv_le; [exact Hvz1 | exact Hb2]. }
  assert (Hsol : sol (vy / vz) vy vz) by (split; [lia | reflexivity]).
  exact (Hct _ _ _ Hin Hsol Hvz1).
Qed.

Lemma flo_z1band_neg : forall yu vz a, a < 0 -> yu <> Ninf ->
  zle (idivc3 yu (Fin a)) (Fin vz) -> zle (Fin (a * vz)) yu.
Proof.
  intros yu vz a Ha Hyn H.
  destruct yu as [u| |]; try congruence.
  - cbn [idivc3] in H. cbn in H. cbn. apply RC1; [lia | exact H].
  - cbn. exact I.
Qed.

Lemma flo_z2band_neg : forall yl vz b, b < -1 -> yl <> Pinf ->
  zle (Fin vz) (idivf3 (sadd3 yl 1) (sadd3 (Fin b) 1)) ->
  zle yl (Fin ((b + 1) * vz - 1)).
Proof.
  intros yl vz b Hb Hyp H. cbn [sadd3] in H.
  destruct yl as [l| |]; try congruence.
  - cbn [sadd3 idivf3] in H. cbn in H.
    assert (Hle : l + 1 <= (b + 1) * vz) by (apply mul_ge_div_neg; [lia | exact H]).
    cbn. lia.
  - cbn. exact I.
Qed.

Lemma flo_z1_lo : forall s z0,
  zle (lo3 z0) (lo3 (if zpos (lo3 (sx3 s))
        then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (hi3 (sy3 s)) (lo3 (sx3 s))))
        else if negb (ziszero (lo3 (sx3 s)))
             then Itv3 (zmax (lo3 z0) (idivc3 (hi3 (sy3 s)) (lo3 (sx3 s)))) (hi3 z0)
             else if zneg (hi3 (sy3 s)) then botitv3 else z0)).
Proof.
  intros s z0.
  destruct (zpos (lo3 (sx3 s))); [cbn [lo3]; apply zle_refl | ].
  destruct (ziszero (lo3 (sx3 s))); cbn [negb].
  - destruct (zneg (hi3 (sy3 s))); [cbn; apply zle_Pinf | cbn [lo3]; apply zle_refl].
  - cbn [lo3]; apply zle_zmax_l.
Qed.

Lemma flo_z1_hi : forall s z0,
  zle (hi3 (if zpos (lo3 (sx3 s))
        then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (hi3 (sy3 s)) (lo3 (sx3 s))))
        else if negb (ziszero (lo3 (sx3 s)))
             then Itv3 (zmax (lo3 z0) (idivc3 (hi3 (sy3 s)) (lo3 (sx3 s)))) (hi3 z0)
             else if zneg (hi3 (sy3 s)) then botitv3 else z0)) (hi3 z0).
Proof.
  intros s z0.
  destruct (zpos (lo3 (sx3 s))); [cbn [hi3]; apply zmin_zle_l | ].
  destruct (ziszero (lo3 (sx3 s))); cbn [negb].
  - destruct (zneg (hi3 (sy3 s))); [cbn | cbn [hi3]; apply zle_refl].
    destruct (hi3 z0); exact I.
  - cbn [hi3]; apply zle_refl.
Qed.

Lemma flo_z2_lo : forall s z0,
  zle (lo3 z0) (lo3 (if zge0 (hi3 (sx3 s))
        then Itv3 (zmax (lo3 z0) (idivc3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1))) (hi3 z0)
        else if negb (zeqm1 (hi3 (sx3 s)))
             then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1)))
             else if zge0 (lo3 (sy3 s)) then botitv3 else z0)).
Proof.
  intros s z0.
  destruct (zge0 (hi3 (sx3 s))); [cbn [lo3]; apply zle_zmax_l | ].
  destruct (zeqm1 (hi3 (sx3 s))); cbn [negb].
  - destruct (zge0 (lo3 (sy3 s))); [cbn; apply zle_Pinf | cbn [lo3]; apply zle_refl].
  - cbn [lo3]; apply zle_refl.
Qed.

Lemma flo_z2_hi : forall s z0,
  zle (hi3 (if zge0 (hi3 (sx3 s))
        then Itv3 (zmax (lo3 z0) (idivc3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1))) (hi3 z0)
        else if negb (zeqm1 (hi3 (sx3 s)))
             then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1)))
             else if zge0 (lo3 (sy3 s)) then botitv3 else z0)) (hi3 z0).
Proof.
  intros s z0.
  destruct (zge0 (hi3 (sx3 s))); [cbn [hi3]; apply zle_refl | ].
  destruct (zeqm1 (hi3 (sx3 s))); cbn [negb].
  - destruct (zge0 (lo3 (sy3 s))); [cbn | cbn [hi3]; apply zle_refl].
    destruct (hi3 z0); exact I.
  - cbn [hi3]; apply zmin_zle_l.
Qed.

Lemma flo_ycorner_lo : forall xl zl zu vz,
  zle (Fin 1) zl -> zle zl (Fin vz) -> zle (Fin vz) zu ->
  zle (zmin (imul3 xl zl) (imul3 xl zu)) (fyminZ xl vz).
Proof.
  intros xl zl zu vz Hz1 Hzl Hzu.
  destruct xl as [a| |]; cbn [fyminZ]; [ | apply zle_Pinf | ].
  - destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
    + eapply zle_trans; [apply zmin_zle_l | ]. cbn [imul3]. cbn. nia.
    + eapply zle_trans; [apply zmin_zle_r | ].
      destruct zu as [u| |]; cbn in Hzu; try contradiction.
      * cbn [imul3]. cbn. nia.
      * rewrite imul3_fn by lia. exact I.
  - destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    eapply zle_trans; [apply zmin_zle_l | ]. rewrite imul3_ninf_fp by lia. exact I.
Qed.

Lemma flo_ycorner_hi : forall xu zl zu vz,
  zle (Fin 1) zl -> zle zl (Fin vz) -> zle (Fin vz) zu ->
  zle (fymaxZ xu vz) (zmax (sadd3 (imul3 (sadd3 xu 1) zl) (-1))
                          (sadd3 (imul3 (sadd3 xu 1) zu) (-1))).
Proof.
  intros xu zl zu vz Hz1 Hzl Hzu.
  destruct xu as [b| |]; cbn [fymaxZ].
  - cbn [sadd3]. destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    destruct (Z.lt_trichotomy (b+1) 0) as [Hb|[Hb|Hb]].
    + eapply zle_trans; [ | apply zle_zmax_l ]. cbn [imul3 sadd3]. cbn. nia.
    + eapply zle_trans; [ | apply zle_zmax_l ]. rewrite Hb. cbn [imul3 sadd3]. cbn. nia.
    + eapply zle_trans; [ | apply zle_zmax_r ].
      destruct zu as [u| |]; cbn in Hzu; try contradiction.
      * cbn [imul3 sadd3]. cbn. nia.
      * rewrite imul3_fp by lia. exact I.
  - cbn [sadd3]. destruct zl as [l| |]; cbn in Hz1, Hzl; try contradiction.
    eapply zle_trans; [ | apply zle_zmax_l ].
    rewrite imul3_pinf_fp by lia. exact I.
  - exact I.
Qed.

Lemma idivf3_mono_num_pinf : forall n1 n2, zle n1 n2 -> zle (idivf3 n1 Pinf) (idivf3 n2 Pinf).
Proof.
  intros [a| |] [b| |] Hn; cbn in Hn |- *; try contradiction; try exact I;
    try (destruct (Z.ltb_spec a 0)); try (destruct (Z.ltb_spec b 0)); cbn; lia.
Qed.

Lemma flo_Hband : forall s z0 z1 z2,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  z1 = (if zpos (lo3 (sx3 s)) then Itv3 (lo3 z0) (zmin (hi3 z0) (idivf3 (hi3 (sy3 s)) (lo3 (sx3 s))))
        else if negb (ziszero (lo3 (sx3 s)))
             then Itv3 (zmax (lo3 z0) (idivc3 (hi3 (sy3 s)) (lo3 (sx3 s)))) (hi3 z0)
             else if zneg (hi3 (sy3 s)) then botitv3 else z0) ->
  z2 = (if zge0 (hi3 (sx3 s)) then Itv3 (zmax (lo3 z1) (idivc3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1))) (hi3 z1)
        else if negb (zeqm1 (hi3 (sx3 s)))
             then Itv3 (lo3 z1) (zmin (hi3 z1) (idivf3 (sadd3 (lo3 (sy3 s)) 1) (sadd3 (hi3 (sx3 s)) 1)))
             else if zge0 (lo3 (sy3 s)) then botitv3 else z1) ->
  nonempty3b z2 = true ->
  forall vz, 1 <= vz -> zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
  zle (fyminZ (lo3 (sx3 s)) vz) (hi3 (sy3 s)) /\ zle (lo3 (sy3 s)) (fymaxZ (hi3 (sx3 s)) vz).
Proof.
  intros s z0 z1 z2 Hx Hy Hz1 Hz2 E2 vz Hvz1 Hvlo Hvhi.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  assert (Hlo12 : zle (lo3 z1) (lo3 z2)) by (rewrite Hz2; apply (flo_z2_lo s z1)).
  assert (Hhi12 : zle (hi3 z2) (hi3 z1)) by (rewrite Hz2; apply (flo_z2_hi s z1)).
  split.
  - destruct (lo3 (sx3 s)) as [a| |] eqn:Exl; [ | congruence | ].
    2:{ cbn [fyminZ]. destruct (hi3 (sy3 s)); exact I. }
    cbn [fyminZ].
    destruct (Z.lt_trichotomy a 0) as [Ha|[Ha|Ha]].
    + assert (Hzp : zpos (Fin a) = false) by (cbn; apply Z.ltb_ge; lia).
      assert (Hzz : ziszero (Fin a) = false) by (cbn; apply Z.eqb_neq; lia).
      rewrite Hzp, Hzz in Hz1. cbn [negb] in Hz1.
      apply (flo_z1band_neg (hi3 (sy3 s)) vz a Ha Hyun).
      eapply zle_trans; [ | eapply zle_trans; [exact Hlo12 | exact Hvlo] ].
      rewrite Hz1; cbn [lo3]. apply zle_zmax_r.
    + subst a. assert (Hzp : zpos (Fin 0) = false) by reflexivity.
      assert (Hzz : ziszero (Fin 0) = true) by reflexivity.
      rewrite Hzp, Hzz in Hz1. cbn [negb] in Hz1.
      destruct (zneg (hi3 (sy3 s))) eqn:Eyn.
      * rewrite Hz1 in Hlo12. cbn [lo3] in Hlo12.
        destruct (lo3 z2) as [m| |] eqn:Em; cbn in Hlo12; try contradiction; congruence.
      * destruct (hi3 (sy3 s)) as [u| |] eqn:Ey; cbn in Eyn |- *.
        -- apply Z.ltb_ge in Eyn. lia.
        -- exact I.
        -- congruence.
    + assert (Hzp : zpos (Fin a) = true) by (cbn; apply Z.ltb_lt; lia).
      rewrite Hzp in Hz1.
      apply (z1band_pos (hi3 (sy3 s)) vz a Ha Hyun).
      eapply zle_trans; [exact Hvhi | ]. eapply zle_trans; [exact Hhi12 | ].
      rewrite Hz1; cbn [hi3]. apply zmin_zle_r.
  - destruct (hi3 (sx3 s)) as [b| |] eqn:Exu; [ | | congruence ].
    2:{ cbn [fymaxZ]. destruct (lo3 (sy3 s)); exact I. }
    cbn [fymaxZ].
    destruct (Z.lt_trichotomy b (-1)) as [Hb|[Hb|Hb]].
    + assert (Hzg : zge0 (Fin b) = false) by (cbn; apply Z.leb_gt; lia).
      assert (Hze : zeqm1 (Fin b) = false) by (cbn; apply Z.eqb_neq; lia).
      rewrite Hzg, Hze in Hz2. cbn [negb] in Hz2.
      apply (flo_z2band_neg (lo3 (sy3 s)) vz b Hb Hylp).
      eapply zle_trans; [exact Hvhi | ].
      rewrite Hz2; cbn [hi3]. apply zmin_zle_r.
    + subst b. assert (Hzg : zge0 (Fin (-1)) = false) by reflexivity.
      assert (Hze : zeqm1 (Fin (-1)) = true) by reflexivity.
      rewrite Hzg, Hze in Hz2. cbn [negb] in Hz2.
      destruct (zge0 (lo3 (sy3 s))) eqn:Eyl.
      * exfalso. rewrite Hz2 in E2. discriminate.
      * destruct (lo3 (sy3 s)) as [l| |] eqn:Ey; cbn in Eyl |- *.
        -- apply Z.leb_gt in Eyl. lia.
        -- congruence.
        -- exact I.
    + assert (Hzg : zge0 (Fin b) = true) by (cbn; apply Z.leb_le; lia).
      rewrite Hzg in Hz2.
      apply (z2band_pos (lo3 (sy3 s)) vz b ltac:(lia) Hylp).
      eapply zle_trans; [ | exact Hvlo ].
      rewrite Hz2; cbn [lo3]. apply zle_zmax_r.
Qed.

Lemma zfpos3_band : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (zfdiv_pos3 s) = true ->
  exists vz, 1 <= vz /\ mem3 (sz3 s) vz
    /\ zle (fyminZ (lo3 (sx3 s)) vz) (hi3 (sy3 s))
    /\ zle (lo3 (sy3 s)) (fymaxZ (hi3 (sx3 s)) vz).
Proof.
  intros s Hx Hy Hne.
  unfold zfdiv_pos3 in Hne; cbv zeta in Hne.
  match type of Hne with context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : zle (Fin 1) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_r).
  assert (Hz0hi : hi3 z0 = hi3 (sz3 s)) by (rewrite Hz0; cbn [hi3]; reflexivity).
  assert (Hz0lo : zle (lo3 (sz3 s)) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_l).
  destruct (nonempty3b z0) eqn:E0; cbn [negb] in Hne;
    [ | unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne;
        rewrite E0, !andb_false_r in Hne; discriminate ].
  match type of Hne with context[if zpos (lo3 (sx3 s)) then ?A else ?B] =>
    remember (if zpos (lo3 (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : zle (Fin 1) (lo3 z1)) by (rewrite Hz1; apply flo_z1_pos; exact Hz0l1).
  assert (Hlo01 : zle (lo3 z0) (lo3 z1)) by (rewrite Hz1; apply (flo_z1_lo s z0)).
  assert (Hhi01 : zle (hi3 z1) (hi3 z0)) by (rewrite Hz1; apply (flo_z1_hi s z0)).
  match type of Hne with context[if zge0 (hi3 (sx3 s)) then ?A else ?B] =>
    remember (if zge0 (hi3 (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : zle (Fin 1) (lo3 z2)) by (rewrite Hz2; apply flo_z2_pos; exact Hz1l1).
  assert (Hlo12 : zle (lo3 z1) (lo3 z2)) by (rewrite Hz2; apply (flo_z2_lo s z1)).
  assert (Hhi12 : zle (hi3 z2) (hi3 z1)) by (rewrite Hz2; apply (flo_z2_hi s z1)).
  destruct (nonempty3b z2) eqn:E2; cbn [negb] in Hne;
    [ | unfold ne_store3 in Hne; cbn [sx3 sy3 sz3] in Hne;
        rewrite E2, !andb_false_r in Hne; discriminate ].
  clear Hne.
  pose proof (nonempty_bounds _ E2) as [Hz2lp Hz2un].
  pose proof (ne_zle _ E2) as Hz2ne.
  destruct (fin_of_ge1 (lo3 z2) Hz2l1 Hz2lp) as [zv [Ez2lo Hvz1]].
  exists zv. split; [exact Hvz1 | ].
  assert (Hzvhi : zle (Fin zv) (hi3 (sz3 s))).
  { rewrite <- Hz0hi. eapply zle_trans; [ | exact Hhi01].
    eapply zle_trans; [ | exact Hhi12]. rewrite <- Ez2lo. exact Hz2ne. }
  assert (Hzvlo : zle (lo3 (sz3 s)) (Fin zv)).
  { rewrite <- Ez2lo. eapply zle_trans; [exact Hz0lo | ].
    eapply zle_trans; [exact Hlo01 | exact Hlo12]. }
  split; [ split; [exact Hzvlo | exact Hzvhi] | ].
  assert (Hzvlo2 : zle (lo3 z2) (Fin zv)) by (rewrite Ez2lo; apply zle_refl).
  assert (Hzvhi2 : zle (Fin zv) (hi3 z2)) by (rewrite <- Ez2lo; exact Hz2ne).
  apply (flo_Hband s z0 z1 z2 Hx Hy Hz1 Hz2 E2 zv Hvz1 Hzvlo2 Hzvhi2).
Qed.

Theorem fpos_ne_feasible : forall s,
  nonempty3b (sx3 s) = true -> nonempty3b (sy3 s) = true ->
  ne_store3 (zfdiv_pos3 s) = true -> slice_feasible sol s.
Proof.
  intros s Hx Hy Hne.
  destruct (zfpos3_band s Hx Hy Hne) as [vz [Hvz1 [Hmz [Hb1 Hb2]]]].
  pose proof (ne_zle _ Hx) as Hxle.
  pose proof (ne_zle _ Hy) as Hyle.
  pose proof (fband_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz Hvz1 Hxle) as Hbn.
  pose proof (nonempty_bounds _ Hx) as [Hxlp Hxun].
  pose proof (nonempty_bounds _ Hy) as [Hylp Hyun].
  set (L := zmax (fyminZ (lo3 (sx3 s)) vz) (lo3 (sy3 s))).
  set (U := zmin (fymaxZ (hi3 (sx3 s)) vz) (hi3 (sy3 s))).
  assert (HLU : zle L U).
  { unfold L, U. apply zle_zmin_glb.
    - apply zmax_lub; [exact Hbn | exact Hb2].
    - apply zmax_lub; [exact Hb1 | exact Hyle]. }
  assert (HLp : L <> Pinf)
    by (unfold L; apply zmax_not_Pinf; [apply fyminZ_not_Pinf; exact Hxlp | exact Hylp]).
  assert (HUn : U <> Ninf)
    by (unfold U; apply zmin_not_Ninf; [apply fymaxZ_not_Ninf; exact Hxun | exact Hyun]).
  destruct (pickf_mem L U HLU HLp HUn) as [HLvy HvyU].
  unfold L in HLvy. unfold U in HvyU.
  set (vy := pickf L U) in *.
  exists (vy / vz), vy, vz.
  split.
  - split; [ | split ].
    + split.
      * apply fdiv_ge; [exact Hvz1 | eapply zle_trans; [apply zle_zmax_l | exact HLvy]].
      * apply fdiv_le; [exact Hvz1 | eapply zle_trans; [exact HvyU | apply zmin_zle_l]].
    + split.
      * eapply zle_trans; [apply zle_zmax_r | exact HLvy].
      * eapply zle_trans; [exact HvyU | apply zmin_zle_r].
    + exact Hmz.
  - split; [ split; [lia | reflexivity] | exact Hvz1 ].
Qed.

Theorem fpos_best : forall s, slice_feasible sol s ->
  forall t, slice_contains sol s t -> sle3 (zfdiv_pos3 s) t.
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
  pose proof (ne_zle _ Hx) as Hxle.
  pose proof (ne_zle _ Hy) as Hyle.
  unfold zfdiv_pos3 in HneO |- *; cbv zeta in HneO |- *.
  match goal with |- context[nonempty3b ?Z] => remember Z as z0 eqn:Hz0 end.
  assert (Hz0l1 : zle (Fin 1) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_r).
  assert (Hz0hi : hi3 z0 = hi3 (sz3 s)) by (rewrite Hz0; cbn [hi3]; reflexivity).
  assert (Hz0lo : zle (lo3 (sz3 s)) (lo3 z0)) by (rewrite Hz0; cbn [lo3]; apply zle_zmax_l).
  destruct (nonempty3b z0) eqn:E0; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite E0, !andb_false_r in HneO; discriminate ].
  match goal with |- context[if zpos (lo3 (sx3 s)) then ?A else ?B] =>
    remember (if zpos (lo3 (sx3 s)) then A else B) as z1 eqn:Hz1 end.
  assert (Hz1l1 : zle (Fin 1) (lo3 z1)) by (rewrite Hz1; apply flo_z1_pos; exact Hz0l1).
  assert (Hlo01 : zle (lo3 z0) (lo3 z1)) by (rewrite Hz1; apply (flo_z1_lo s z0)).
  assert (Hhi01 : zle (hi3 z1) (hi3 z0)) by (rewrite Hz1; apply (flo_z1_hi s z0)).
  match goal with |- context[if zge0 (hi3 (sx3 s)) then ?A else ?B] =>
    remember (if zge0 (hi3 (sx3 s)) then A else B) as z2 eqn:Hz2 end.
  assert (Hz2l1 : zle (Fin 1) (lo3 z2)) by (rewrite Hz2; apply flo_z2_pos; exact Hz1l1).
  assert (Hlo12 : zle (lo3 z1) (lo3 z2)) by (rewrite Hz2; apply (flo_z2_lo s z1)).
  assert (Hhi12 : zle (hi3 z2) (hi3 z1)) by (rewrite Hz2; apply (flo_z2_hi s z1)).
  destruct (nonempty3b z2) eqn:E2; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite E2, !andb_false_r in HneO; discriminate ].
  match goal with |- context[nonempty3b ?Y] => remember Y as yF eqn:HyF end.
  destruct (nonempty3b yF) eqn:EY; cbn [negb] in HneO |- *;
    [ | unfold ne_store3 in HneO; cbn [sx3 sy3 sz3] in HneO;
        rewrite EY, !andb_false_r in HneO; discriminate ].
  assert (Hv1 : forall vz, zle (lo3 z2) (Fin vz) -> 1 <= vz).
  { intros vz Hvlo. assert (HH : zle (Fin 1) (Fin vz)) by (eapply zle_trans; [exact Hz2l1 | exact Hvlo]).
    cbn in HH. lia. }
  assert (Hband : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    zle (fyminZ (lo3 (sx3 s)) vz) (hi3 (sy3 s)) /\ zle (lo3 (sy3 s)) (fymaxZ (hi3 (sx3 s)) vz)).
  { intros vz Hvlo Hvhi. apply (flo_Hband s z0 z1 z2 Hx Hy Hz1 Hz2 E2 vz (Hv1 vz Hvlo) Hvlo Hvhi). }
  assert (Hmemz : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) -> mem3 (sz3 s) vz).
  { intros vz Hvlo Hvhi. unfold mem3. split.
    - eapply zle_trans; [exact Hz0lo | ]. eapply zle_trans; [exact Hlo01 | ].
      eapply zle_trans; [exact Hlo12 | exact Hvlo].
    - rewrite <- Hz0hi. eapply zle_trans; [exact Hvhi | ].
      eapply zle_trans; [exact Hhi12 | exact Hhi01]. }
  assert (Hwit : forall vz vy, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    mem3 (sy3 s) vy -> zle (fyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (fymaxZ (hi3 (sx3 s)) vz) ->
    mem3 (sx3 t) (vy / vz) /\ mem3 (sy3 t) vy /\ mem3 (sz3 t) vz).
  { intros vz vy Hvlo Hvhi Hmy Hby1 Hby2.
    apply (fwit_in_t s t vz vy Hct (Hv1 vz Hvlo) (Hmemz vz Hvlo Hvhi) Hmy Hby1 Hby2). }
  assert (Hpickvy : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    exists vy, mem3 (sy3 s) vy /\ zle (fyminZ (lo3 (sx3 s)) vz) (Fin vy) /\ zle (Fin vy) (fymaxZ (hi3 (sx3 s)) vz)).
  { intros vz Hvlo Hvhi.
    destruct (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (fband_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    set (L := zmax (fyminZ (lo3 (sx3 s)) vz) (lo3 (sy3 s))).
    set (U := zmin (fymaxZ (hi3 (sx3 s)) vz) (hi3 (sy3 s))).
    assert (HLU : zle L U).
    { unfold L, U. apply zle_zmin_glb.
      - apply zmax_lub; [exact Hbn | exact Hb2].
      - apply zmax_lub; [exact Hb1 | exact Hyle]. }
    assert (HLp : L <> Pinf) by (unfold L; apply zmax_not_Pinf; [apply fyminZ_not_Pinf; exact Hxlp | exact Hylp]).
    assert (HUn : U <> Ninf) by (unfold U; apply zmin_not_Ninf; [apply fymaxZ_not_Ninf; exact Hxun | exact Hyun]).
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
    zle (fyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (fymaxZ (hi3 (sx3 s)) vz) ->
    zle (lo3 (sy3 t)) (Fin vy) /\ zle (Fin vy) (hi3 (sy3 t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (_ & Hmyt & _).
    split; [apply (mem3_lo _ _ Hmyt) | apply (mem3_hi _ _ Hmyt)]. }
  assert (Hattx : forall vz vy, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    zle (lo3 (sy3 s)) (Fin vy) -> zle (Fin vy) (hi3 (sy3 s)) ->
    zle (fyminZ (lo3 (sx3 s)) vz) (Fin vy) -> zle (Fin vy) (fymaxZ (hi3 (sx3 s)) vz) ->
    zle (lo3 (sx3 t)) (Fin (vy / vz)) /\ zle (Fin (vy / vz)) (hi3 (sx3 t))).
  { intros vz vy A1 A2 A3 A4 A5 A6.
    destruct (Hwit vz vy A1 A2 (conj A3 A4) A5 A6) as (Hmxt & _ & _).
    split; [apply (mem3_lo _ _ Hmxt) | apply (mem3_hi _ _ Hmxt)]. }
  pose proof (ne_zle _ EY) as Hyfne.
  assert (Hyfyl : zle (lo3 (sy3 s)) (lo3 yF)) by (rewrite HyF; cbn [lo3]; apply zle_zmax_l).
  assert (Hyfyh : zle (hi3 yF) (hi3 (sy3 s))) by (rewrite HyF; cbn [hi3]; apply zmin_zle_l).
  assert (Hyflo_hi : zle (lo3 yF) (hi3 (sy3 s))) by (eapply zle_trans; [exact Hyfne | exact Hyfyh]).
  assert (Hyfhi_lo : zle (lo3 (sy3 s)) (hi3 yF)) by (eapply zle_trans; [exact Hyfyl | exact Hyfne]).
  unfold sle3; cbn [sx3 sy3 sz3].
  split; [ | split ].
  assert (Hlyf : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    zle (lo3 yF) (fymaxZ (hi3 (sx3 s)) vz)).
  { intros vz Hvlo Hvhi.
    pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (fband_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    rewrite HyF; cbn [lo3]. apply zmax_lub; [exact Hb2 | ].
    eapply zle_trans; [ | exact Hbn ].
    apply (flo_ycorner_lo (lo3 (sx3 s)) (lo3 z2) (hi3 z2) vz Hz2l1 Hvlo Hvhi). }
  assert (Hhyf : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
    zle (fyminZ (lo3 (sx3 s)) vz) (hi3 yF)).
  { intros vz Hvlo Hvhi.
    pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
    pose proof (fband_ne (lo3 (sx3 s)) (hi3 (sx3 s)) vz (Hv1 vz Hvlo) Hxle) as Hbn.
    rewrite HyF; cbn [hi3]. apply zle_zmin_glb; [exact Hb1 | ].
    eapply zle_trans; [ exact Hbn | ].
    apply (flo_ycorner_hi (hi3 (sx3 s)) (lo3 z2) (hi3 z2) vz Hz2l1 Hvlo Hvhi). }
  assert (Hbf : forall X a, zleb (Fin a) X = false -> zle X (Fin (a - 1))).
  { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | discriminate | exact I ]. }
  unfold ile3. cbn [lo3 hi3]. split.
  { assert (Hcx : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
      forall ylv, lo3 yF = Fin ylv -> zle (lo3 (sx3 s)) (Fin (ylv / vz)) ->
      zle (lo3 (sx3 t)) (Fin (ylv / vz))).
    { intros vz Hvlo Hvhi ylv Eyl Hxc.
      assert (Hbl : zle (fyminZ (lo3 (sx3 s)) vz) (Fin ylv)).
      { destruct (lo3 (sx3 s)) as [a| |] eqn:Exl; cbn [fyminZ].
        - cbn in Hxc. cbn. apply (floor_lb a ylv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
        - cbn in Hxc. contradiction.
        - exact I. }
      assert (Hbu : zle (Fin ylv) (fymaxZ (hi3 (sx3 s)) vz)) by (rewrite <- Eyl; apply (Hlyf vz Hvlo Hvhi)).
      assert (Hy1 : zle (lo3 (sy3 s)) (Fin ylv)) by (rewrite <- Eyl; exact Hyfyl).
      assert (Hy2 : zle (Fin ylv) (hi3 (sy3 s))) by (rewrite <- Eyl; exact Hyflo_hi).
      destruct (Hattx vz ylv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [HH _]. exact HH. }
    destruct (zleb (lo3 (sx3 s)) (zmin (zmin (idivf3 (lo3 yF) (lo3 z2)) (idivf3 (lo3 yF) (hi3 z2)))
       (zmin (idivf3 (hi3 yF) (lo3 z2)) (idivf3 (hi3 yF) (hi3 z2))))) eqn:Hclip.
    - apply zleb_zle in Hclip.
      eapply zle_trans; [ | apply zle_zmax_r ].
      destruct (lo3 yF) as [ylv| |] eqn:Eyl.
      + assert (Hcll : zle (lo3 (sx3 s)) (idivf3 (Fin ylv) (lo3 z2))).
        { eapply zle_trans; [exact Hclip | ]. eapply zle_trans; [apply zmin_zle_l | apply zmin_zle_l]. }
        assert (Hclh : zle (lo3 (sx3 s)) (idivf3 (Fin ylv) (hi3 z2))).
        { eapply zle_trans; [exact Hclip | ]. eapply zle_trans; [apply zmin_zle_l | apply zmin_zle_r]. }
        assert (HA : zle (lo3 (sx3 t)) (zmin (idivf3 (Fin ylv) (lo3 z2)) (idivf3 (Fin ylv) (hi3 z2)))).
        { apply zle_zmin_glb.
          - rewrite Hzlo2 in Hcll |- *. cbn [idivf3] in Hcll |- *. apply (Hcx zlo2 Hzlo2lo Hzlo2hi ylv eq_refl Hcll).
          - destruct (hi3 z2) as [zh| |] eqn:Eh.
            + cbn [idivf3] in Hclh |- *. apply (Hcx zh Hz2ne (zle_refl _) ylv eq_refl Hclh).
            + cbn [idivf3] in Hclh |- *.
              assert (Hq0 : ylv / (Z.max zlo2 (Z.abs ylv + 1)) = (if ylv <? 0 then -1 else 0)).
              { destruct (Z.ltb_spec ylv 0) as [Hn|Hp].
                - assert (HL0 : 0 < Z.max zlo2 (Z.abs ylv + 1)) by lia.
                  assert (ylv / (Z.max zlo2 (Z.abs ylv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                  assert (-1 <= ylv / (Z.max zlo2 (Z.abs ylv + 1))) by (apply Z.div_le_lower_bound; lia).
                  lia.
                - apply Z.div_small. lia. }
              rewrite <- Hq0. apply (Hcx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _) ylv eq_refl).
              rewrite Hq0. exact Hclh.
            + congruence. }
        apply zle_zmin_glb; [exact HA | ].
        eapply zle_trans; [exact HA | ].
        apply zle_zmin_glb.
        * eapply zle_trans; [apply zmin_zle_l | rewrite Hzlo2; apply idivf3_mono_pos; [exact Hyfne | lia] ].
        * eapply zle_trans; [apply zmin_zle_r | ].
          destruct (hi3 z2) as [zh| |] eqn:Eh.
          { apply idivf3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia]. }
          { destruct (hi3 yF) as [yhv| |] eqn:Eyh; cbn in Hyfne.
            - cbn [idivf3]. destruct (Z.ltb_spec ylv 0); destruct (Z.ltb_spec yhv 0); cbn; lia.
            - cbn [idivf3]. destruct (ylv <? 0); cbn; lia.
            - contradiction. }
          { congruence. }
      + pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
      + assert (En : idivf3 Ninf (Fin zlo2) = Ninf) by (cbn [idivf3]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
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
        assert (Hbl : zle (fyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (rewrite Hxn; cbn; exact I).
        assert (Hbu : zle (Fin vy) (fymaxZ (hi3 (sx3 s)) zlo2)) by (eapply zle_trans; [ | exact Hby2]; cbn; unfold vy; lia).
        destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
        pose proof (mem3_lo (sx3 t) _ Hmxt) as HH. rewrite EtL in HH. cbn in HH.
        assert (Hqle : vy / zlo2 <= ((M-1) * zlo2) / zlo2) by (apply Z.div_le_mono; [lia | unfold vy; lia]).
        rewrite Z.div_mul in Hqle by lia. lia.
    - eapply zle_trans; [ | apply zle_zmax_l ].
      destruct (lo3 (sx3 s)) as [xl| |] eqn:Exl; [ | congruence | cbn [zleb] in Hclip; discriminate ].
      assert (Hclipx : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
        zle (idivf3 (lo3 yF) (Fin vz)) (Fin (xl - 1)) -> zle (lo3 (sx3 t)) (Fin xl)).
      { intros vz Hvlo Hvhi Hcorner.
        pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
        destruct (fattain_vx (Fin xl) (hi3 (sx3 s)) vz xl ltac:(pose proof (Hv1 vz Hvlo); lia) (zle_refl _) Hxle) as (Hbl & Hbu & Hqeq).
        set (vy := xl * vz) in *.
        assert (Hvyhi : zle (Fin vy) (hi3 (sy3 s))) by (unfold vy; cbn [fyminZ] in Hb1; exact Hb1).
        assert (Hvylo : zle (lo3 (sy3 s)) (Fin vy)).
        { eapply zle_trans; [exact Hyfyl | ].
          destruct (lo3 yF) as [ylv| |] eqn:Eyl.
          - cbn [idivf3] in Hcorner. cbn in Hcorner. cbn.
            destruct (Z.lt_ge_cases ylv vy) as [H|H]; [lia | exfalso].
            pose proof (Z.div_le_mono vy ylv vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
          - pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
          - exact I. }
        destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [HH _]. rewrite Hqeq in HH. exact HH. }
      destruct (zleb (Fin xl) (idivf3 (lo3 yF) (lo3 z2))) eqn:Ell.
      + destruct (hi3 z2) as [zh| |] eqn:Eh.
        * apply (Hclipx zh Hz2ne (zle_refl _)).
          destruct (zleb (Fin xl) (idivf3 (lo3 yF) (Fin zh))) eqn:Elh.
          -- exfalso. apply zleb_zle in Ell, Elh.
             assert (Hge : zle (Fin xl) (zmin (zmin (idivf3 (lo3 yF) (lo3 z2)) (idivf3 (lo3 yF) (Fin zh)))
               (zmin (idivf3 (hi3 yF) (lo3 z2)) (idivf3 (hi3 yF) (Fin zh))))).
             { apply zle_zmin_glb; apply zle_zmin_glb; try assumption.
               - eapply zle_trans; [exact Ell | rewrite Hzlo2; apply idivf3_mono_pos; [exact Hyfne | lia] ].
               - eapply zle_trans; [exact Elh | apply idivf3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia] ]. }
             apply zleb_zle in Hge. rewrite Hge in Hclip. discriminate.
          -- apply Hbf. exact Elh.
        * destruct (Z.le_gt_cases xl 0) as [Hxl0|Hxl0].
          -- exfalso. apply zleb_zle in Ell. rewrite Hzlo2 in Ell.
             assert (Hcp : forall yb, zle (Fin xl) (idivf3 yb (Fin zlo2)) -> zle (Fin xl) (idivf3 yb Pinf)).
             { intros yb Hyb. destruct yb as [v| |]; cbn [idivf3] in Hyb |- *.
               - destruct (Z.ltb_spec v 0) as [Hn|Hp]; cbn in Hyb |- *.
                 + assert (v / zlo2 < 0) by (apply Z.div_lt_upper_bound; lia). lia.
                 + lia.
               - cbn; lia.
               - rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)) in Hyb. cbn in Hyb. contradiction. }
             assert (Hge : zle (Fin xl) (zmin (zmin (idivf3 (lo3 yF) (lo3 z2)) (idivf3 (lo3 yF) Pinf))
               (zmin (idivf3 (hi3 yF) (lo3 z2)) (idivf3 (hi3 yF) Pinf)))).
             { apply zle_zmin_glb; apply zle_zmin_glb.
               - rewrite Hzlo2. exact Ell.
               - apply Hcp. exact Ell.
               - rewrite Hzlo2. eapply zle_trans; [exact Ell | apply idivf3_mono_pos; [exact Hyfne | lia] ].
               - apply Hcp. eapply zle_trans; [exact Ell | apply idivf3_mono_pos; [exact Hyfne | lia] ]. }
             apply zleb_zle in Hge. rewrite Hge in Hclip. discriminate.
          -- destruct (lo3 yF) as [ylv| |] eqn:Eyl.
             ++ apply (Hclipx (Z.max zlo2 (Z.abs ylv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                cbn [idivf3].
                assert (Hq0 : ylv / (Z.max zlo2 (Z.abs ylv + 1)) = (if ylv <? 0 then -1 else 0)).
                { destruct (Z.ltb_spec ylv 0) as [Hn|Hp].
                  - assert (HL0 : 0 < Z.max zlo2 (Z.abs ylv + 1)) by lia.
                    assert (ylv / (Z.max zlo2 (Z.abs ylv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                    assert (-1 <= ylv / (Z.max zlo2 (Z.abs ylv + 1))) by (apply Z.div_le_lower_bound; lia).
                    lia.
                  - apply Z.div_small. lia. }
                rewrite Hq0. destruct (ylv <? 0); cbn; lia.
             ++ pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
             ++ apply (Hclipx (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                cbn [idivf3]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). cbn. lia.
        * congruence.
      + apply (Hclipx zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ell. apply Hbf. exact Ell. }
  { assert (Hcxu : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
      forall yhv, hi3 yF = Fin yhv -> zle (Fin (yhv / vz)) (hi3 (sx3 s)) ->
      zle (Fin (yhv / vz)) (hi3 (sx3 t))).
    { intros vz Hvlo Hvhi yhv Eyh Hxc.
      assert (Hbu : zle (Fin yhv) (fymaxZ (hi3 (sx3 s)) vz)).
      { destruct (hi3 (sx3 s)) as [b| |] eqn:Exu; cbn [fymaxZ].
        - cbn in Hxc. cbn. apply (floor_ub b yhv vz); [pose proof (Hv1 vz Hvlo); lia | exact Hxc].
        - exact I.
        - cbn in Hxc. contradiction. }
      assert (Hbl : zle (fyminZ (lo3 (sx3 s)) vz) (Fin yhv)) by (rewrite <- Eyh; apply (Hhyf vz Hvlo Hvhi)).
      assert (Hy1 : zle (lo3 (sy3 s)) (Fin yhv)) by (rewrite <- Eyh; exact Hyfhi_lo).
      assert (Hy2 : zle (Fin yhv) (hi3 (sy3 s))) by (rewrite <- Eyh; exact Hyfyh).
      destruct (Hattx vz yhv Hvlo Hvhi Hy1 Hy2 Hbl Hbu) as [_ HH]. exact HH. }
    destruct (zleb (zmax (zmax (idivf3 (lo3 yF) (lo3 z2)) (idivf3 (lo3 yF) (hi3 z2)))
       (zmax (idivf3 (hi3 yF) (lo3 z2)) (idivf3 (hi3 yF) (hi3 z2)))) (hi3 (sx3 s))) eqn:Hclip.
    - apply zleb_zle in Hclip.
      eapply zle_trans; [ apply zmin_zle_r | ].
      destruct (hi3 yF) as [yhv| |] eqn:Eyh.
      + assert (Hchl : zle (idivf3 (Fin yhv) (lo3 z2)) (hi3 (sx3 s))).
        { eapply zle_trans; [ | exact Hclip ]. eapply zle_trans; [ | apply zle_zmax_r]. apply zle_zmax_l. }
        assert (Hchh : zle (idivf3 (Fin yhv) (hi3 z2)) (hi3 (sx3 s))).
        { eapply zle_trans; [ | exact Hclip ]. eapply zle_trans; [ | apply zle_zmax_r]. apply zle_zmax_r. }
        assert (HA : zle (zmax (idivf3 (Fin yhv) (lo3 z2)) (idivf3 (Fin yhv) (hi3 z2))) (hi3 (sx3 t))).
        { apply zmax_lub.
          - rewrite Hzlo2 in Hchl |- *. cbn [idivf3] in Hchl |- *. apply (Hcxu zlo2 Hzlo2lo Hzlo2hi yhv eq_refl Hchl).
          - destruct (hi3 z2) as [zh| |] eqn:Eh.
            + cbn [idivf3] in Hchh |- *. apply (Hcxu zh Hz2ne (zle_refl _) yhv eq_refl Hchh).
            + cbn [idivf3] in Hchh |- *.
              assert (Hq0 : yhv / (Z.max zlo2 (Z.abs yhv + 1)) = (if yhv <? 0 then -1 else 0)).
              { destruct (Z.ltb_spec yhv 0) as [Hn|Hp].
                - assert (HL0 : 0 < Z.max zlo2 (Z.abs yhv + 1)) by lia.
                  assert (yhv / (Z.max zlo2 (Z.abs yhv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                  assert (-1 <= yhv / (Z.max zlo2 (Z.abs yhv + 1))) by (apply Z.div_le_lower_bound; lia).
                  lia.
                - apply Z.div_small. lia. }
              rewrite <- Hq0. apply (Hcxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _) yhv eq_refl).
              rewrite Hq0. exact Hchh.
            + congruence. }
        apply zmax_lub; [ | exact HA ].
        eapply zle_trans; [ | exact HA ].
        apply zmax_lub.
        * eapply zle_trans; [ | apply zle_zmax_l ]. rewrite Hzlo2. apply idivf3_mono_pos; [exact Hyfne | lia].
        * eapply zle_trans; [ | apply zle_zmax_r ].
          destruct (hi3 z2) as [zh| |] eqn:Eh.
          { apply idivf3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia]. }
          { apply idivf3_mono_num_pinf. exact Hyfne. }
          { congruence. }
      + assert (Ep : idivf3 Pinf (Fin zlo2) = Pinf) by (cbn [idivf3]; rewrite (proj2 (Z.ltb_lt 0 zlo2) ltac:(lia)); reflexivity).
        assert (Hzp : forall x, zmax x Pinf = Pinf) by (intros [?| |]; reflexivity).
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
        assert (Hbl : zle (fyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (eapply zle_trans; [exact Hby1 | ]; cbn; unfold vy; lia).
        assert (Hbu : zle (Fin vy) (fymaxZ (hi3 (sx3 s)) zlo2)) by (rewrite Hxp; cbn; exact I).
        destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (Hmxt & _ & _).
        pose proof (mem3_hi (sx3 t) _ Hmxt) as HH. rewrite EtH in HH. cbn in HH.
        assert (Hqge : ((M+1) * zlo2) / zlo2 <= vy / zlo2) by (apply Z.div_le_mono; [lia | unfold vy; lia]).
        rewrite Z.div_mul in Hqge by lia. lia.
      + pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
    - eapply zle_trans; [ apply zmin_zle_l | ].
      assert (Hzlp : forall x, zleb x Pinf = true) by (intros [?| |]; reflexivity).
      destruct (hi3 (sx3 s)) as [xu| |] eqn:Exu; [ | rewrite Hzlp in Hclip; discriminate | congruence ].
      assert (Hclipxu : forall vz, zle (lo3 z2) (Fin vz) -> zle (Fin vz) (hi3 z2) ->
        zle (Fin (xu + 1)) (idivf3 (hi3 yF) (Fin vz)) -> zle (Fin xu) (hi3 (sx3 t))).
      { intros vz Hvlo Hvhi Hcorner.
        pose proof (Hband vz Hvlo Hvhi) as [Hb1 Hb2].
        destruct (fattain_vx_hi (lo3 (sx3 s)) (Fin xu) vz xu ltac:(pose proof (Hv1 vz Hvlo); lia) Hxle (zle_refl _)) as (Hbl & Hbu & Hqeq).
        set (vy := (xu + 1) * vz - 1) in *.
        assert (Hvylo : zle (lo3 (sy3 s)) (Fin vy)) by (unfold vy; cbn [fymaxZ] in Hb2; exact Hb2).
        assert (Hvyhi : zle (Fin vy) (hi3 (sy3 s))).
        { eapply zle_trans; [ | exact Hyfyh ].
          destruct (hi3 yF) as [yhv| |] eqn:Eyh.
          - cbn [idivf3] in Hcorner. cbn in Hcorner. cbn.
            destruct (Z.lt_ge_cases vy yhv) as [H|H]; [lia | exfalso].
            pose proof (Z.div_le_mono yhv vy vz ltac:(pose proof (Hv1 vz Hvlo); lia) H) as HH. rewrite Hqeq in HH. lia.
          - exact I.
          - pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
        destruct (Hattx vz vy Hvlo Hvhi Hvylo Hvyhi Hbl Hbu) as [_ HH]. rewrite Hqeq in HH. exact HH. }
      assert (Hbfu : forall X a, zleb X (Fin a) = false -> zle (Fin (a + 1)) X).
      { intros [x| |] a Hb; cbn in Hb |- *; [ apply Z.leb_gt in Hb; lia | exact I | discriminate ]. }
      destruct (zleb (idivf3 (hi3 yF) (lo3 z2)) (Fin xu)) eqn:Ehl.
      + destruct (hi3 z2) as [zh| |] eqn:Eh.
        * apply (Hclipxu zh Hz2ne (zle_refl _)).
          destruct (zleb (idivf3 (hi3 yF) (Fin zh)) (Fin xu)) eqn:Ehh.
          -- exfalso. apply zleb_zle in Ehl, Ehh.
             assert (Hle : zle (zmax (zmax (idivf3 (lo3 yF) (lo3 z2)) (idivf3 (lo3 yF) (Fin zh)))
               (zmax (idivf3 (hi3 yF) (lo3 z2)) (idivf3 (hi3 yF) (Fin zh)))) (Fin xu)).
             { apply zmax_lub; apply zmax_lub.
               - eapply zle_trans; [ | exact Ehl ]. rewrite Hzlo2. apply idivf3_mono_pos; [exact Hyfne | lia].
               - eapply zle_trans; [ | exact Ehh ]. apply idivf3_mono_pos; [exact Hyfne | pose proof Hzlo2hi as HH; cbn in HH; lia].
               - exact Ehl.
               - exact Ehh. }
             apply zleb_zle in Hle. rewrite Hle in Hclip. discriminate.
          -- apply Hbfu. exact Ehh.
        * destruct (zleb (idivf3 (hi3 yF) Pinf) (Fin xu)) eqn:Ehh.
          -- exfalso. apply zleb_zle in Ehl, Ehh.
             assert (Hle : zle (zmax (zmax (idivf3 (lo3 yF) (lo3 z2)) (idivf3 (lo3 yF) Pinf))
               (zmax (idivf3 (hi3 yF) (lo3 z2)) (idivf3 (hi3 yF) Pinf))) (Fin xu)).
             { apply zmax_lub; apply zmax_lub.
               - eapply zle_trans; [ | exact Ehl ]. rewrite Hzlo2. apply idivf3_mono_pos; [exact Hyfne | lia].
               - eapply zle_trans; [ | exact Ehh ]. apply idivf3_mono_num_pinf. exact Hyfne.
               - exact Ehl.
               - exact Ehh. }
             apply zleb_zle in Hle. rewrite Hle in Hclip. discriminate.
          -- apply Hbfu in Ehh.
             destruct (hi3 yF) as [yhv| |] eqn:Eyh.
             ++ apply (Hclipxu (Z.max zlo2 (Z.abs yhv + 1)) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                cbn [idivf3] in Ehh |- *.
                assert (Hq0 : yhv / (Z.max zlo2 (Z.abs yhv + 1)) = (if yhv <? 0 then -1 else 0)).
                { destruct (Z.ltb_spec yhv 0) as [Hn|Hp].
                  - assert (HL0 : 0 < Z.max zlo2 (Z.abs yhv + 1)) by lia.
                    assert (yhv / (Z.max zlo2 (Z.abs yhv + 1)) < 0) by (apply Z.div_lt_upper_bound; lia).
                    assert (-1 <= yhv / (Z.max zlo2 (Z.abs yhv + 1))) by (apply Z.div_le_lower_bound; lia).
                    lia.
                  - apply Z.div_small. lia. }
                rewrite Hq0. exact Ehh.
             ++ apply (Hclipxu (Z.max zlo2 1) ltac:(rewrite Hzlo2; cbn; lia) (zle_Pinf _)).
                cbn [idivf3]. rewrite (proj2 (Z.ltb_lt 0 (Z.max zlo2 1)) ltac:(lia)). exact I.
             ++ pose proof (nonempty_bounds _ EY) as [_ HH]; congruence.
        * congruence.
      + apply (Hclipxu zlo2 Hzlo2lo Hzlo2hi). rewrite Hzlo2 in Ehl. apply Hbfu. exact Ehl. }
  unfold ile3. cbn [lo3 hi3]. split.
  { destruct (lo3 yF) as [vlo| |] eqn:Eylo.
    - assert (Hex : exists vzs, zle (lo3 z2) (Fin vzs) /\ zle (Fin vzs) (hi3 z2) /\
        zle (fyminZ (lo3 (sx3 s)) vzs) (Fin vlo) /\ zle (Fin vlo) (fymaxZ (hi3 (sx3 s)) vzs)).
      { destruct (lo3 (sx3 s)) as [a| |] eqn:Exl.
        - destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
          + exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
            pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
            pose proof (fband_ne (Fin a) (hi3 (sx3 s)) zlo2 Hzlo21 Hxle) as Hbn.
            assert (Hzmin : zmin (imul3 (Fin a) (lo3 z2)) (imul3 (Fin a) (hi3 z2)) = Fin (a*zlo2)).
            { rewrite Hzlo2. destruct (hi3 z2) as [zhi2| |] eqn:Eh; [ | | congruence ].
              - cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.min_l by nia; reflexivity.
              - destruct (Z.eq_dec a 0) as [->|Han].
                + cbn. reflexivity.
                + cbn. rewrite (proj2 (Z.eqb_neq a 0) Han), (proj2 (Z.ltb_lt 0 a) ltac:(lia)). reflexivity. }
            split.
            * rewrite <- Eylo, HyF; cbn [lo3]; rewrite Hzmin; cbn [fyminZ]. apply zle_zmax_r.
            * rewrite <- Eylo, HyF; cbn [lo3]; rewrite Hzmin.
              apply zmax_lub; [exact Hb2 | ]. change (Fin (a*zlo2)) with (fyminZ (Fin a) zlo2). exact Hbn.
          + destruct (hi3 z2) as [zhi2| |] eqn:Eh.
            * exists zhi2. split; [exact Hz2ne | split; [apply zle_refl | ]].
              pose proof (Hband zhi2 Hz2ne (zle_refl _)) as [Hb1 Hb2].
              pose proof (fband_ne (Fin a) (hi3 (sx3 s)) zhi2 (Hv1 zhi2 Hz2ne) Hxle) as Hbn.
              assert (Hzmin : zmin (imul3 (Fin a) (lo3 z2)) (imul3 (Fin a) (Fin zhi2)) = Fin (a*zhi2)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.min_r by nia; reflexivity. }
              split.
              -- rewrite <- Eylo, HyF; cbn [lo3]; rewrite Hzmin; cbn [fyminZ]. apply zle_zmax_r.
              -- rewrite <- Eylo, HyF; cbn [lo3]; rewrite Hzmin.
                 apply zmax_lub; [exact Hb2 | ]. change (Fin (a*zhi2)) with (fyminZ (Fin a) zhi2). exact Hbn.
            * assert (Hlo3yf : lo3 yF = lo3 (sy3 s)).
              { rewrite HyF; cbn [lo3]; rewrite Hzlo2; rewrite imul3_fn by lia; cbn; destruct (lo3 (sy3 s)); reflexivity. }
              assert (Hyleq : lo3 (sy3 s) = Fin vlo) by (rewrite <- Hlo3yf; exact Eylo).
              set (vzs := Z.max zlo2 (Z.max 1 (1 - vlo))).
              assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
              assert (Hgev : 1 - vlo <= vzs) by (unfold vzs; lia).
              assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
              clearbody vzs.
              assert (HB1 : zle (lo3 z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
              exists vzs. split; [exact HB1 | split; [apply zle_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply zle_Pinf)) as [Hb1 Hb2].
              split.
              -- cbn [fyminZ]. cbn. nia.
              -- rewrite Hyleq in Hb2. exact Hb2.
            * congruence.
        - congruence.
        - exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          assert (Hlo3yf : lo3 yF = lo3 (sy3 s)).
          { rewrite HyF; cbn [lo3]; rewrite Hzlo2; rewrite imul3_ninf_fp by lia; cbn; destruct (lo3 (sy3 s)); reflexivity. }
          assert (Hyleq : lo3 (sy3 s) = Fin vlo) by (rewrite <- Hlo3yf; exact Eylo).
          split; [ cbn [fyminZ]; exact I | rewrite Hyleq in Hb2; exact Hb2 ]. }
      destruct Hex as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vlo A B Hyfyl Hyflo_hi C D) as [HH _]. exact HH.
    - pose proof (nonempty_bounds _ EY) as [HH _]; congruence.
    - assert (Hlo0 : lo3 (sy3 s) = Ninf) by (destruct (lo3 (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyl; contradiction).
      destruct (lo3 (sy3 t)) as [M| |] eqn:EtL; [ | | exact I ].
      2:{ exfalso. pose proof (mem3_lo (sy3 t) fy Hfty) as HH. rewrite EtL in HH. cbn in HH. exact HH. }
      exfalso.
      assert (HMfy : M <= fy) by (pose proof (mem3_lo (sy3 t) fy Hfty) as HH; rewrite EtL in HH; cbn in HH; exact HH).
      assert (Hfyhi : zle (Fin fy) (hi3 (sy3 s))) by (apply (mem3_hi _ _ Hfym)).
      destruct (lo3 (sx3 s)) as [a| |] eqn:Exl.
      + destruct (Z.le_gt_cases 0 a) as [Ha|Ha].
        * exfalso. rewrite HyF in Eylo; cbn [lo3] in Eylo; rewrite Hlo0 in Eylo.
          rewrite Hzlo2 in Eylo. destruct (hi3 z2) as [zh| |] eqn:Eh.
          -- cbn in Eylo. discriminate.
          -- destruct (Z.eq_dec a 0) as [->|Han]; cbn in Eylo; try discriminate.
             rewrite (proj2 (Z.eqb_neq a 0) Han), (proj2 (Z.ltb_lt 0 a) ltac:(lia)) in Eylo. cbn in Eylo. discriminate.
          -- congruence.
        * destruct (hi3 z2) as [zh| |] eqn:Eh.
          -- exfalso. rewrite HyF in Eylo; cbn [lo3] in Eylo; rewrite Hlo0, Hzlo2 in Eylo; cbn in Eylo; discriminate.
          -- destruct (hi3 (sy3 s)) as [hh| |] eqn:Ehy.
             ++ set (vzs := Z.max zlo2 (Z.max 1 (Z.max (1-M) (1-hh)))).
                assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
                assert (HgeM : 1 - M <= vzs) by (unfold vzs; lia).
                assert (Ggehh : 1 - hh <= vzs) by (unfold vzs; lia).
                assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
                clearbody vzs.
                assert (HB1 : zle (lo3 z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
                assert (Hmemy : mem3 (sy3 s) (a * vzs)).
                { split; [rewrite Hlo0; exact I | rewrite Ehy; cbn; nia]. }
                assert (Hbl : zle (fyminZ (Fin a) vzs) (Fin (a * vzs))) by (cbn [fyminZ]; cbn; lia).
                assert (Hbu : zle (Fin (a * vzs)) (fymaxZ (hi3 (sx3 s)) vzs)).
                { pose proof (fband_ne (Fin a) (hi3 (sx3 s)) vzs Hz1v Hxle) as Hbn.
                  assert (Efym : fyminZ (Fin a) vzs = Fin (a * vzs)) by reflexivity.
                  rewrite Efym in Hbn. exact Hbn. }
                destruct (Hwit vzs (a * vzs) HB1 (zle_Pinf _) Hmemy Hbl Hbu) as (_ & Hmyt & _).
                pose proof (mem3_lo (sy3 t) (a * vzs) Hmyt) as HH. rewrite EtL in HH. cbn in HH. nia.
             ++ set (vzs := Z.max zlo2 (Z.max 1 (1-M))).
                assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
                assert (HgeM : 1 - M <= vzs) by (unfold vzs; lia).
                assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
                clearbody vzs.
                assert (HB1 : zle (lo3 z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
                assert (Hmemy : mem3 (sy3 s) (a * vzs)).
                { split; [rewrite Hlo0; exact I | rewrite Ehy; exact I]. }
                assert (Hbl : zle (fyminZ (Fin a) vzs) (Fin (a * vzs))) by (cbn [fyminZ]; cbn; lia).
                assert (Hbu : zle (Fin (a * vzs)) (fymaxZ (hi3 (sx3 s)) vzs)).
                { pose proof (fband_ne (Fin a) (hi3 (sx3 s)) vzs Hz1v Hxle) as Hbn.
                  assert (Efym : fyminZ (Fin a) vzs = Fin (a * vzs)) by reflexivity.
                  rewrite Efym in Hbn. exact Hbn. }
                destruct (Hwit vzs (a * vzs) HB1 (zle_Pinf _) Hmemy Hbl Hbu) as (_ & Hmyt & _).
                pose proof (mem3_lo (sy3 t) (a * vzs) Hmyt) as HH. rewrite EtL in HH. cbn in HH. nia.
             ++ congruence.
          -- congruence.
      + congruence.
      + destruct (fymaxZ (hi3 (sx3 s)) zlo2) as [tm| |] eqn:Etm.
        * set (vy := Z.min (M-1) tm).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [rewrite Hlo0; exact I | eapply zle_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
          assert (Hbl : zle (fyminZ Ninf zlo2) (Fin vy)) by (cbn [fyminZ]; exact I).
          assert (Hbu : zle (Fin vy) (fymaxZ (hi3 (sx3 s)) zlo2)) by (rewrite Etm; cbn; unfold vy; lia).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
        * set (vy := M-1).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [rewrite Hlo0; exact I | eapply zle_trans'; [ | exact Hfyhi]; cbn; unfold vy; lia]. }
          assert (Hbl : zle (fyminZ Ninf zlo2) (Fin vy)) by (cbn [fyminZ]; exact I).
          assert (Hbu : zle (Fin vy) (fymaxZ (hi3 (sx3 s)) zlo2)) by (rewrite Etm; apply zle_Pinf).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_lo (sy3 t) vy Hmyt) as HH. rewrite EtL in HH. cbn in HH. unfold vy in HH. lia.
        * exfalso. apply (fymaxZ_not_Ninf (hi3 (sx3 s)) zlo2 Hxun). exact Etm. }
  { destruct (hi3 yF) as [vhi| |] eqn:Eyhi.
    - assert (Hexu : exists vzs, zle (lo3 z2) (Fin vzs) /\ zle (Fin vzs) (hi3 z2) /\
        zle (fyminZ (lo3 (sx3 s)) vzs) (Fin vhi) /\ zle (Fin vhi) (fymaxZ (hi3 (sx3 s)) vzs)).
      { destruct (hi3 (sx3 s)) as [xu| |] eqn:Exu.
        - destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
          + destruct (hi3 z2) as [zhi2| |] eqn:Eh.
            * exists zhi2. split; [exact Hz2ne | split; [apply zle_refl | ]].
              pose proof (Hband zhi2 Hz2ne (zle_refl _)) as [Hb1 Hb2].
              pose proof (fband_ne (lo3 (sx3 s)) (Fin xu) zhi2 (Hv1 zhi2 Hz2ne) Hxle) as Hbn.
              assert (Hzmax : zmax (sadd3 (imul3 (sadd3 (Fin xu) 1) (lo3 z2)) (-1)) (sadd3 (imul3 (sadd3 (Fin xu) 1) (Fin zhi2)) (-1)) = Fin ((xu+1)*zhi2-1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.max_r by nia; nia. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzmax.
                 apply zle_zmin_glb; [exact Hb1 | ]. change (Fin ((xu+1)*zhi2-1)) with (fymaxZ (Fin xu) zhi2). exact Hbn.
              -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzmax; cbn [fymaxZ]. apply zmin_zle_r.
            * assert (Hhi0 : hi3 yF = hi3 (sy3 s)).
              { rewrite HyF; cbn [hi3]; rewrite Hzlo2; cbn [sadd3]; rewrite imul3_fp by lia; cbn; destruct (hi3 (sy3 s)); reflexivity. }
              assert (Hyheq : hi3 (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
              set (vzs := Z.max zlo2 (Z.max 1 (vhi + 2))).
              assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
              assert (Hvge : vhi + 2 <= vzs) by (unfold vzs; lia).
              assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
              clearbody vzs.
              assert (HB1 : zle (lo3 z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
              exists vzs. split; [exact HB1 | split; [apply zle_Pinf | ]].
              pose proof (Hband vzs HB1 ltac:(apply zle_Pinf)) as [Hb1 Hb2].
              split.
              -- rewrite <- Hyheq. exact Hb1.
              -- cbn [fymaxZ]. cbn. nia.
            * congruence.
          + destruct (hi3 z2) as [zhi2| |] eqn:Eh.
            * exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
              pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
              pose proof (fband_ne (lo3 (sx3 s)) (Fin xu) zlo2 Hzlo21 Hxle) as Hbn.
              assert (Hzmax : zmax (sadd3 (imul3 (sadd3 (Fin xu) 1) (lo3 z2)) (-1)) (sadd3 (imul3 (sadd3 (Fin xu) 1) (Fin zhi2)) (-1)) = Fin ((xu+1)*zlo2-1)).
              { rewrite Hzlo2. cbn. f_equal. assert (zlo2 <= zhi2) by (pose proof Hzlo2hi as HH; cbn in HH; lia). rewrite Z.max_l by nia; nia. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzmax.
                 apply zle_zmin_glb; [exact Hb1 | ]. change (Fin ((xu+1)*zlo2-1)) with (fymaxZ (Fin xu) zlo2). exact Hbn.
              -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzmax; cbn [fymaxZ]. apply zmin_zle_r.
            * exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
              pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
              pose proof (fband_ne (lo3 (sx3 s)) (Fin xu) zlo2 Hzlo21 Hxle) as Hbn.
              assert (Hzmax : zmax (sadd3 (imul3 (sadd3 (Fin xu) 1) (lo3 z2)) (-1)) (sadd3 (imul3 (sadd3 (Fin xu) 1) Pinf) (-1)) = Fin ((xu+1)*zlo2-1)).
              { rewrite Hzlo2. cbn [sadd3]. destruct (Z.eq_dec (xu+1) 0) as [Hx1|Hx1].
                - rewrite Hx1. cbn. reflexivity.
                - rewrite imul3_fn by lia. cbn. reflexivity. }
              split.
              -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzmax.
                 apply zle_zmin_glb; [exact Hb1 | ]. change (Fin ((xu+1)*zlo2-1)) with (fymaxZ (Fin xu) zlo2). exact Hbn.
              -- rewrite <- Eyhi, HyF; cbn [hi3]; rewrite Hzmax; cbn [fymaxZ]. apply zmin_zle_r.
            * congruence.
        - assert (Hhi0 : hi3 yF = hi3 (sy3 s)).
          { rewrite HyF; cbn [hi3]; rewrite Hzlo2; cbn [sadd3]; rewrite imul3_pinf_fp by lia; cbn; destruct (hi3 (sy3 s)); reflexivity. }
          assert (Hyheq : hi3 (sy3 s) = Fin vhi) by (rewrite <- Hhi0; exact Eyhi).
          exists zlo2. split; [exact Hzlo2lo | split; [exact Hzlo2hi | ]].
          pose proof (Hband zlo2 Hzlo2lo Hzlo2hi) as [Hb1 Hb2].
          split.
          -- rewrite <- Hyheq. exact Hb1.
          -- cbn [fymaxZ]. apply zle_Pinf.
        - congruence. }
      destruct Hexu as [vzs [A [B [C D]]]].
      destruct (Hatt vzs vhi A B Hyfhi_lo Hyfyh C D) as [_ HH]. exact HH.
    - assert (Hhi0 : hi3 (sy3 s) = Pinf) by (destruct (hi3 (sy3 s)) eqn:E; try reflexivity; cbn in Hyfyh; contradiction).
      destruct (hi3 (sy3 t)) as [M| |] eqn:EtH; [ | exact I | ].
      2:{ exfalso. pose proof (mem3_hi (sy3 t) fy Hfty) as HH. rewrite EtH in HH. cbn in HH. exact HH. }
      exfalso.
      assert (HfyM : fy <= M) by (pose proof (mem3_hi (sy3 t) fy Hfty) as HH; rewrite EtH in HH; cbn in HH; exact HH).
      assert (Hfylo : zle (lo3 (sy3 s)) (Fin fy)) by (apply (mem3_lo _ _ Hfym)).
      destruct (hi3 (sx3 s)) as [xu| |] eqn:Exu.
      + destruct (Z.le_gt_cases 0 xu) as [Hu|Hu].
        * destruct (hi3 z2) as [zh| |] eqn:Eh.
          -- exfalso. rewrite HyF in Eyhi; cbn [hi3] in Eyhi; rewrite Hhi0, Hzlo2 in Eyhi; cbn in Eyhi; discriminate.
          -- set (vzs := Z.max zlo2 (Z.max 1 (M + 2))).
             assert (Hz1v : 1 <= vzs) by (unfold vzs; lia).
             assert (HgeM : M + 2 <= vzs) by (unfold vzs; lia).
             assert (Hzgev : zlo2 <= vzs) by (unfold vzs; lia).
             clearbody vzs.
             assert (HB1 : zle (lo3 z2) (Fin vzs)) by (rewrite Hzlo2; cbn; lia).
             assert (Hmemy : mem3 (sy3 s) ((xu+1)*vzs-1)).
             { split; [eapply zle_trans'; [exact Hfylo | ]; cbn; nia | rewrite Hhi0; exact I]. }
             assert (Hbu : zle (Fin ((xu+1)*vzs-1)) (fymaxZ (Fin xu) vzs)) by (cbn [fymaxZ]; cbn; lia).
             assert (Hbl : zle (fyminZ (lo3 (sx3 s)) vzs) (Fin ((xu+1)*vzs-1))).
             { pose proof (fband_ne (lo3 (sx3 s)) (Fin xu) vzs Hz1v Hxle) as Hbn.
               assert (Efym : fymaxZ (Fin xu) vzs = Fin ((xu+1)*vzs-1)) by reflexivity.
               rewrite Efym in Hbn. exact Hbn. }
             destruct (Hwit vzs ((xu+1)*vzs-1) HB1 (zle_Pinf _) Hmemy Hbl Hbu) as (_ & Hmyt & _).
             pose proof (mem3_hi (sy3 t) ((xu+1)*vzs-1) Hmyt) as HH. rewrite EtH in HH. cbn in HH. nia.
          -- congruence.
        * exfalso. rewrite HyF in Eyhi; cbn [hi3] in Eyhi; rewrite Hhi0, Hzlo2 in Eyhi.
          destruct (hi3 z2) as [zh| |] eqn:Eh; cbn [sadd3] in Eyhi.
          -- cbn in Eyhi. discriminate.
          -- destruct (Z.eq_dec (xu+1) 0) as [Hx1|Hx1].
             ++ rewrite Hx1 in Eyhi. cbn in Eyhi. discriminate.
             ++ rewrite imul3_fn in Eyhi by lia. cbn in Eyhi. discriminate.
          -- congruence.
      + destruct (fyminZ (lo3 (sx3 s)) zlo2) as [tmn| |] eqn:Etm.
        * set (vy := Z.max (M+1) tmn).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [eapply zle_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
          assert (Hbu : zle (Fin vy) (fymaxZ Pinf zlo2)) by (cbn [fymaxZ]; apply zle_Pinf).
          assert (Hbl : zle (fyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; unfold vy; lia).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
        * exfalso. apply (fyminZ_not_Pinf (lo3 (sx3 s)) zlo2 Hxlp). exact Etm.
        * set (vy := M+1).
          assert (Hmemy : mem3 (sy3 s) vy).
          { split; [eapply zle_trans'; [exact Hfylo | ]; cbn; unfold vy; lia | rewrite Hhi0; exact I]. }
          assert (Hbu : zle (Fin vy) (fymaxZ Pinf zlo2)) by (cbn [fymaxZ]; apply zle_Pinf).
          assert (Hbl : zle (fyminZ (lo3 (sx3 s)) zlo2) (Fin vy)) by (rewrite Etm; cbn; exact I).
          destruct (Hwit zlo2 vy Hzlo2lo Hzlo2hi Hmemy Hbl Hbu) as (_ & Hmyt & _).
          pose proof (mem3_hi (sy3 t) vy Hmyt) as HH. rewrite EtH in HH. cbn in HH. unfold vy in HH. lia.
      + congruence.
    - pose proof (nonempty_bounds _ EY) as [_ HH]; congruence. }
  unfold ile3. cbn [lo3 hi3]. split.
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


Theorem ztdiv4_complete : forall s,
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

Theorem zfdiv4_complete : forall s,
  feasible3 sol s -> forall t, contains3 sol s t -> sle3 (zfdiv4 s) t.
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

Lemma sle3_mir_xy : forall a b, sle3 (mir_xy a) (mir_xy b) <-> sle3 a b.
Proof.
  intros a b. unfold sle3, mir_xy; cbn [sx3 sy3 sz3].
  rewrite !ile3_mirror. tauto.
Qed.

Lemma ne_mir_xy : forall s, ne_store3 (mir_xy s) = ne_store3 s.
Proof.
  intros s. unfold ne_store3, mir_xy; cbn [sx3 sy3 sz3].
  rewrite !nonempty3b_mirror. reflexivity.
Qed.

Lemma in_mir_xy_inv : forall s vx vy vz,
  in_store3 (mir_xy s) vx vy vz -> in_store3 s (- vx) (- vy) vz.
Proof.
  intros s vx vy vz H. pose proof (in_mir_xy (mir_xy s) vx vy vz H) as H2.
  rewrite mir_xy_invol in H2. exact H2.
Qed.

Lemma csol_of_sol_xy : forall vx vy vz, sol vx vy vz -> csol (- vx) (- vy) vz.
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  unfold cdiv. rewrite Z.opp_involutive. lia.
Qed.

Lemma csol_of_sol_xz : forall vx vy vz, sol vx vy vz -> csol (- vx) vy (- vz).
Proof.
  intros vx vy vz [Hnz Hq]. split; [lia | ].
  unfold cdiv. rewrite Z.div_opp_opp by lia. lia.
Qed.

Theorem zcdiv4_complete : forall s,
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
Lemma esol_of_sol_pos : forall vx vy vz, sol vx vy vz -> 0 < vz -> esol vx vy vz.
Proof.
  intros vx vy vz [Hnz Hq] Hpos. split; [lia | ].
  rewrite (proj2 (Z.ltb_lt 0 vz) Hpos). exact Hq.
Qed.

Lemma esol_of_sol_xz_neg : forall vx vy vz, sol vx vy vz -> 0 < vz -> esol (- vx) vy (- vz).
Proof.
  intros vx vy vz Hsol Hpos. destruct (csol_of_sol_xz vx vy vz Hsol) as [Hnz Hq].
  split; [lia | ]. rewrite (proj2 (Z.ltb_ge 0 (- vz)) ltac:(lia)). exact Hq.
Qed.

Theorem zediv4_complete : forall s,
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

Theorem zfdiv4_ne_feasible : forall s,
  ne_store3 (zfdiv4 s) = true -> feasible3 sol s.
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
