(* Grid validation of the div4 model (dev file, not part of the build):
   1. EXACT-HULL DIFFERENTIAL (finite): on all stores over [-3,3], each of
      the four propagators returns EXACTLY the hull of the solutions of the
      input (brute force); on infeasible inputs the output is empty.  This
      is soundness + completeness on the grid, and mirrors the exhaustive
      C++ tests of z*div_4.
   2. INFINITE: on all stores with bounds in {-oo,-2..2,+oo}:
      (a) soundness sample: every solution in the window [-8,8]^2 stays in;
      (b) reductivity;
      (c) limit oracle: substituting +-L for the infinities (L = 32, 64),
          every finite output bound agrees with both L-runs, and every
          infinite output bound corresponds to L-runs that differ (i.e. the
          bound genuinely scales with L). *)
From LalaInterval Require Import itv fdiv2 fdiv3 div4.
From Stdlib Require Import ZArith Lia List Bool. Import ListNotations.
Open Scope Z_scope.

(* ---- shared helpers ---- *)
Definition zinf_eqb (a b : Zinf) : bool :=
  match a, b with
  | Fin x, Fin y => x =? y
  | Pinf, Pinf => true
  | Ninf, Ninf => true
  | _, _ => false
  end.
Definition itv3_eqb (i j : itv3) : bool :=
  (zinf_eqb (lo3 i) (lo3 j) && zinf_eqb (hi3 i) (hi3 j))%bool.
Definition store3_eqb (u v : store3) : bool :=
  (itv3_eqb (sx3 u) (sx3 v) && itv3_eqb (sy3 u) (sy3 v)
   && itv3_eqb (sz3 u) (sz3 v))%bool.

Definition to3 (i : itv) : itv3 := Itv3 (Fin (lo i)) (Fin (hi i)).
Definition st3 (s : store) : store3 := St3 (to3 (sx s)) (to3 (sy s)) (to3 (sz s)).

Definition mem3b (i : itv3) (v : Z) : bool :=
  (zleb (lo3 i) (Fin v) && zleb (Fin v) (hi3 i))%bool.
Definition in3b (s : store3) (vx vy vz : Z) : bool :=
  (mem3b (sx3 s) vx && mem3b (sy3 s) vy && mem3b (sz3 s) vz)%bool.

(* the four division functions (y z |-> x) *)
Definition fdivZ (y z : Z) : Z := y / z.
Definition tdivZ (y z : Z) : Z := Z.quot y z.
Definition cdivZ (y z : Z) : Z := cdiv y z.
Definition edivZ (y z : Z) : Z := if 0 <? z then y / z else cdiv y z.

(* ---- 1. finite exact-hull differential ---- *)
Definition zs : list Z := [-3;-2;-1;0;1;2;3].
Definition itvs : list itv :=
  flat_map (fun l => map (Itv l) (filter (Z.leb l) zs)) zs.
Definition allstores : list store :=
  flat_map (fun ix => flat_map (fun iy => map (St ix iy) itvs) itvs) itvs.

Definition rng (a b : Z) : list Z :=
  map (fun n => a + Z.of_nat n) (List.seq 0 (Z.to_nat (b - a + 1))).

Definition sols (dv : Z -> Z -> Z) (s : store) : list (Z * Z * Z) :=
  flat_map (fun z =>
    if z =? 0 then [] else
    flat_map (fun y =>
      let x := dv y z in
      if ((lo (sx s) <=? x) && (x <=? hi (sx s)))%bool then [(x, y, z)] else [])
      (rng (lo (sy s)) (hi (sy s))))
    (rng (lo (sz s)) (hi (sz s))).

Fixpoint hull (l : list (Z * Z * Z)) : option store :=
  match l with
  | [] => None
  | (x, y, z) :: tl =>
    match hull tl with
    | None => Some (St (Itv x x) (Itv y y) (Itv z z))
    | Some h => Some (St (Itv (Z.min x (lo (sx h))) (Z.max x (hi (sx h))))
                        (Itv (Z.min y (lo (sy h))) (Z.max y (hi (sy h))))
                        (Itv (Z.min z (lo (sz h))) (Z.max z (hi (sz h)))))
    end
  end.

Definition exact_ok (op : store3 -> store3) (dv : Z -> Z -> Z) (s : store) : bool :=
  let out := op (st3 s) in
  match hull (sols dv s) with
  | None => negb (ne_store3 out)
  | Some h => (ne_store3 out && store3_eqb out (st3 h))%bool
  end.

Theorem ztdiv4_exact_grid : forallb (exact_ok ztdiv4 tdivZ) allstores = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zfdiv4_exact_grid : forallb (exact_ok zfdiv4 fdivZ) allstores = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zcdiv4_exact_grid : forallb (exact_ok zcdiv4 cdivZ) allstores = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zediv4_exact_grid : forallb (exact_ok zediv4 edivZ) allstores = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 2. infinite-bound grids ---- *)
Definition zinfs : list Zinf := [Ninf; Fin (-2); Fin (-1); Fin 0; Fin 1; Fin 2; Pinf].
Definition itv3s : list itv3 :=
  flat_map (fun l => map (Itv3 l) zinfs) zinfs.
Definition allstores3 : list store3 :=
  flat_map (fun ix => flat_map (fun iy => map (St3 ix iy) itv3s) itv3s) itv3s.

Definition window : list Z := [-8;-7;-6;-5;-4;-3;-2;-1;0;1;2;3;4;5;6;7;8].

(* (a) every solution of s in the window stays in the output *)
Definition sound_ok (op : store3 -> store3) (dv : Z -> Z -> Z) (s : store3) : bool :=
  let p := op s in
  forallb (fun z =>
    if z =? 0 then true else
    forallb (fun y =>
      let x := dv y z in
      if in3b s x y z then in3b p x y z else true)
      window)
    window.

Theorem ztdiv4_infinite_sound_grid :
  forallb (sound_ok ztdiv4 tdivZ) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zfdiv4_infinite_sound_grid :
  forallb (sound_ok zfdiv4 fdivZ) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zcdiv4_infinite_sound_grid :
  forallb (sound_ok zcdiv4 cdivZ) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zediv4_infinite_sound_grid :
  forallb (sound_ok zediv4 edivZ) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

(* (b) reductivity *)
Definition zleb_ile3 (i j : itv3) : bool :=
  (zleb (lo3 j) (lo3 i) && zleb (hi3 i) (hi3 j))%bool.
Definition red_ok (op : store3 -> store3) (s : store3) : bool :=
  let p := op s in
  (zleb_ile3 (sx3 p) (sx3 s) && zleb_ile3 (sy3 p) (sy3 s) && zleb_ile3 (sz3 p) (sz3 s))%bool.

Theorem ztdiv4_infinite_red_grid : forallb (red_ok ztdiv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zfdiv4_infinite_red_grid : forallb (red_ok zfdiv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zcdiv4_infinite_red_grid : forallb (red_ok zcdiv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zediv4_infinite_red_grid : forallb (red_ok zediv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

(* (c) limit oracle: infinities replaced by +-L must reproduce every finite
   output bound exactly, and the L-runs must differ wherever the output
   bound is infinite *)
Definition substL (L : Z) (a : Zinf) : Zinf :=
  match a with Ninf => Fin (- L) | Pinf => Fin L | Fin v => Fin v end.
Definition substLi (L : Z) (i : itv3) : itv3 :=
  Itv3 (substL L (lo3 i)) (substL L (hi3 i)).
Definition substLs (L : Z) (s : store3) : store3 :=
  St3 (substLi L (sx3 s)) (substLi L (sy3 s)) (substLi L (sz3 s)).

Definition bound_ok (binf b1 b2 : Zinf) : bool :=
  match binf with
  | Fin v => (zinf_eqb b1 (Fin v) && zinf_eqb b2 (Fin v))%bool
  | _ => negb (zinf_eqb b1 b2)
  end.

Definition limit_ok (op : store3 -> store3) (s : store3) : bool :=
  if negb (ne_store3 s) then true else
  let oi := op s in
  let o1 := op (substLs 32 s) in
  let o2 := op (substLs 64 s) in
  match ne_store3 oi, ne_store3 o1, ne_store3 o2 with
  | false, false, false => true
  | true, true, true =>
      (bound_ok (lo3 (sx3 oi)) (lo3 (sx3 o1)) (lo3 (sx3 o2)) &&
       bound_ok (hi3 (sx3 oi)) (hi3 (sx3 o1)) (hi3 (sx3 o2)) &&
       bound_ok (lo3 (sy3 oi)) (lo3 (sy3 o1)) (lo3 (sy3 o2)) &&
       bound_ok (hi3 (sy3 oi)) (hi3 (sy3 o1)) (hi3 (sy3 o2)) &&
       bound_ok (lo3 (sz3 oi)) (lo3 (sz3 o1)) (lo3 (sz3 o2)) &&
       bound_ok (hi3 (sz3 oi)) (hi3 (sz3 o1)) (hi3 (sz3 o2)))%bool
  | _, _, _ => false
  end.

Theorem ztdiv4_limit_grid : forallb (limit_ok ztdiv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zfdiv4_limit_grid : forallb (limit_ok zfdiv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zcdiv4_limit_grid : forallb (limit_ok zcdiv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zediv4_limit_grid : forallb (limit_ok zediv4) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.
