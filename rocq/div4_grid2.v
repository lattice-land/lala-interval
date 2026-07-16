(* Grid validation of the SLICE-LEVEL statements of div4.v (dev file):
   the two positive-slice solvers are exact w.r.t. the solutions restricted
   to vz >= 1:
   1. finite stores over [-3,3]: output = exact hull of the slice solutions
      (empty output iff no slice solution) -- validates fpos_sound/fpos_best/
      fpos_ne_feasible and the tdiv counterparts on the grid;
   2. infinite stores over {-oo,-2..2,+oo}: window soundness + limit oracle. *)
From LalaInterval Require Import itv fdiv2 fdiv3 div4.
From Stdlib Require Import ZArith Lia List Bool. Import ListNotations.
Open Scope Z_scope.

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

Definition fdivZ (y z : Z) : Z := y / z.
Definition tdivZ (y z : Z) : Z := Z.quot y z.

(* ---- 1. finite exact-hull for the slice solvers (z >= 1) ---- *)
Definition zs : list Z := [-3;-2;-1;0;1;2;3].
Definition itvs : list itv :=
  flat_map (fun l => map (Itv l) (filter (Z.leb l) zs)) zs.
Definition allstores : list store :=
  flat_map (fun ix => flat_map (fun iy => map (St ix iy) itvs) itvs) itvs.

Definition rng (a b : Z) : list Z :=
  map (fun n => a + Z.of_nat n) (List.seq 0 (Z.to_nat (b - a + 1))).

Definition slice_sols (dv : Z -> Z -> Z) (s : store) : list (Z * Z * Z) :=
  flat_map (fun z =>
    if z <? 1 then [] else
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

Definition slice_exact_ok (op : store3 -> store3) (dv : Z -> Z -> Z) (s : store) : bool :=
  let out := op (st3 s) in
  match hull (slice_sols dv s) with
  | None => negb (ne_store3 out)
  | Some h => (ne_store3 out && store3_eqb out (st3 h))%bool
  end.

Theorem fpos_exact_grid : forallb (slice_exact_ok zfdiv_pos3 fdivZ) allstores = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tpos_exact_grid : forallb (slice_exact_ok ztdiv_pos3 tdivZ) allstores = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 2. infinite stores: window soundness + limit oracle ---- *)
Definition zinfs : list Zinf := [Ninf; Fin (-2); Fin (-1); Fin 0; Fin 1; Fin 2; Pinf].
Definition itv3s : list itv3 :=
  flat_map (fun l => map (Itv3 l) zinfs) zinfs.
Definition allstores3 : list store3 :=
  flat_map (fun ix => flat_map (fun iy => map (St3 ix iy) itv3s) itv3s) itv3s.

Definition window : list Z := [-8;-7;-6;-5;-4;-3;-2;-1;0;1;2;3;4;5;6;7;8].

Definition slice_sound_ok (op : store3 -> store3) (dv : Z -> Z -> Z) (s : store3) : bool :=
  let p := op s in
  forallb (fun z =>
    if z <? 1 then true else
    forallb (fun y =>
      let x := dv y z in
      if in3b s x y z then in3b p x y z else true)
      window)
    window.

Theorem fpos_infinite_sound_grid :
  forallb (slice_sound_ok zfdiv_pos3 fdivZ) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tpos_infinite_sound_grid :
  forallb (slice_sound_ok ztdiv_pos3 tdivZ) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

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

Definition ne3b (i : itv3) : bool := nonempty3b i.

Definition slice_limit_ok (op : store3 -> store3) (s : store3) : bool :=
  if negb ((ne3b (sx3 s) && ne3b (sy3 s) && ne3b (sz3 s))%bool) then true else
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

Theorem fpos_limit_grid : forallb (slice_limit_ok zfdiv_pos3) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tpos_limit_grid : forallb (slice_limit_ok ztdiv_pos3) allstores3 = true.
Proof. vm_compute. reflexivity. Qed.
