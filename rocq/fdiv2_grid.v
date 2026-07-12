(* Grid validation of the fdiv2 model: on all stores over [-3,3], the
   propagator equals the exact hull of the solution set (optimality +
   soundness), and detects infeasibility. Dev file, not part of the build. *)
From LalaInterval Require Import fdiv2.
From Stdlib Require Import ZArith Lia List. Import ListNotations.
Open Scope Z_scope.

Definition zs : list Z := [-3;-2;-1;0;1;2;3].
Definition itvs : list itv :=
  flat_map (fun l => map (Itv l) (filter (Z.leb l) zs)) zs.
Definition allstores : list store :=
  flat_map (fun ix => flat_map (fun iy => map (St ix iy) itvs) itvs) itvs.

Definition memb (i : itv) (v : Z) : bool := ((lo i <=? v) && (v <=? hi i))%bool.
Definition vals (i : itv) : list Z := filter (memb i) zs.

Definition triples (s : store) : list (Z * Z * Z) :=
  flat_map (fun y =>
    flat_map (fun z =>
      if (negb (z =? 0) && memb (sx s) (y / z))%bool
      then [(y / z, y, z)] else [])
      (vals (sz s)))
    (vals (sy s)).

Definition fold_min (f : Z * Z * Z -> Z) (ts : list (Z * Z * Z)) (init : Z) : Z :=
  fold_left (fun acc t => Z.min acc (f t)) ts init.
Definition fold_max (f : Z * Z * Z -> Z) (ts : list (Z * Z * Z)) (init : Z) : Z :=
  fold_left (fun acc t => Z.max acc (f t)) ts init.

Definition opt_ok (s : store) : bool :=
  let p := propagator s in
  match triples s with
  | [] => negb (ne_store p)
  | t0 :: _ =>
    let gx := fun '(x,_,_) => x in
    let gy := fun '(_,y,_) => y in
    let gz := fun '(_,_,z) => z in
    ((lo (sx p) =? fold_min gx (triples s) (gx t0)) &&
     (hi (sx p) =? fold_max gx (triples s) (gx t0)) &&
     (lo (sy p) =? fold_min gy (triples s) (gy t0)) &&
     (hi (sy p) =? fold_max gy (triples s) (gy t0)) &&
     (lo (sz p) =? fold_min gz (triples s) (gz t0)) &&
     (hi (sz p) =? fold_max gz (triples s) (gz t0)))%bool
  end.

Theorem fdiv2_opt_grid : forallb opt_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
