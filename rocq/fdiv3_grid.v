(* Grid validation of the fdiv3 model (dev file, not part of the build):
   1. DIFFERENTIAL: on finite bounds, propagator3 agrees exactly with the
      verified finite band propagator (fdiv2.propagator) on all stores
      over [-3,3].
   2. INFINITE: on all stores with bounds in {-oo,-2..2,+oo}, the output
      (a) contains every solution of the input in the window [-8,8]^3
          (soundness sample) and
      (b) is contained in the input (reductivity). *)
From LalaInterval Require Import itv fdiv2 fdiv3.
From Stdlib Require Import ZArith Lia List Bool. Import ListNotations.
Open Scope Z_scope.

(* ---- 1. differential check ---- *)
Definition zs : list Z := [-3;-2;-1;0;1;2;3].
Definition itvs : list itv :=
  flat_map (fun l => map (Itv l) (filter (Z.leb l) zs)) zs.
Definition allstores : list store :=
  flat_map (fun ix => flat_map (fun iy => map (St ix iy) itvs) itvs) itvs.

Definition to3 (i : itv) : itv3 := Itv3 (Fin (lo i)) (Fin (hi i)).
Definition st3 (s : store) : store3 := St3 (to3 (sx s)) (to3 (sy s)) (to3 (sz s)).

Definition zinf_eqb (a b : Zinf) : bool :=
  match a, b with
  | Fin x, Fin y => x =? y
  | Pinf, Pinf => true
  | Ninf, Ninf => true
  | _, _ => false
  end.
Definition itv3_eqb (i j : itv3) : bool :=
  (zinf_eqb (lo3 i) (lo3 j) && zinf_eqb (hi3 i) (hi3 j))%bool.
Definition eq3b (u : store3) (v : store) : bool :=
  (itv3_eqb (sx3 u) (to3 (sx v)) && itv3_eqb (sy3 u) (to3 (sy v))
   && itv3_eqb (sz3 u) (to3 (sz v)))%bool.

(* the finite and infinite propagators agree on finite stores, up to
   emptiness (empty results may use different empty representations) *)
Definition ne_eqb (u : store3) (v : store) : bool :=
  match ne_store3 u, ne_store v with
  | false, false => true
  | true, true => eq3b u v
  | _, _ => false
  end.

Definition diff_ok (s : store) : bool :=
  ne_eqb (propagator3 (st3 s)) (propagator s).

Theorem fdiv3_differential_grid : forallb diff_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- 2. infinite-bound soundness + reductivity sample ---- *)
Definition zinfs : list Zinf := [Ninf; Fin (-2); Fin (-1); Fin 0; Fin 1; Fin 2; Pinf].
Definition itv3s : list itv3 :=
  flat_map (fun l => map (Itv3 l) zinfs) zinfs.
Definition allstores3 : list store3 :=
  flat_map (fun ix => flat_map (fun iy => map (St3 ix iy) itv3s) itv3s) itv3s.

Definition zleb3 := zleb.
Definition mem3b (i : itv3) (v : Z) : bool :=
  (zleb (lo3 i) (Fin v) && zleb (Fin v) (hi3 i))%bool.
Definition in3b (s : store3) (vx vy vz : Z) : bool :=
  (mem3b (sx3 s) vx && mem3b (sy3 s) vy && mem3b (sz3 s) vz)%bool.

Definition window : list Z := [-8;-7;-6;-5;-4;-3;-2;-1;0;1;2;3;4;5;6;7;8].

(* every solution of s in the window stays in the output *)
Definition sound_ok (s : store3) : bool :=
  let p := propagator3 s in
  forallb (fun y =>
    forallb (fun z =>
      if (negb (z =? 0) && in3b s (y / z) y z)%bool
      then in3b p (y / z) y z else true)
      window)
    window.

Definition zleb_ile3 (i j : itv3) : bool :=
  (zleb (lo3 j) (lo3 i) && zleb (hi3 i) (hi3 j))%bool.
Definition red_ok (s : store3) : bool :=
  let p := propagator3 s in
  (zleb_ile3 (sx3 p) (sx3 s) && zleb_ile3 (sy3 p) (sy3 s) && zleb_ile3 (sz3 p) (sz3 s))%bool.

Theorem fdiv3_infinite_sound_grid : forallb sound_ok allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fdiv3_infinite_reductive_grid : forallb red_ok allstores3 = true.
Proof. vm_compute. reflexivity. Qed.
