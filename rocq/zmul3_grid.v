(* Grid validation of the zmul3 model (dev file, not part of the build):
   1. FINITE: on all stores over [-3,3], the output is sound (contains every
      solution of x = y*z) and reductive.
   2. INFINITE: same checks on all stores with bounds in {-oo,-2..2,+oo},
      solutions sampled in the window [-6,6]^2 for (y,z). *)
From LalaInterval Require Import itv3 zadd3 zmul3.
From Stdlib Require Import ZArith Lia List Bool. Import ListNotations.
Open Scope Z_scope.

Definition zinfs : list Zinf := [Ninf; Fin (-2); Fin (-1); Fin 0; Fin 1; Fin 2; Pinf].
Definition itv3s : list itv3 :=
  flat_map (fun l => map (Itv3 l) zinfs) zinfs.
Definition allstores3 : list store3 :=
  flat_map (fun ix => flat_map (fun iy => map (St3 ix iy) itv3s) itv3s) itv3s.

Definition finzs : list Zinf := map Fin [-3;-2;-1;0;1;2;3].
Definition fitv3s : list itv3 :=
  flat_map (fun l => map (Itv3 l) finzs) finzs.
Definition fallstores3 : list store3 :=
  flat_map (fun ix => flat_map (fun iy => map (St3 ix iy) fitv3s) fitv3s) fitv3s.

Definition mem3b (i : itv3) (v : Z) : bool :=
  (zleb (lo3 i) (Fin v) && zleb (Fin v) (hi3 i))%bool.
Definition in3b (s : store3) (vx vy vz : Z) : bool :=
  (mem3b (sx3 s) vx && mem3b (sy3 s) vy && mem3b (sz3 s) vz)%bool.

Definition window : list Z := [-6;-5;-4;-3;-2;-1;0;1;2;3;4;5;6].

Definition sound_ok (s : store3) : bool :=
  let p := zmul3 s in
  forallb (fun y =>
    forallb (fun z =>
      if in3b s (y * z) y z then in3b p (y * z) y z else true)
      window)
    window.

Definition ile3b (i j : itv3) : bool :=
  (zleb (lo3 j) (lo3 i) && zleb (hi3 i) (hi3 j))%bool.
Definition red_ok (s : store3) : bool :=
  let p := zmul3 s in
  (ile3b (sx3 p) (sx3 s) && ile3b (sy3 p) (sy3 s) && ile3b (sz3 p) (sz3 s))%bool.

Theorem zmul3_finite_sound_grid : forallb sound_ok fallstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zmul3_finite_reductive_grid : forallb red_ok fallstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zmul3_infinite_sound_grid : forallb sound_ok allstores3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zmul3_infinite_reductive_grid : forallb red_ok allstores3 = true.
Proof. vm_compute. reflexivity. Qed.
