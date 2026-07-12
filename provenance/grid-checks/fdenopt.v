From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition memb (i : itv) (v : Z) : bool := andb (lo i <=? v) (v <=? hi i).
(* is z attained by a solution with x in ix, y in iy ? *)
Definition attained_z (ix iy : itv) (z : Z) : bool :=
  existsb (fun x => existsb (fun y =>
     andb (memb ix x) (andb (memb iy y) (andb (negb (z =? 0)) (x =? Z.div y z)))) rng) rng.

Definition ileb (i j : itv) : bool := andb (lo j <=? lo i) (hi i <=? hi j).
Definition Cxb (iy iz : itv) : itv :=
  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz)).

(* Version A: fden z-optimal for ARBITRARY ix *)
Definition fden_opt_ok (ix iy iz : itv) : bool :=
  let f := fden ix iy iz in
  let signdef := orb (0 <? lo iz) (hi iz <? 0) in
  implb (andb signdef (lo f <=? hi f))
        (andb (attained_z ix iy (lo f)) (attained_z ix iy (hi f))).

(* Version B: additionally assume ix is quotient-tight (ix subset Cx iy iz) *)
Definition fden_opt_tight_ok (ix iy iz : itv) : bool :=
  let f := fden ix iy iz in
  let signdef := orb (0 <? lo iz) (hi iz <? 0) in
  implb (andb (ileb ix (Cxb iy iz)) (andb signdef (lo f <=? hi f)))
        (andb (attained_z ix iy (lo f)) (attained_z ix iy (hi f))).

Theorem fden_optB : forallb (fun a => forallb (fun b => forallb (fun c => fden_opt_tight_ok a b c) itvs) itvs) itvs = true.
Proof. vm_compute. reflexivity. Qed.
