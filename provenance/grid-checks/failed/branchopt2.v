From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition consistent_b (s : store) : bool :=
  andb (andb (lo (sx s) <=? hi (sx s)) (lo (sy s) <=? hi (sy s))) (lo (sz s) <=? hi (sz s)).
Definition signdef (w : store) : bool := orb (0 <? lo (sz w)) (hi (sz w) <? 0).

(* is vx a corner quotient y/z with y in {lo iy,hi iy}, z in {lo iz,hi iz} (z<>0)? *)
Definition corner_x (iy : itv) (zs : list Z) (vx : Z) : bool :=
  existsb (fun y => existsb (fun z => andb (negb (z =? 0)) (vx =? Z.div y z))
            zs) [lo iy; hi iy].

(* Is each x-bound of F(w) a corner quotient of (sy w, z) for z a corner of the
   ORIGINAL or the OUTPUT z-interval? *)
Definition xcorner_ok (w : store) : bool :=
  let f := fdivxz_pos w in
  let zs := [lo (sz w); hi (sz w); lo (sz f); hi (sz f)] in
  implb (andb (signdef w) (consistent_b f))
        (andb (corner_x (sy w) zs (lo (sx f)))
              (corner_x (sy w) zs (hi (sx f)))).

Theorem xcorner_grid : forallb xcorner_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
