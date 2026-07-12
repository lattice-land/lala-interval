From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition consistent_b (s : store) : bool :=
  andb (andb (lo (sx s) <=? hi (sx s)) (lo (sy s) <=? hi (sy s))) (lo (sz s) <=? hi (sz s)).
Definition signdef (w : store) : bool := orb (0 <? lo (sz w)) (hi (sz w) <? 0).

(* Is vx within the 1D floor-range [min(yl/z,yu/z), max(...)] for SOME z-corner of iz (z<>0)? *)
Definition in1d (iy iz : itv) (vx : Z) : bool :=
  existsb (fun z => andb (negb (z =? 0))
     (andb (Z.min (Z.div (lo iy) z) (Z.div (hi iy) z) <=? vx)
           (vx <=? Z.max (Z.div (lo iy) z) (Z.div (hi iy) z))))
     [lo iz; hi iz].

Definition x1d_ok (w : store) : bool :=
  let f := fdivxz_pos w in
  implb (andb (signdef w) (consistent_b f))
        (andb (in1d (sy w) (sz f) (lo (sx f))) (in1d (sy w) (sz f) (hi (sx f)))).

Theorem x1d_grid : forallb x1d_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
