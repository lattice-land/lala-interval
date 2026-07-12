From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.
Definition consistent_b (s : store) : bool :=
  andb (andb (lo (sx s) <=? hi (sx s)) (lo (sy s) <=? hi (sy s))) (lo (sz s) <=? hi (sz s)).
Definition signdef (w : store) : bool := orb (0 <? lo (sz w)) (hi (sz w) <? 0).
Definition Xhib (iy iz : itv) : Z := Xhi (lo iy) (hi iy) (lo iz) (hi iz).
Definition Xlob (iy iz : itv) : Z := Xlo (lo iy) (hi iy) (lo iz) (hi iz).

(* Is each x-bound of F(w) equal to a quotient-enclosure bound over the OUTPUT z or the ORIGINAL z? *)
Definition xub_ok (w : store) : bool :=
  let f := fdivxz_pos w in
  implb (andb (signdef w) (consistent_b f))
    (andb (orb (hi (sx f) =? Xhib (sy w) (sz f)) (hi (sx f) =? Xhib (sy w) (sz w)))
          (orb (lo (sx f) =? Xlob (sy w) (sz f)) (lo (sx f) =? Xlob (sy w) (sz w)))).

Theorem xub_grid : forallb xub_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
