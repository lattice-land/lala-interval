From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.
Definition consistent_b (s : store) : bool :=
  andb (andb (lo (sx s) <=? hi (sx s)) (lo (sy s) <=? hi (sy s))) (lo (sz s) <=? hi (sz s)).
(* is there a z-corner of (sz p) s.t. y / z lands in the x-interval? -> witness (y/z, y, z) *)
Definition yband (p : store) (y : Z) : bool :=
  existsb (fun z => andb (negb (z =? 0))
     (andb (lo (sx p) <=? Z.div y z) (Z.div y z <=? hi (sx p))))
     [lo (sz p); hi (sz p)].
Definition y1d_ok (s : store) : bool :=
  let p := propagator s in
  implb (consistent_b p) (andb (yband p (lo (sy p))) (yband p (hi (sy p)))).
Theorem y1d_grid : forallb y1d_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
