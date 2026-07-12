From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition ne (i:itv) : bool := lo i <=? hi i.
Definition Pne (w:store) : bool :=
  let P := fdivxz_pos w in andb (ne (sx P)) (andb (ne (sy P)) (ne (sz P))).

Definition BLU (w:store) : bool :=
  let P := fdivxz_pos w in
  let a := lo (sx P) in let b := hi (sx P) in
  let zl := lo (sz P) in let zu := hi (sz P) in
  let c := lo (sy w) in let d := hi (sy w) in
  if andb (Pne w) (orb (0 <? lo (sz w)) (hi (sz w) <? 0)) then
    andb (andb
      (implb (0 <? zu) (a*zu <=? d))          (* BL1 *)
      (implb (0 <? zl) (a*zl <=? d)))          (* BL2 *)
    (andb (andb
      (implb (zl <? 0) ((b+1)*zl+1 <=? d))     (* BL3 *)
      (implb (zu <? 0) ((b+1)*zu+1 <=? d)))    (* BL4 *)
    (andb (andb
      (implb (0 <? zu) (c <=? (b+1)*zu-1))     (* BU1 *)
      (implb (0 <? zl) (c <=? (b+1)*zl-1)))     (* BU2 *)
    (andb
      (implb (zl <? 0) (c <=? a*zl))           (* BU3 *)
      (implb (zu <? 0) (c <=? a*zu)))))        (* BU4 *)
  else true.

Theorem BLU_grid : forallb BLU allstores = true.
Proof. vm_compute. reflexivity. Qed.
