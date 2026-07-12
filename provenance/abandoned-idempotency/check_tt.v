From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.
Definition rng : list Z := (-4 :: -3 :: -2 :: -1 :: 0 :: 1 :: 2 :: 3 :: 4 :: nil)%Z.
(* claim: tightness => achievability at zl and zu *)
Definition claim (a b c d zl zu : Z) : bool :=
  implb (andb (a <=? -1) (andb (0 <=? b)
        (andb (a <=? b) (andb (c <=? d) (andb (zl <=? zu) (andb (zu <? 0)
        (andb (Xlo c d zl zu <=? a) (b <=? Xhi c d zl zu))))))))
        (andb (c <=? zu * a) (andb (zu * (b+1) <? d)
              (andb (c <=? zl * a) (zl * (b+1) <? d)))).
Definition allok : bool :=
  forallb (fun a => forallb (fun b => forallb (fun c => forallb (fun d =>
   forallb (fun zl => forallb (fun zu => claim a b c d zl zu) rng) rng) rng) rng) rng) rng.
Eval vm_compute in allok.
