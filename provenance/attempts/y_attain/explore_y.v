From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.
Definition mk (a b c d e f : Z) : store := St (Itv a b) (Itv c d) (Itv e f).

Definition w1 := mk (-10) (-1) (-6) (-2) 1 3.
Compute (fdivxz_pos w1).
Compute (let P := fdivxz_pos w1 in
  (lo (sx P), hi (sx P), lo (sz P), hi (sz P), hi (sy w1),
   lo (sx P) * lo (sz P), lo (sx P) * hi (sz P))).

(* another yu<0 case *)
Definition w2 := mk (-10) (-1) (-20) (-3) 1 5.
Compute (fdivxz_pos w2).
Compute (let P := fdivxz_pos w2 in
  (lo (sx P), hi (sx P), lo (sz P), hi (sz P), hi (sy w2),
   lo (sx P) * lo (sz P), lo (sx P) * hi (sz P))).
