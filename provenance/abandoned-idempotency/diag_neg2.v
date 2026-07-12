From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition ileb (i j : itv) : bool := andb (lo j <=? lo i) (hi i <=? hi j).
Definition neb (i : itv) : bool := lo i <=? hi i.
Definition rng : list Z := (-3 :: -2 :: -1 :: 0 :: 1 :: 2 :: 3 :: nil)%Z.
Definition itvs : list itv :=
  flat_map (fun a => map (fun b => Itv a b) (filter (fun b => a <=? b) rng)) rng.

Definition rows_neg_ok (ix1 iy iz0 : itv) : bool :=
  let iz  := inter iz0 (fden ix1 iy iz0) in
  let ix2 := inter ix1 (Cx iy iz) in
  let iy2 := inter iy (Cy ix2 iz) in
  let a := lo ix2 in let b := hi ix2 in let c := lo iy2 in let d := hi iy2 in
  let zl := lo iz in let zu := hi iz in
  let nM0 := negb ((a <=? 0) && (0 <=? b) && (c <=? 0) && (0 <=? d))%bool in
  let base := andb (hi iz0 <? 0) (andb (ileb ix1 (Cx iy iz0))
                (andb (neb iz) (andb (neb ix2) (neb iy2)))) in
  let chk (g cc : bool) := implb (andb base g) cc in
  forallb (fun x : bool => x)
  [ chk ((0 <? a) && (0 <=? c) && (0 <? d))%bool (((Z.max 1 c / (b+1) + 1 <=? zl) && (zu <=? d / a))%bool)
  ; chk ((0 <? a) && (d <? 0) && (c <=? 0))%bool (((cdiv c a <=? zl) && (zu <=? cdiv (Z.min (-1) d) (b+1) - 1))%bool)
  ; chk ((0 <? a) && negb ((0 <=? c) && (0 <? d)) && negb ((d <? 0) && (c <=? 0)))%bool (((cdiv c a <=? zl) && (zu <=? d / a))%bool)
  ; chk ((a <=? 0) && (b <? -1) && (0 <=? c) && (0 <? d))%bool (((d / (b+1) + 1 <=? zl) && (zu <=? c / a))%bool)
  ; chk ((a <=? 0) && (b <? -1) && (c <? 0) && (d <=? 0))%bool (((cdiv d a <=? zl) && (zu <=? cdiv c (b+1) - 1))%bool)
  ; chk ((a <=? 0) && (b <? -1) && negb ((0 <=? c) && (0 <? d)) && negb ((c <? 0) && (d <=? 0)))%bool (((d / (b+1) + 1 <=? zl) && (zu <=? cdiv c (b+1) - 1))%bool)
  ; chk (nM0 && (a =? 0) && (b =? 0) && (d <? 0))%bool (zu <=? d - 1)
  ; chk (nM0 && (a =? 0) && (b =? 0) && (0 <=? d))%bool (c + 1 <=? zl)
  ; chk ((a <=? -1) && (b =? -1) && (c <? 0) && (d <=? 0))%bool (cdiv (Z.min (-1) d) a <=? zl)
  ; chk ((a <=? -1) && (b =? -1) && negb ((c <? 0) && (d <=? 0)) && (0 <? d) && (0 <=? c))%bool (zu <=? Z.max 1 c / a)
  ; chk ((a <=? -1) && (b =? -1) && negb ((c <? 0) && (d <=? 0)) && negb ((0 <? d) && (0 <=? c)) && (c =? 0) && (d =? 0))%bool (((1 <=? zl) && (zu <=? 0))%bool)
  ; chk (nM0 && (a =? 0) && (0 <? b) && (c <? 0) && (d <=? 0))%bool (zu <=? cdiv (Z.min (-1) d) (b+1) - 1)
  ; chk (nM0 && (a =? 0) && (0 <? b) && negb ((c <? 0) && (d <=? 0)) && (0 <? d) && (0 <=? c))%bool (Z.max 1 c / (b+1) + 1 <=? zl)
  ].

Theorem rows_neg2_grid :
  forallb (fun a => forallb (fun b => forallb (fun c => rows_neg_ok a b c) itvs) itvs) itvs = true.
Proof. vm_compute. reflexivity. Qed.
