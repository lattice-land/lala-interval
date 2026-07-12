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

Definition witness (ix1 iy iz0 : itv) : bool :=
  let iz  := inter iz0 (fden ix1 iy iz0) in
  let ix2 := inter ix1 (Cx iy iz) in
  let iy2 := inter iy (Cy ix2 iz) in
  let a := lo ix2 in let b := hi ix2 in let c := lo iy2 in let d := hi iy2 in
  let nM0 := negb ((a <=? 0) && (0 <=? b) && (c <=? 0) && (0 <=? d))%bool in
  let base := andb (hi iz0 <? 0) (andb (ileb ix1 (Cx iy iz0))
                (andb (neb iz) (andb (neb ix2) (neb iy2)))) in
  (base && nM0 && (a =? 0) && (b =? 0) && (d <? 0))%bool.

Definition results : list (itv * itv * itv * itv * itv * itv) :=
  flat_map (fun a => flat_map (fun b => flat_map (fun c =>
    if witness a b c then
      let iz := inter c (fden a b c) in
      let ix2 := inter a (Cx b iz) in
      let iy2 := inter b (Cy ix2 iz) in
      [(a,b,c,iz,ix2,iy2)]
    else []) itvs) itvs) itvs.

Compute results.
