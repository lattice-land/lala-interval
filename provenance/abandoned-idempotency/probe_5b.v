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

Definition active (ix1 iy iz0 : itv) : bool :=
  let iz  := inter iz0 (fden ix1 iy iz0) in
  let ix2 := inter ix1 (Cx iy iz) in
  let iy2 := inter iy (Cy ix2 iz) in
  let a := lo ix2 in let b := hi ix2 in let c := lo iy2 in let d := hi iy2 in
  let zl := lo iz in let zu := hi iz in
  let base := andb (hi iz0 <? 0) (andb (ileb ix1 (Cx iy iz0))
                (andb (neb iz) (andb (neb ix2) (neb iy2)))) in
  andb base ((a <=? -1) && (b =? -1) && negb ((c <? 0) && (d <=? 0)) && (0 <? d) && (0 <=? c))%bool.

Definition info (ix1 iy iz0 : itv) : list Z :=
  let iz  := inter iz0 (fden ix1 iy iz0) in
  let ix2 := inter ix1 (Cx iy iz) in
  let iy2 := inter iy (Cy ix2 iz) in
  let X := Xlo (lo iy) (hi iy) (lo iz) (hi iz) in
  [lo ix1; hi ix1; lo iy; hi iy;
   lo ix2; hi ix2; lo iy2; hi iy2; lo iz; hi iz;
   X; (if (lo ix1 <? X) then 1 else 0) (* 1 if ix2 picks Xlo, 0 if picks lo ix1 *);
   Ylo (lo ix2) (hi ix2) (lo iz) (hi iz);
   (if (lo iy <=? lo ix2 * hi iz) then 1 else 0)].

Definition results : list (list Z) :=
  flat_map (fun a => flat_map (fun b => flat_map (fun c =>
     if active a b c then [info a b c] else []) itvs) itvs) itvs.

Compute results.
