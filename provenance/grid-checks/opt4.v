From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition rng4 : list Z := (-4::-3::-2::-1::0::1::2::3::4::nil)%Z.
Definition itvs4 : list itv :=
  flat_map (fun a => map (fun b => Itv a b) (filter (fun b => a <=? b) rng4)) rng4.
Definition allstores4 : list store :=
  flat_map (fun ix => flat_map (fun iy => map (fun iz => St ix iy iz) itvs4) itvs4) itvs4.

Definition ieqb (i j : itv) : bool := andb (lo i =? lo j) (hi i =? hi j).
Definition seqb (u v : store) : bool :=
  andb (andb (ieqb (sx u) (sx v)) (ieqb (sy u) (sy v))) (ieqb (sz u) (sz v)).
Definition bott (i : itv) : bool := hi i <? lo i.
Definition consistent_b (s : store) : bool :=
  andb (andb (negb (bott (sx s))) (negb (bott (sy s)))) (negb (bott (sz s))).

Definition memb (i : itv) (v : Z) : bool := andb (lo i <=? v) (v <=? hi i).
Definition insol (s : store) (t : Z * Z * Z) : bool :=
  let '(x,y,z) := t in
  andb (andb (memb (sx s) x) (andb (memb (sy s) y) (memb (sz s) z)))
       (andb (negb (z =? 0)) (x =? Z.div y z)).
Definition triples4 : list (Z*Z*Z) :=
  flat_map (fun x => flat_map (fun y => map (fun z => (x,y,z)) rng4) rng4) rng4.
Definition sols (s : store) : list (Z*Z*Z) := filter (insol s) triples4.

Definition bbox (L : list (Z*Z*Z)) : option store :=
  match L with
  | [] => None
  | (x0,y0,z0) :: _ =>
      Some (St (Itv (fold_right (fun t m => let '(x,_,_):=t in Z.min x m) x0 L)
                    (fold_right (fun t m => let '(x,_,_):=t in Z.max x m) x0 L))
               (Itv (fold_right (fun t m => let '(_,y,_):=t in Z.min y m) y0 L)
                    (fold_right (fun t m => let '(_,y,_):=t in Z.max y m) y0 L))
               (Itv (fold_right (fun t m => let '(_,_,z):=t in Z.min z m) z0 L)
                    (fold_right (fun t m => let '(_,_,z):=t in Z.max z m) z0 L)))
  end.

Definition opt_ok (s : store) : bool :=
  match bbox (sols s) with
  | Some B => seqb (propagator s) B
  | None => negb (consistent_b (propagator s))
  end.

Theorem opt4_grid : forallb opt_ok allstores4 = true.
Proof. vm_compute. reflexivity. Qed.
