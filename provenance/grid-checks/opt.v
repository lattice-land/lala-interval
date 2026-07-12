From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition memb (i : itv) (v : Z) : bool := andb (lo i <=? v) (v <=? hi i).
Definition insol (s : store) (t : Z * Z * Z) : bool :=
  let '(x,y,z) := t in
  andb (andb (memb (sx s) x) (andb (memb (sy s) y) (memb (sz s) z)))
       (andb (negb (z =? 0)) (x =? Z.div y z)).
Definition triples : list (Z*Z*Z) :=
  flat_map (fun x => flat_map (fun y => map (fun z => (x,y,z)) rng) rng) rng.
Definition sols (s : store) : list (Z*Z*Z) := filter (insol s) triples.

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

(* optimality on stores that HAVE solutions: propagator = tightest box of solutions. *)
Definition opt_ok (s : store) : bool :=
  match bbox (sols s) with
  | Some B => seqb (propagator s) B
  | None => true   (* no-solution case handled separately below *)
  end.

(* infeasibility detection: no solutions => propagator output is bottom (inconsistent). *)
Definition infeas_ok (s : store) : bool :=
  match sols s with
  | [] => negb (consistent_b (propagator s))
  | _ => true
  end.

Theorem opt_grid : forallb opt_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.

Theorem infeas_grid : forallb infeas_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
