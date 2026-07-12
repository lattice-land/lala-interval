From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition memb (i : itv) (v : Z) : bool := andb (lo i <=? v) (v <=? hi i).
(* solution (vx,y,z) inside store w, for some y,z *)
Definition att_x (w : store) (vx : Z) : bool :=
  andb (memb (sx w) vx)
       (existsb (fun y => existsb (fun z =>
          andb (memb (sy w) y) (andb (memb (sz w) z)
               (andb (negb (z =? 0)) (vx =? Z.div y z)))) rng) rng).
Definition att_z (w : store) (vz : Z) : bool :=
  andb (memb (sz w) vz)
       (existsb (fun x => existsb (fun y =>
          andb (memb (sx w) x) (andb (memb (sy w) y)
               (andb (negb (vz =? 0)) (x =? Z.div y vz)))) rng) rng).

Definition consistent_b (s : store) : bool :=
  andb (andb (lo (sx s) <=? hi (sx s)) (lo (sy s) <=? hi (sy s))) (lo (sz s) <=? hi (sz s)).
Definition signdef (w : store) : bool := orb (0 <? lo (sz w)) (hi (sz w) <? 0).

(* Branch x,z optimality: for a sign-definite w with consistent F(w), the x and z
   bounds of F(w) are attained by solutions inside w. *)
Definition branch_ok (w : store) : bool :=
  let f := fdivxz_pos w in
  implb (andb (signdef w) (consistent_b f))
        (andb (andb (att_x w (lo (sx f))) (att_x w (hi (sx f))))
              (andb (att_z w (lo (sz f))) (att_z w (hi (sz f))))).

Theorem branch_grid : forallb branch_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
