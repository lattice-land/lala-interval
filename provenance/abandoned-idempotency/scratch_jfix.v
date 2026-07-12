From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import List. Import ListNotations.
Open Scope Z_scope.

Definition Jfix_ok (s : store) : bool :=
  implb (consistent_b (propagator s)) (seqb (J (propagator s)) (propagator s)).

Theorem Jfix_grid : forallb Jfix_ok allstores = true.
Proof. vm_compute. reflexivity. Qed.
