From LalaInterval Require Import fdiv.
From LalaInterval Require Import optbase2.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* corner predicate *)
Definition corner (a b zl zu Y : Z) : Prop :=
  exists z, (z = zl \/ z = zu) /\ z <> 0 /\ a <= Z.div Y z <= b.

(* band membership -> corner, positive corner *)
Lemma band_pos : forall a b z Y, 0 < z -> a*z <= Y -> Y <= (b+1)*z - 1 -> a <= Z.div Y z <= b.
Proof.
  intros a b z Y Hz H1 H2. split.
  - apply Z.div_le_lower_bound; [lia|nia].
  - assert (Z.div Y z < b+1) by (apply Z.div_lt_upper_bound; [lia|nia]). lia.
Qed.

Lemma band_neg : forall a b z Y, z < 0 -> (b+1)*z + 1 <= Y -> Y <= a*z -> a <= Z.div Y z <= b.
Proof.
  intros a b z Y Hz H1 H2. split.
  - apply fdiv_lb_neg; [lia|nia].
  - assert (Z.div Y z < b+1) by (apply fdiv_lt_neg; [lia|nia]). lia.
Qed.
