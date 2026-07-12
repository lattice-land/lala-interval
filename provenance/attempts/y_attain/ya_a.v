From LalaInterval Require Import fdiv.
From LalaInterval Require Import idem.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ================================================================= *)
(*  Numerator "band" membership: if Y lies in the pre-image band of  *)
(*  the quotient window [a,b] for divisor z, then a <= Y/z <= b.      *)
(* ================================================================= *)

Lemma num_in_band_pos : forall a b z Y,
  0 < z -> a * z <= Y -> Y <= (b+1)*z - 1 -> a <= Y / z <= b.
Proof.
  intros a b z Y Hz Hlo Hhi. split.
  - apply Z.div_le_lower_bound; [lia | nia].
  - assert (Y / z < b + 1) by (apply Z.div_lt_upper_bound; [lia | nia]). lia.
Qed.

Lemma num_in_band_neg : forall a b z Y,
  z < 0 -> (b+1)*z + 1 <= Y -> Y <= a * z -> a <= Y / z <= b.
Proof.
  intros a b z Y Hz Hlo Hhi. split.
  - apply fdiv_lb_neg; [lia | nia].
  - assert (Y / z < b + 1) by (apply fdiv_lt_neg; [lia | nia]). lia.
Qed.

(* ================================================================= *)
(*  Corner selection for the HI y-bound.                             *)
(* ================================================================= *)

Lemma pick_hi : forall a b zl zu Y,
  a <= b -> zl <= zu -> zl <> 0 -> zu <> 0 ->
  Y <= Yhi a b zl zu ->
  (0 < zu -> a*zu <= Y) ->
  (0 < zl -> a*zl <= Y) ->
  (zl < 0 -> (b+1)*zl + 1 <= Y) ->
  (zu < 0 -> (b+1)*zu + 1 <= Y) ->
  exists z, zl <= z <= zu /\ z <> 0 /\ a <= Y / z <= b.
Proof.
  intros a b zl zu Y Hab Hz Hzl0 Hzu0 HY L1 L2 L3 L4.
  unfold Yhi in HY.
  destruct (Z.max_spec (Z.max (a*zl) (a*zu)) (Z.max ((b+1)*zl-1) ((b+1)*zu-1)))
    as [[_ E]|[_ E]]; rewrite E in HY.
  - (* Yhi from (b+1)*_-1 forms *)
    destruct (Z.max_spec ((b+1)*zl-1) ((b+1)*zu-1)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + (* zu form *)
      exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply num_in_band_pos; [lia | apply L1; lia | lia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | apply L4; lia | nia].
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply num_in_band_pos; [lia | apply L2; lia | lia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | apply L3; lia | nia].
  - (* Yhi from a*_ forms *)
    destruct (Z.max_spec (a*zl) (a*zu)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply num_in_band_pos; [lia | apply L1; lia | nia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | apply L4; lia | lia].
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply num_in_band_pos; [lia | apply L2; lia | nia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | apply L3; lia | lia].
Qed.

(* ================================================================= *)
(*  Corner selection for the LO y-bound.                            *)
(* ================================================================= *)

Lemma pick_lo : forall a b zl zu Y,
  a <= b -> zl <= zu -> zl <> 0 -> zu <> 0 ->
  Ylo a b zl zu <= Y ->
  (0 < zu -> Y <= (b+1)*zu - 1) ->
  (0 < zl -> Y <= (b+1)*zl - 1) ->
  (zl < 0 -> Y <= a*zl) ->
  (zu < 0 -> Y <= a*zu) ->
  exists z, zl <= z <= zu /\ z <> 0 /\ a <= Y / z <= b.
Proof.
  intros a b zl zu Y Hab Hz Hzl0 Hzu0 HY U1 U2 U3 U4.
  unfold Ylo in HY.
  destruct (Z.min_spec (Z.min (a*zl) (a*zu)) (Z.min ((b+1)*zl+1) ((b+1)*zu+1)))
    as [[_ E]|[_ E]]; rewrite E in HY.
  - (* Ylo from a*_ forms *)
    destruct (Z.min_spec (a*zl) (a*zu)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply num_in_band_pos; [lia | lia | apply U2; lia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | nia | apply U3; lia].
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply num_in_band_pos; [lia | lia | apply U1; lia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | nia | apply U4; lia].
  - (* Ylo from (b+1)*_+1 forms *)
    destruct (Z.min_spec ((b+1)*zl+1) ((b+1)*zu+1)) as [[_ E2]|[_ E2]]; rewrite E2 in HY.
    + exists zl. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zl) as [Hp|Hn].
      * apply num_in_band_pos; [lia | nia | apply U2; lia].
      * assert (zl < 0) by lia.
        apply num_in_band_neg; [lia | lia | apply U3; lia].
    + exists zu. split; [lia|]. split; [lia|].
      destruct (Z_lt_le_dec 0 zu) as [Hp|Hn].
      * apply num_in_band_pos; [lia | nia | apply U1; lia].
      * assert (zu < 0) by lia.
        apply num_in_band_neg; [lia | lia | apply U4; lia].
Qed.
