From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* a := lo ix2, b := hi ix2, c := lo iy2, d := hi iy2, zl := lo iz, zu := hi iz.
   Each row corresponds to one leaf of [fden ix2 iy2 iz] returning a non-trivial
   interval; the conclusion is exactly the two (or one) inclusion facts needed
   for [ile iz (fden ix2 iy2 iz)]. *)

Section Rows.
Variables ix1 iy iz0 iz ix2 iy2 : itv.
Hypothesis Hz0 : 0 < lo iz0.
Hypothesis Ht  : ile ix1 (Cx iy iz0).
Hypothesis Diz : iz  = inter iz0 (fden ix1 iy iz0).
Hypothesis Dx2 : ix2 = inter ix1 (Cx iy iz).
Hypothesis Dy2 : iy2 = inter iy (Cy ix2 iz).
Hypothesis Nz  : lo iz <= hi iz.
Hypothesis Nx2 : lo ix2 <= hi ix2.
Hypothesis Ny2 : lo iy2 <= hi iy2.

(* 2a  P1 x P *)
Lemma zpos_2a : 0 < lo ix2 -> 0 <= lo iy2 -> 0 < hi iy2 ->
  Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= hi iy2 / lo ix2.
Admitted.

(* 2b  P1 x N *)
Lemma zpos_2b : 0 < lo ix2 -> hi iy2 < 0 -> lo iy2 <= 0 ->
  cdiv (lo iy2) (lo ix2) <= lo iz /\ hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1.
Admitted.

(* 2c  P1 x M/Z *)
Lemma zpos_2c : 0 < lo ix2 ->
  ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false ->
  ((hi iy2 <? 0) && (lo iy2 <=? 0))%bool = false ->
  cdiv (lo iy2) (lo ix2) <= lo iz /\ hi iz <= hi iy2 / lo ix2.
Admitted.

(* 3a  N'1 x P *)
Lemma zpos_3a : lo ix2 <= 0 -> hi ix2 < -1 -> 0 <= lo iy2 -> 0 < hi iy2 ->
  hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= lo iy2 / lo ix2.
Admitted.

(* 3b  N'1 x N *)
Lemma zpos_3b : lo ix2 <= 0 -> hi ix2 < -1 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  cdiv (hi iy2) (lo ix2) <= lo iz /\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1.
Admitted.

(* 3c  N'1 x M/Z *)
Lemma zpos_3c : lo ix2 <= 0 -> hi ix2 < -1 ->
  ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false ->
  ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false ->
  hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1.
Admitted.

(* 4a  Z (x=[0,0]), d<0 *)
Lemma zpos_4a : lo ix2 = 0 -> hi ix2 = 0 -> hi iy2 < 0 ->
  hi iz <= hi iy2 - 1.
Admitted.

(* 4b  Z (x=[0,0]), d>=0 *)
Lemma zpos_4b : lo ix2 = 0 -> hi ix2 = 0 -> 0 <= hi iy2 ->
  lo iy2 + 1 <= lo iz.
Admitted.

(* 5a  N'0,O (x=[a,-1], a<=-1) x N *)
Lemma zpos_5a : lo ix2 <= -1 -> hi ix2 = -1 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  cdiv (Z.min (-1) (hi iy2)) (lo ix2) <= lo iz.
Admitted.

(* 5b  N'0,O x P *)
Lemma zpos_5b : lo ix2 <= -1 -> hi ix2 = -1 ->
  ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false ->
  0 < hi iy2 -> 0 <= lo iy2 ->
  hi iz <= Z.max 1 (lo iy2) / lo ix2.
Admitted.

(* 5c  N'0,O x Z (y=[0,0]) : row returns bottom [1,0]; the hypotheses are
       inconsistent, so both inclusions hold vacuously. *)
Lemma zpos_5c : lo ix2 <= -1 -> hi ix2 = -1 ->
  ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false ->
  ((0 <? hi iy2) && (0 <=? lo iy2))%bool = false ->
  lo iy2 = 0 -> hi iy2 = 0 ->
  1 <= lo iz /\ hi iz <= 0.
Admitted.

(* 6a  P0 (x=[0,b], 0<b) x N *)
Lemma zpos_6a : lo ix2 = 0 -> 0 < hi ix2 -> lo iy2 < 0 -> hi iy2 <= 0 ->
  hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1.
Admitted.

(* 6b  P0 x P *)
Lemma zpos_6b : lo ix2 = 0 -> 0 < hi ix2 ->
  ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false ->
  0 < hi iy2 -> 0 <= lo iy2 ->
  Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz.
Admitted.

End Rows.
