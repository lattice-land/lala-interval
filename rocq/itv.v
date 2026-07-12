(** * Integer intervals

    Generic finite integer intervals and their basic lattice operations
    (membership, emptiness test, meet [inter] and join [ijoin]).  Extracted
    from [fdiv.v] so the interval infrastructure is self-contained and reusable;
    [fdiv.v] re-exports this module. *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Intervals and membership                                        *)
(* ------------------------------------------------------------------ *)

(** A (finite) interval is a pair of bounds; we work with finite bounds,
    which is what the top-level infinite-bound guard secures. *)
Record itv := Itv { lo : Z ; hi : Z }.

Definition mem (i : itv) (v : Z) : Prop := lo i <= v <= hi i.

Definition nonempty (i : itv) : Prop := lo i <= hi i.

Definition nonemptyb (i : itv) : bool := Z.leb (lo i) (hi i).

Lemma nonemptyb_true : forall i v, mem i v -> nonemptyb i = true.
Proof. intros i v Hm. unfold nonemptyb. apply Z.leb_le. unfold mem in Hm. lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** Meet (intersection) and join                                    *)
(* ------------------------------------------------------------------ *)

Definition inter (i j : itv) : itv := Itv (Z.max (lo i) (lo j)) (Z.min (hi i) (hi j)).
Lemma mem_inter : forall i j v, mem i v -> mem j v -> mem (inter i j) v.
Proof. intros i j v Hi Hj. unfold mem, inter in *; simpl in *. lia. Qed.

Definition ijoin (i j : itv) : itv :=
  Itv (Z.min (lo i) (lo j)) (Z.max (hi i) (hi j)).
Lemma in_store_ijoin_l : forall i j v, mem i v -> mem (ijoin i j) v.
Proof. intros i j v Hm. unfold mem, ijoin in *; simpl in *. lia. Qed.
Lemma in_store_ijoin_r : forall i j v, mem j v -> mem (ijoin i j) v.
Proof. intros i j v Hm. unfold mem, ijoin in *; simpl in *. lia. Qed.

(* ------------------------------------------------------------------ *)
(** ** Stores: a box is a triple of intervals                          *)
(* ------------------------------------------------------------------ *)

Record store := St { sx : itv ; sy : itv ; sz : itv }.

Definition in_store (s : store) (vx vy vz : Z) : Prop :=
  mem (sx s) vx /\ mem (sy s) vy /\ mem (sz s) vz.

Definition ne_store (s : store) : bool :=
  (nonemptyb (sx s) && nonemptyb (sy s) && nonemptyb (sz s))%bool.

Lemma ne_store_true : forall s vx vy vz, in_store s vx vy vz -> ne_store s = true.
Proof.
  intros s vx vy vz (Hx & Hy & Hz); unfold ne_store.
  rewrite (nonemptyb_true _ _ Hx), (nonemptyb_true _ _ Hy), (nonemptyb_true _ _ Hz).
  reflexivity.
Qed.

Definition sjoin (s t : store) : store :=
  St (ijoin (sx s) (sx t)) (ijoin (sy s) (sy t)) (ijoin (sz s) (sz t)).

Definition sqcupbot (s t : store) : store :=
  if ne_store s
  then (if ne_store t then sjoin s t else s)
  else t.

Lemma sqcupbot_pres_l : forall s t vx vy vz,
  in_store s vx vy vz -> in_store (sqcupbot s t) vx vy vz.
Proof.
  intros s t vx vy vz Hs.
  unfold sqcupbot.
  rewrite (ne_store_true _ _ _ _ Hs).
  destruct (ne_store t) eqn:Et.
  - destruct Hs as (Hx & Hy & Hz).
    repeat split; simpl; apply in_store_ijoin_l; assumption.
  - exact Hs.
Qed.

Lemma sqcupbot_pres_r : forall s t vx vy vz,
  in_store t vx vy vz -> in_store (sqcupbot s t) vx vy vz.
Proof.
  intros s t vx vy vz Ht.
  unfold sqcupbot.
  rewrite (ne_store_true _ _ _ _ Ht).
  destruct (ne_store s) eqn:Es; simpl.
  - destruct Ht as (Hx & Hy & Hz).
    repeat split; simpl; apply in_store_ijoin_r; assumption.
  - exact Ht.
Qed.
