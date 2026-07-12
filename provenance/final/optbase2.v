From LalaInterval Require Import fdiv.
From LalaInterval Require Export optbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Lemma ile_refl : forall i, ile i i.
Proof. intro i; unfold ile; lia. Qed.
Lemma ile_trans : forall i j k, ile i j -> ile j k -> ile i k.
Proof. unfold ile; intros i j k [??] [??]; lia. Qed.
Lemma inter_ile_l : forall i j, ile (inter i j) i.
Proof. intros i j; unfold ile, inter; cbn [lo hi]; lia. Qed.
Lemma ijoin_ile : forall i j k, ile i k -> ile j k -> ile (ijoin i j) k.
Proof. unfold ile, ijoin; cbn [lo hi]; intros i j k [??] [??]; lia. Qed.
Lemma sle_trans : forall a b c, sle a b -> sle b c -> sle a c.
Proof.
  unfold sle; intros a b c [Hx [Hy Hz]] [Hx' [Hy' Hz']];
  split; [|split]; eapply ile_trans; eassumption.
Qed.

Lemma restrict_z_pos_ile : forall t, sle (restrict_z_pos t) t.
Proof.
  intro t; unfold restrict_z_pos, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply ile_refl | apply inter_ile_l]].
Qed.
Lemma restrict_z_neg_ile : forall t, sle (restrict_z_neg t) t.
Proof.
  intro t; unfold restrict_z_neg, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply ile_refl | apply inter_ile_l]].
Qed.
Lemma fdivxz_pos_ile : forall w, sle (fdivxz_pos w) w.
Proof.
  intro w. unfold fdivxz_pos; cbv zeta; unfold sle; cbn [sx sy sz].
  split; [ eapply ile_trans; apply inter_ile_l
         | split; [apply ile_refl | apply inter_ile_l] ].
Qed.
Lemma fdivxz_neg_ile : forall w, sle (fdivxz_neg w) w.
Proof.
  intro w. unfold fdivxz_neg; cbv zeta; unfold sle; cbn [sx sy sz].
  split; [ eapply ile_trans; apply inter_ile_l
         | split; [apply ile_refl | apply inter_ile_l] ].
Qed.
Lemma refine_y_ile : forall w, sle (refine_y w) w.
Proof.
  intro w; unfold refine_y, sle; cbn [sx sy sz].
  split; [apply ile_refl | split; [apply inter_ile_l | apply ile_refl]].
Qed.
Lemma sqcupbot_ile : forall a b t, sle a t -> sle b t -> sle (sqcupbot a b) t.
Proof.
  intros a b t Ha Hb. unfold sqcupbot.
  destruct (ne_store a), (ne_store b); cbn iota; try assumption.
  unfold sjoin, sle in *; cbn [sx sy sz].
  destruct Ha as [Hax [Hay Haz]]; destruct Hb as [Hbx [Hby Hbz]].
  split; [|split]; apply ijoin_ile; assumption.
Qed.

Theorem propagator_reductive : forall s, sle (propagator s) s.
Proof.
  intro s. unfold propagator.
  eapply sle_trans; [apply refine_y_ile|].
  apply sqcupbot_ile.
  - eapply sle_trans; [apply fdivxz_neg_ile | apply restrict_z_neg_ile].
  - eapply sle_trans; [apply fdivxz_pos_ile | apply restrict_z_pos_ile].
Qed.
