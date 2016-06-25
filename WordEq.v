Require Import Bedrock.Word Bedrock.Nomega.
Require Import List Omega NArith Nnat.

Lemma word_replace: forall n m, n = m -> word n = word m.
Proof. intros; subst; intuition. Qed.

Lemma pow2_inv : forall n m, pow2 n = pow2 m -> n = m.
Proof.
  induction n; intros; simpl in *;
    induction m; simpl in *; intuition.
Qed.

Lemma pow2_gt0 : forall n, (pow2 n > O)%nat.
Proof. induction n; simpl; omega. Qed.

Lemma pow2_N_bound: forall n j,
  (j < pow2 n)%nat -> (N.of_nat j < Npow2 n)%N.
Proof. Admitted.

Class Enumerable A := {
  elements : list A;
  correct : forall x: A, In x elements;
  good: NoDup elements;
}.

Arguments elements _ {_}.

Definition word_elements (n: nat): list (word n) :=
  map (natToWord n) (seq O (pow2 n)).

Lemma word_index_correct : forall n (x: word n),
  x = nth (wordToNat x) (word_elements n) (natToWord _ 0).
Proof.
  intros; unfold word_elements.
  rewrite map_nth.
  rewrite seq_nth; try apply wordToNat_bound; simpl.
  rewrite natToWord_wordToNat.
  reflexivity.
Qed.

Lemma word_elements_correct: forall n (x: word n),
    In x (word_elements n).
Proof.
  intros; unfold word_elements.
  destruct (nth_in_or_default (wordToNat x) (word_elements n) (natToWord _ 0)).

  - rewrite <- word_index_correct in i.
    assumption.

  - rewrite <- word_index_correct in e.
    apply in_map_iff.
    exists 0; split; simpl; intuition.
    apply in_seq.
    pose proof (pow2_gt0 n).
    omega.
Qed.

Lemma word_elements_good: forall n, NoDup (word_elements n).
Proof.
  intros; unfold word_elements.

  apply <- (NoDup_nth (map (natToWord n) (seq 0 (pow2 n))) (natToWord _ 0)).

  intros; repeat rewrite map_nth in H1.

  rewrite map_length in H, H0.
  rewrite seq_length in H, H0.

  replace (nth i (seq 0 (pow2 n)) 0) with i in H1
    by (rewrite seq_nth; simpl; intuition).
  replace (nth j (seq 0 (pow2 n)) 0) with j in H1
    by (rewrite seq_nth; simpl; intuition).

  rewrite <- (@wordToNat_natToWord_idempotent n i);
    try apply pow2_N_bound; intuition
  rewrite <- (@wordToNat_natToWord_idempotent n j);
    try apply pow2_N_bound; intuition
  rewrite H1; intuition.

Qed.

Instance word_enumerable: forall n, Enumerable (word n) := {
  elements := word_elements n;
  correct := word_elements_correct n;
  good := word_elements_good n
}.

Lemma word_enum_correct: forall n e, length (@elements (word n) e) = pow2 n.
Proof.
  intros.
  destruct e as [nelem ncorrect ngood].
  induction n.

  - simpl; inversion ngood.

    + rewrite <- H in ncorrect.
      pose proof (ncorrect WO).
      inversion H0.

    + rewrite (shatter_word_0 x) in *.
      destruct (list_eq_dec (@weq 0) l nil); subst; intuition.
      contradict H.
      induction l.

      * apply n; intuition.

      * rewrite (shatter_word_0 a).
        intuition.

  - replace (pow2 (S n)) with (2 * pow2 n) by (simpl; intuition).
    unfold elements; cbv zeta.

    assert (exists l1 l2, partition (@whd _) nelem = (l1, l2)) as H by (
      destruct (partition (@whd _) nelem) as [l l0];
      exists l; exists l0; intuition).

    destruct H as [l1 H].
    destruct H as [l2 H].

    assert (forall x : word n, In x (map (split2 1 n) l1))
        as ncorrect1. {
      intro. clear ngood IHn.

      replace x with (split2 1 n (WS true x)) by (simpl; intuition).
      apply in_map.

      revert x H; revert l1 l2; induction nelem; intros l1 l2 x H.

      + pose proof (ncorrect (wzero _)) as Z; simpl in Z; inversion Z.

      + admit.
    }

    assert (forall x : word n, In x (map (split2 1 n) l2))
        as ncorrect2. {
      intro. clear ngood IHn.

      replace x with (split2 1 n (WS false x)) by (simpl; intuition).
      apply in_map.
      revert x H ncorrect1; revert l1 l2; induction nelem; intros l1 l2 x H.

      + pose proof (ncorrect (wzero _)) as Z; simpl in Z; inversion Z.

      + admit.
    }

    assert (NoDup (map (split2 1 n) l1)) as ngood1. {
      admit.
    }

    assert (NoDup (map (split2 1 n) l2)) as ngood2. {
      admit.
    }

    pose proof (IHn _ ncorrect1 ngood1) as H1;
      unfold elements in H1; rewrite map_length in H1.

    pose proof (IHn _ ncorrect2 ngood2) as H2;
      unfold elements in H2; rewrite map_length in H2.

    rewrite (partition_length _ _ H); simpl in *.
    rewrite H1, H2.
    omega.
Admitted.

Lemma word_equiv_correct: forall n m, word n = word m -> n = m.
Proof.
  intros n m H.
  apply pow2_inv.

  pose proof (word_enum_correct n) as Hn.
  pose proof (word_enum_correct m) as Hm.

  rewrite H in Hn.
  rewrite <- (Hn (word_enumerable m)).
  rewrite <- (Hm (word_enumerable m)).

  reflexivity.
Qed.
