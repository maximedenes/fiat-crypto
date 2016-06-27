Require Import Bedrock.Word Bedrock.Nomega.
Require Import List Omega NArith Nnat BoolEq.

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
Proof.
  intros.
  rewrite <- Npow2_nat in H.
  unfold N.lt.
  rewrite N2Nat.inj_compare.
  rewrite Nat2N.id.
  apply Nat.compare_lt_iff in H.
  assumption.
Qed.

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

      pose proof (ncorrect (WS true x)) as ncorrect'; clear ncorrect.

      revert ncorrect'; revert x H; revert l1 l2; induction nelem; intros.

      - inversion ncorrect'.

      - destruct ncorrect'; subst.

        + simpl in H.
          destruct (partition (whd (sz:=n)) nelem) as [g d].
          inversion H.
          intuition.

        + simpl in H; destruct (whd a); simpl in H;
            destruct (partition (whd (sz:=n)) nelem) as [g d];
            inversion H; subst; clear H.

          * right; apply (IHnelem g l2); intuition.

          * apply (IHnelem l1 d); intuition.
    }

    assert (forall x : word n, In x (map (split2 1 n) l2))
        as ncorrect2. {
      intro. clear ngood IHn ncorrect1.

      replace x with (split2 1 n (WS false x)) by (simpl; intuition).
      apply in_map.

      pose proof (ncorrect (WS false x)) as ncorrect'; clear ncorrect.

      revert ncorrect'; revert x H; revert l1 l2; induction nelem; intros.

      - inversion ncorrect'.

      - destruct ncorrect'; subst.

        + simpl in H.
          destruct (partition (whd (sz:=n)) nelem) as [g d].
          inversion H.
          intuition.

        + simpl in H; destruct (whd a); simpl in H;
            destruct (partition (whd (sz:=n)) nelem) as [g d];
            inversion H; subst; clear H.

          * apply (IHnelem g); intuition.

          * right; apply (IHnelem l1); intuition.
    }

    assert (NoDup (map (split2 1 n) l1)) as ngood1. {
      clear ncorrect1 ncorrect2 IHn ncorrect.
      revert ngood H; revert l1 l2; induction nelem; intros.

      - simpl in H; inversion H; subst; clear H.
        simpl; constructor.

      - inversion ngood; subst; clear ngood.

        assert (exists g d, partition (@whd n) nelem = (g, d)) as E by (
            destruct (partition _ _) as [g d]; exists g; exists d; intuition);
          destruct E as [g E];
          destruct E as [d E].

        pose proof (elements_in_partition _ _ E) as I.

        destruct (shatter_word_S a) as [b Q].
        destruct Q as [a' Ha].
        rewrite Ha in *; simpl in H.

        simpl in H; destruct b; rewrite E in *;
          inversion H; subst; clear H.

        + constructor. 

          * intro H; clear IHnelem.

            pose proof (@in_map_iff (word (S n)) (word n) (@wtl n) g a') as M.
            apply M in H; clear M; destruct H; destruct H as [Ha Hb].
            assert (whd x = true) as Hhd. {
              clear I H2 H3 Ha a'.
              destruct (shatter_word_S x) as [b H];
                destruct H as [x' H]; rewrite H in *; clear H x; simpl.

              revert Hb E. revert x' b g l2.
              induction nelem; intros; simpl in E.

              - inversion E; subst.
                inversion Hb.

              - simpl in E;
                  destruct (bool_dec (whd a) true) as [B|B];
                  destruct (partition (whd (sz:=n)) nelem) as [g' d'].

                + rewrite B in E; inversion E; subst; clear E;
                    destruct Hb.

                  * rewrite H in *; simpl in B; intuition.

                  * apply (IHnelem x' b g' l2); intuition.

                + assert (whd a = false) as B' by (
                      induction (whd a); intuition); clear B.
                  rewrite B' in E. inversion E. subst. clear E.
                  apply (IHnelem x' b g d'); intuition.
            }

            destruct (shatter_word_S x) as [b H].
            destruct H as [x' H].
            rewrite H in *; simpl in *; clear H.
            rewrite Hhd in Hb.
            rewrite Ha in Hb.
            assert (In (a'~1) g \/ In (a'~1) l2) as Q by intuition.
            apply I in Q.
            intuition.

          * apply (IHnelem g l2); intuition.

        + apply (IHnelem _ d); intuition.
    }

    assert (NoDup (map (split2 1 n) l2)) as ngood2. {
      clear ncorrect1 ncorrect2 IHn ncorrect ngood1.
      revert ngood H; revert l1 l2; induction nelem; intros.

      - simpl in H; inversion H; subst; clear H.
        simpl; constructor.

      - inversion ngood; subst; clear ngood.

        assert (exists g d, partition (@whd n) nelem = (g, d)) as E by (
            destruct (partition _ _) as [g d]; exists g; exists d; intuition);
          destruct E as [g E];
          destruct E as [d E].

        pose proof (elements_in_partition _ _ E) as I.

        destruct (shatter_word_S a) as [b Q].
        destruct Q as [a' Ha].
        rewrite Ha in *; simpl in H.

        simpl in H; destruct b; rewrite E in *;
          inversion H; subst; clear H.

        + apply (IHnelem g l2); intuition.

        + constructor. 

          * intro H; clear IHnelem.

            pose proof (@in_map_iff (word (S n)) (word n) (@wtl n) d a') as M.
            apply M in H; clear M; destruct H; destruct H as [Ha Hb].
            assert (whd x = false) as Hhd. {
              clear I H2 H3 Ha a'.
              destruct (shatter_word_S x) as [b H];
                destruct H as [x' H]; rewrite H in *; clear H x; simpl.

              revert Hb E. revert x' b d l1.
              induction nelem; intros; simpl in E.

              - inversion E; subst.
                inversion Hb.

              - simpl in E;
                  destruct (bool_dec (whd a) false) as [B|B];
                  destruct (partition (whd (sz:=n)) nelem) as [g' d'].

                + rewrite B in E; inversion E; subst; clear E;
                    destruct Hb.

                  * rewrite H in *; simpl in B; intuition.

                  * apply (IHnelem x' b d' l1); intuition.

                + assert (whd a = true) as B' by (
                      induction (whd a); intuition); clear B.
                  rewrite B' in E. inversion E. subst. clear E.
                  apply (IHnelem x' b d g'); intuition.
            }

            destruct (shatter_word_S x) as [b H].
            destruct H as [x' H].
            rewrite H in *; simpl in *; clear H.
            rewrite Hhd in Hb.
            rewrite Ha in Hb.
            assert (In (a'~0) l1 \/ In (a'~0) d) as Q by intuition.
            apply I in Q.
            intuition.

          * apply (IHnelem l1 d); intuition.
    }

    pose proof (IHn _ ncorrect1 ngood1) as H1;
      unfold elements in H1; rewrite map_length in H1.

    pose proof (IHn _ ncorrect2 ngood2) as H2;
      unfold elements in H2; rewrite map_length in H2.

    rewrite (partition_length _ _ H); simpl in *.
    rewrite H1, H2.
    omega.
Qed.

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
