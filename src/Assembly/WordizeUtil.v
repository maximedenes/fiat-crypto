Require Import Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec.
Require Import List Omega NArith Nnat BoolEq.
Require Import SetoidTactics.
Require Import ProofIrrelevance FunctionalExtensionality.
Require Import QhasmUtil QhasmEvalCommon.

Ltac shatter a :=
  let H := fresh in
  pose proof (shatter_word a) as H; simpl in H;
    try rewrite H in *; clear H.

Section Misc.
  Local Open Scope nword_scope.

  Lemma word_replace: forall n m, n = m -> word n = word m.
  Proof. intros; subst; intuition. Qed.

  Lemma of_nat_lt: forall x b, (x < b)%nat <-> (N.of_nat x < N.of_nat b)%N.
  Proof.
    intros x b; split; intro H.

    - unfold N.lt; rewrite N2Nat.inj_compare.
      repeat rewrite Nat2N.id.
      apply Nat.compare_lt_iff in H.
      intuition.

    - unfold N.lt in H; rewrite N2Nat.inj_compare in H.
      repeat rewrite Nat2N.id in H.
      apply Nat.compare_lt_iff in H.
      intuition.
  Qed.

  Lemma to_nat_lt: forall x b, (x < b)%N <-> (N.to_nat x < N.to_nat b)%nat.
  Proof.
    intros x b; split; intro H.

    - unfold N.lt in H; rewrite N2Nat.inj_compare in H.
      apply Nat.compare_lt_iff in H.
      intuition.

    - unfold N.lt; rewrite N2Nat.inj_compare.
      apply Nat.compare_lt_iff.
      intuition.
  Qed.

  Lemma word_size_bound : forall {n} (w: word n), (&w < Npow2 n)%N.
  Proof.
    intros; pose proof (wordToNat_bound w) as B;
      rewrite of_nat_lt in B;
      rewrite <- Npow2_nat in B;
      rewrite N2Nat.id in B;
      rewrite <- wordToN_nat in B;
      assumption.
  Qed.

  Lemma ge_to_le: forall (x y: N), (x >= y)%N <-> (y <= x)%N.
  Proof.
    intros x y; split; intro H;
      unfold N.ge, N.le in *;
      intro H0; contradict H;
      rewrite N.compare_antisym;
      rewrite H0; simpl; intuition.
  Qed.

  Lemma N_ge_0: forall x: N, (0 <= x)%N.
  Proof.
    intro x0; unfold N.le.
    pose proof (N.compare_0_r x0) as H.
    rewrite N.compare_antisym in H.
    induction x0; simpl in *;
      intro V; inversion V.
  Qed.

  Lemma Pos_ge_1: forall p, (1 <= N.pos p)%N.
  Proof.
    intro.
    replace (N.pos p) with (N.succ (N.pos p - 1)%N) by (
      induction p; simpl;
      try rewrite Pos.succ_pred_double;
      try reflexivity).
    unfold N.succ.
    apply N.le_pred_le_succ.
    replace (N.pred 1%N) with 0%N by (simpl; intuition).
    apply N_ge_0.
  Qed.

  Lemma testbit_wones_false: forall n k,
     (k >= N.of_nat n)%N
   -> false = N.testbit (& wones n) k.
  Proof.
    induction n; try abstract (simpl; intuition).
    induction k; try abstract (
      intro H; destruct H; simpl; intuition).

    intro H.
    assert (N.pos p - 1 >= N.of_nat n)%N as Z.
      apply ge_to_le;
      apply ge_to_le in H;
      apply (N.add_le_mono_r _ _ 1%N);
      replace (N.of_nat n + 1)%N with (N.of_nat (S n));
      replace (N.pos p - 1 + 1)%N with (N.pos p);
      try rewrite N.sub_add;
      try assumption;
      try nomega;
      apply Pos_ge_1.

    rewrite (IHn (N.pos p - 1)%N Z) at 1.

    assert (N.pos p = N.succ (N.pos p - 1)) as Hp by (
      rewrite <- N.pred_sub;
      rewrite N.succ_pred;
      try abstract intuition;
      intro H0; inversion H0).

    symmetry.
    rewrite Hp at 1.
    rewrite Hp in H.

    revert H; clear IHn Hp Z;
      generalize (N.pos p - 1)%N as x;
      intros x H.

    replace (& wones (S n)) with (2 * & (wones n) + N.b2n true)%N
      by (simpl; nomega).

    rewrite N.testbit_succ_r; reflexivity.
  Qed.

  Lemma testbit_wones_true: forall n k,
     (k < N.of_nat n)%N
   -> true = N.testbit (& wones n) k.
  Proof.
    induction n; intros k H; try nomega.
    destruct (N.eq_dec k (N.of_nat n)).

    - clear IHn H; subst.
      induction n.

      + simpl; intuition.

      + replace (& (wones (S (S n))))
           with (2 * (& (wones (S n))) + N.b2n true)%N
          by (simpl; nomega).
        rewrite Nat2N.inj_succ.
        rewrite N.testbit_succ_r.
        assumption.

    - induction k.

      + replace (& (wones (S n))) with (2 * (& (wones n)) + N.b2n true)%N
          by (simpl; nomega).
        rewrite N.testbit_0_r.
        reflexivity.

      + assert (N.pos p < N.of_nat n)%N as IH by (
          rewrite Nat2N.inj_succ in H;
          nomega).
        apply N.lt_lt_pred in IH.
        apply IHn in IH.
        replace (N.pos p) with (N.succ (N.pred (N.pos p))) by (
          induction p; simpl;
          try rewrite Pos.succ_pred_double;
          intuition).
        replace (& (wones (S n))) with (2 * (& (wones n)) + N.b2n true)%N
          by (simpl; nomega).
        rewrite N.testbit_succ_r.
        assumption.
  Qed.
End Misc.

Section Exp.
  Local Open Scope nword_scope.

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

  Lemma Npow2_gt0 : forall x, (0 < Npow2 x)%N.
  Proof.
    intros; induction x.

    - simpl; apply N.lt_1_r; intuition.

    - replace (Npow2 (S x)) with (2 * (Npow2 x))%N by intuition.
        apply (N.lt_0_mul 2 (Npow2 x)); left; split; apply N.neq_0_lt_0.

      + intuition; inversion H.

      + apply N.neq_0_lt_0 in IHx; intuition.
  Qed.

  Lemma Npow2_ge1 : forall x, (1 <= Npow2 x)%N.
  Proof.
    intro x.
    pose proof (Npow2_gt0 x) as Z.
    apply N.lt_pred_le; simpl.
    assumption.
  Qed.

  Lemma Npow2_split: forall a b,
    (Npow2 (a + b) = (Npow2 a) * (Npow2 b))%N.
  Proof.
    intros; revert a.
    induction b.

    - intros; simpl; replace (a + 0) with a; try nomega.
      rewrite N.mul_1_r; intuition.

    - intros.
      replace (a + S b) with (S a + b) by intuition.
      rewrite (IHb (S a)); simpl; clear IHb.
      induction (Npow2 a), (Npow2 b); simpl; intuition.
      rewrite Pos.mul_xO_r; intuition.
  Qed.

  Lemma Npow2_N: forall n, Npow2 n = (2 ^ N.of_nat n)%N.
  Proof.
    induction n.

    - simpl; intuition.

    - rewrite Nat2N.inj_succ.
      rewrite N.pow_succ_r; try apply N_ge_0.
      rewrite <- IHn.
      simpl; intuition.
  Qed.
 
  Lemma Npow2_succ: forall n, (Npow2 (S n) = 2 * (Npow2 n))%N.
  Proof. intros; simpl; induction (Npow2 n); intuition. Qed.

  Lemma Npow2_ordered: forall n m, (n <= m)%nat -> (Npow2 n <= Npow2 m)%N.
  Proof.
    induction n; intros m H; try rewrite Npow2_succ.

    - simpl; apply Npow2_ge1.

    - induction m; try rewrite Npow2_succ.

      + inversion H.

      + assert (n <= m)%nat as H0 by omega.
        apply IHn in H0.
        apply N.mul_le_mono_l.
        assumption.
  Qed.

End Exp.

Section Conversions.
  Local Open Scope nword_scope.

  Lemma NToWord_wordToN: forall sz x, NToWord sz (wordToN x) = x.
  Proof.
    intros.
    rewrite NToWord_nat.
    rewrite wordToN_nat.
    rewrite Nat2N.id.
    rewrite natToWord_wordToNat.
    intuition.
  Qed.

  Lemma NToWord_equal: forall n (x y: word n),
      wordToN x = wordToN y -> x = y.
  Proof.
    intros.
    rewrite <- (NToWord_wordToN _ x).
    rewrite <- (NToWord_wordToN _ y).
    rewrite H; reflexivity.
  Qed.

  Lemma wordToN_NToWord: forall sz x, (x < Npow2 sz)%N -> wordToN (NToWord sz x) = x.
  Proof.
    intros.
    rewrite NToWord_nat.
    rewrite wordToN_nat.
    rewrite <- (N2Nat.id x).
    apply Nat2N.inj_iff.
    rewrite Nat2N.id.
    apply natToWord_inj with (sz:=sz);
      try rewrite natToWord_wordToNat;
      intuition.

    - apply wordToNat_bound.
    - rewrite <- Npow2_nat; apply to_nat_lt; assumption.
  Qed.

  Lemma Npow2_ignore: forall {n} (x: word n),
    x = NToWord _ (& x + Npow2 n).
  Proof.
    intros.
    rewrite <- (NToWord_wordToN n x) at 1.
    repeat rewrite NToWord_nat.
    rewrite N2Nat.inj_add.
    rewrite Npow2_nat.
    replace (N.to_nat (&x))
       with ((N.to_nat (&x) + pow2 n) - 1 * pow2 n)
         at 1 by omega.
    rewrite drop_sub; intuition.
  Qed.
End Conversions.

Section Enumerability.
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
          destruct E as [g E]; destruct E as [d E].

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
End Enumerability.

Section SpecialFunctions.
  Local Open Scope nword_scope.

  Lemma convS_id: forall A x p, (@convS A A x p) = x.
  Proof.
    intros; unfold convS; vm_compute.
    replace p with (eq_refl A); intuition.
    apply proof_irrelevance.
  Qed.

  Lemma wordToN_convS: forall {n m} x p,
    wordToN (@convS (word n) (word m) x p) = wordToN x.
  Proof.
    intros.
    pose proof (word_equiv_correct _ _ p) as H.
    revert x p; rewrite H; intros.
    rewrite convS_id; reflexivity.
  Qed.

  Lemma wordToN_zext: forall {n m} (x: word n),
    wordToN (@zext n x m) = wordToN x.
  Proof.
    intros; induction x; simpl; intuition.

    - unfold zext, Word.combine.
      rewrite wordToN_nat.
      unfold wzero.
      rewrite (@wordToNat_natToWord_idempotent m 0); simpl; intuition.
      apply Npow2_gt0.

    - unfold zext in IHx; rewrite IHx; clear IHx;
        destruct b; intuition.
  Qed.

  Lemma wordToN_div2: forall {n} (x: word (S n)),
    N.div2 (&x) = & (wtl x).
  Proof.
    intros.
    pose proof (shatter_word x) as Hx; simpl in Hx; rewrite Hx; simpl.
    destruct (whd x).
    replace (match & wtl x with
             | 0%N => 0%N
             | N.pos q => N.pos (xO q)
             end)
       with (N.double (& (wtl x)))
         by (induction (& (wtl x)); simpl; intuition).

    - rewrite N.double_spec.
      replace (N.succ (2 * & wtl x))
         with ((2 * (& wtl x)) + 1)%N
           by nomega.
      rewrite <- N.succ_double_spec.
      rewrite N.div2_succ_double.
      reflexivity.

    - induction (& (wtl x)); simpl; intuition.
  Qed.

  Fixpoint wbit {n} (x: word n) (k: nat): bool :=
    match n as n' return word n' -> bool with
    | O => fun _ => false
    | S m => fun x' =>
      match k with
      | O => (whd x')
      | S k' => wbit (wtl x') k'
      end
    end x.

  Lemma wbit_wtl: forall {n} (x: word (S n)) k,
    wbit x (S k) = wbit (wtl x) k.
  Proof.
    intros.
    pose proof (shatter_word x) as Hx;
      simpl in Hx; rewrite Hx; simpl.
    reflexivity.
  Qed.

  Lemma wordToN_testbit: forall {n} (x: word n) k,
    N.testbit (& x) k = wbit x (N.to_nat k).
  Proof.
    assert (forall x: N, match x with
            | 0%N => 0%N
            | N.pos q => N.pos (q~0)%positive
            end = N.double x) as kill_match by (
      induction x; simpl; intuition).

    induction n; intros.

    - shatter x; simpl; intuition.

    - revert IHn; rewrite <- (N2Nat.id k).
      generalize (N.to_nat k) as k'; intros; clear k.
      rewrite Nat2N.id in *.

      induction k'.

      + clear IHn; induction x; simpl; intuition.
        destruct (& x), b; simpl; intuition. 

      + clear IHk'.
        shatter x; simpl.

        rewrite kill_match.
        replace (N.pos (Pos.of_succ_nat k'))
           with (N.succ (N.of_nat k'))
             by (rewrite <- Nat2N.inj_succ;
                 simpl; intuition).

        rewrite N.double_spec.
        replace (N.succ (2 * & wtl x))
           with (2 * & wtl x + 1)%N
             by nomega.

        destruct (whd x);
          try rewrite N.testbit_odd_succ;
          try rewrite N.testbit_even_succ;
          try abstract (
            unfold N.le; simpl;
            induction (N.of_nat k'); intuition;
            try inversion H);
          rewrite IHn;
          rewrite Nat2N.id;
          reflexivity.
  Qed.
 
  Lemma wordToN_split1: forall {n m} x,
    & (@split1 n m x) = N.land (& x) (& (wones n)).
  Proof.
    intros.

    pose proof (Word.combine_split _ _ x) as C; revert C.
    generalize (split1 n m x) as a, (split2 n m x) as b.
    intros a b C; rewrite <- C; clear C x.

    apply N.bits_inj_iff; unfold N.eqf; intro x.
    rewrite N.land_spec.
    repeat rewrite wordToN_testbit.
    revert x a b.

    induction n, m; intros;
      shatter a; shatter b;
      induction (N.to_nat x) as [|n0];
      try rewrite <- (Nat2N.id n0);
      try rewrite andb_false_r;
      try rewrite andb_true_r;
      simpl; intuition.
  Qed.

  Lemma wordToN_split2: forall {n m} x,
    & (@split2 n m x) = N.shiftr (& x) (N.of_nat n).
  Proof.
    intros.

    pose proof (Word.combine_split _ _ x) as C; revert C.
    generalize (split1 n m x) as a, (split2 n m x) as b.
    intros a b C.
    rewrite <- C; clear C x.

    apply N.bits_inj_iff; unfold N.eqf; intro x;
      rewrite N.shiftr_spec;
      repeat rewrite wordToN_testbit;
      try apply N_ge_0.

    revert x a b.
    induction n, m; intros;
      shatter a;
      try apply N_ge_0.

    - simpl; intuition.

    - replace (x + N.of_nat 0)%N with x by nomega.
      simpl; intuition.

    - rewrite (IHn x (wtl a) b).
      rewrite <- (N2Nat.id x).
      repeat rewrite <- Nat2N.inj_add.
      repeat rewrite Nat2N.id; simpl.
      replace (N.to_nat x + S n) with (S (N.to_nat x + n)) by omega.
      reflexivity.

    - rewrite (IHn x (wtl a) b).
      rewrite <- (N2Nat.id x).
      repeat rewrite <- Nat2N.inj_add.
      repeat rewrite Nat2N.id; simpl.
      replace (N.to_nat x + S n) with (S (N.to_nat x + n)) by omega.
      reflexivity.
  Qed.

  Lemma wordToN_combine: forall {n m} a b,
    & (@Word.combine n a m b) = N.lxor (N.shiftl (& b) (N.of_nat n)) (& a).
  Proof.
    intros; symmetry.

    replace a with (Word.split1 _ _ (Word.combine a b)) at 1
      by (apply Word.split1_combine).

    replace b with (Word.split2 _ _ (Word.combine a b)) at 1
      by (apply Word.split2_combine).

    generalize (Word.combine a b); intro x; clear a b.

    rewrite wordToN_split1, wordToN_split2.
    generalize (&x); clear x; intro x.
    apply N.bits_inj_iff; unfold N.eqf; intro k.

    rewrite N.lxor_spec.
    destruct (Nge_dec k (N.of_nat n)).

    - rewrite N.shiftl_spec_high; try apply N_ge_0;
        try (apply ge_to_le; assumption).
      rewrite N.shiftr_spec; try apply N_ge_0.
      replace (k - N.of_nat n + N.of_nat n)%N with k by nomega.
      rewrite N.land_spec.
      induction (N.testbit x k); 
        replace (N.testbit (& wones n) k) with false;
        simpl; intuition;
        try apply testbit_wones_false;
        try assumption.

    - rewrite N.shiftl_spec_low; try assumption; try apply N_ge_0.
      rewrite N.land_spec.
      induction (N.testbit x k);
        replace (N.testbit (& wones n) k) with true;
        simpl; intuition;
        try apply testbit_wones_true;
        try assumption.
  Qed.

  Lemma wordToN_wones: forall x, & (wones x) = N.ones (N.of_nat x).
  Proof.
    induction x.

    - simpl; intuition.

    - rewrite Nat2N.inj_succ.
      replace (& wones (S x)) with (2 * & (wones x) + N.b2n true)%N
        by (simpl; nomega).
      replace (N.ones (N.succ _))
         with (2 * N.ones (N.of_nat x) + N.b2n true)%N
           by (
        replace (N.succ (N.of_nat x)) with (1 + (N.of_nat x))%N by (
          rewrite N.add_comm; nomega);
        rewrite N.ones_add;
        replace (N.ones 1) with 1%N by (
          unfold N.ones; simpl; intuition);
        simpl; reflexivity).
 
      rewrite IHx.
      nomega.
  Qed.

  Ltac propagate_wordToN :=
    unfold extend, low, high, break;
    repeat match goal with
    | [|- context[@wordToN _ (@convS _ _ _ _)] ] =>
      rewrite wordToN_convS
    | [|- context[@wordToN _ (@split1 _ _ _)] ] =>
      rewrite wordToN_split1
    | [|- context[@wordToN _ (@split2 _ _ _)] ] =>
      rewrite wordToN_split2
    | [|- context[@wordToN _ (@combine _ _ _ _)] ] =>
      rewrite wordToN_combine
    | [|- context[@wordToN _ (@zext _ _ _)] ] =>
      rewrite wordToN_zext
    | [|- context[@wordToN _ (@wones _)] ] =>
      rewrite wordToN_wones
    end.

  Lemma break_spec: forall (m n: nat) (x: word n) low high,
      (low, high) = break m x
    -> &x = (&high * Npow2 m + &low)%N.
  Proof.
    intros m n x low high H.
    unfold break in H.
    destruct (le_dec m n).

    - inversion H; subst; clear H.
      propagate_wordToN.
      rewrite N.land_ones.
      rewrite N.shiftr_div_pow2.
      replace (n - (n - m)) with m by omega.
      rewrite N.mul_comm.
      rewrite Npow2_N.
      rewrite <- (N.div_mod' (& x) (2 ^ (N.of_nat m))%N).
      reflexivity.

    - inversion H; subst; clear H.
      propagate_wordToN; simpl; nomega.
  Qed.

  Lemma extend_bound: forall k n (p: (k <= n)%nat) (w: word k),
    (& (extend p w) < Npow2 k)%N.
  Proof.
    intros.
    propagate_wordToN.
    apply word_size_bound.
  Qed.

  Lemma mask_spec : forall (n: nat) (x: word n) m,
    & (mask (N.to_nat m) x) = (N.land (& x) (N.ones m)).
  Proof.
    intros; unfold mask.
    destruct (le_dec (N.to_nat m) n).

    - propagate_wordToN.
      rewrite N2Nat.id.
      reflexivity.
    
    - rewrite N.land_ones.
      rewrite N.mod_small; try reflexivity.
      rewrite <- (N2Nat.id m).
      rewrite <- Npow2_N.
      apply (N.lt_le_trans _ (Npow2 n) _); try apply word_size_bound.
      apply Npow2_ordered.
      omega.
  Qed.

  Lemma mask_bound : forall (n: nat) (x: word n) m,
    (& (mask m x) < Npow2 m)%N.
  Proof.
    intros; unfold mask.
    destruct (le_dec m n).

    - apply extend_bound.

    - apply (N.lt_le_trans _ (Npow2 n) _); try apply word_size_bound.
      apply Npow2_ordered.
      omega.
  Qed.

End SpecialFunctions.
