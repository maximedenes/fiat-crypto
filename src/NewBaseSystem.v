Require Import Crypto.Util.Tactics Crypto.Util.Decidable Crypto.Util.LetIn.

Require Import ZArith Nsatz Psatz Coq.omega.Omega.
Require Import Coq.ZArith.BinIntDef. Local Open Scope Z_scope.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil.

Require Import Coq.Lists.List. Import ListNotations.
Require Crypto.Util.Tuple. Local Notation tuple := Tuple.tuple.
Require Import Recdef.

    (* TODO: move *)
    Lemma fst_pair {A B} (a:A) (b:B) : fst (a,b) = a. reflexivity. Qed.
    Lemma snd_pair {A B} (a:A) (b:B) : snd (a,b) = b. reflexivity. Qed.
    Create HintDb cancel_pair discriminated. Hint Rewrite @fst_pair @snd_pair : cancel_pair.

    (* TODO: move to ListUtil *)
    Lemma update_nth_id {T} i (xs:list T) : ListUtil.update_nth i id xs = xs.
    Proof.
      revert xs; induction i; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma map_fst_combine {A B} (xs:list A) (ys:list B) : List.map fst (List.combine xs ys) = List.firstn (length ys) xs.
    Proof.
      revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma map_snd_combine {A B} (xs:list A) (ys:list B) : List.map snd (List.combine xs ys) = List.firstn (length xs) ys.
    Proof.
      revert xs; induction ys; destruct xs; simpl; solve [ trivial | congruence ].
    Qed.

    Lemma nth_default_seq_inbouns d s n i (H:(i < n)%nat) :
      List.nth_default d (List.seq s n) i = (s+i)%nat.
    Proof.
      progress cbv [List.nth_default].
      rewrite ListUtil.nth_error_seq.
      break_innermost_match; solve [ trivial | omega ].
    Qed.
    
    Lemma mod_add_mul_full a b c k m : m <> 0 -> c mod m = k mod m -> 
                                    (a + b * c) mod m = (a + b * k) mod m.
    Proof.
      intros; rewrite Z.add_mod, Z.mul_mod by auto.
      match goal with H : _ mod _ = _ mod _ |- _ => rewrite H end.
      rewrite <-Z.mul_mod, <-Z.add_mod by auto; reflexivity.
    Qed.
    
    Fixpoint find_remove_first' {A} (f : A->bool) (acc ls:list A) : (option A) * list A :=
      (match ls with
      | nil => (None, acc)
      | x :: tl =>
        if f x then (Some x, acc ++ tl) else find_remove_first' f (acc ++ x::nil) tl
      end)%list.
    
    Definition find_remove_first {A} (f:A -> bool) ls : (option A) * list A :=
      find_remove_first' f nil ls.

    Lemma find_remove_first_cons {A} f (x:A) tl : f x = true ->
      find_remove_first f (x::tl) = (Some x, tl).
    Proof. intros; cbv [find_remove_first]. simpl find_remove_first'.
           break_if; try congruence; reflexivity. Qed.

    Lemma find_remove_first'_None {A} (f:A->bool) ls : forall acc,
      fst (find_remove_first' f acc ls) = None ->
      forall x, List.In x ls -> f x = false.
    Proof.
      induction ls; simpl find_remove_first'; simpl List.In; [tauto|].
      break_if; intros; [discriminate|].
      destruct H0; subst; auto; eapply IHls; eauto.
    Qed.
    Lemma find_remove_first_None {A} (f:A->bool) ls :
      fst (find_remove_first f ls) = None ->
      forall x, List.In x ls -> f x = false.
    Proof. cbv [find_remove_first]. apply find_remove_first'_None. Qed.

    Lemma length_find_remove_first' {A} (f:A -> bool) ls : forall acc,
      length (snd (@find_remove_first' _ f acc ls)) =
        match (fst (@find_remove_first' _ f acc ls)) with
        | None => length (acc ++ ls)
        | Some _ => (length (acc ++ ls) - 1)%nat
        end.
    Proof.
      induction ls; intros; simpl find_remove_first';
        repeat match goal with
               | |- _ => break_match; try discriminate
               | |- _ => progress (rewrite ?@fst_pair, ?@snd_pair in * )
               | |- _ => progress distr_length
               | |- _ => rewrite IHls
               end.
    Qed.

    Lemma length_find_remove_first {A} (f:A -> bool) ls :
      length (snd (find_remove_first f ls)) =
        match (fst (find_remove_first f ls)) with
        | None => length ls
        | Some _ => (length ls - 1)%nat
        end.
    Proof. cbv [find_remove_first]; rewrite length_find_remove_first'; distr_length. Qed. Hint Rewrite @length_find_remove_first : distr_length.

    Lemma to_nat_neg : forall x, x < 0 -> Z.to_nat x = 0%nat.
    Proof. destruct x; try reflexivity; intros. pose proof (Pos2Z.is_pos p). omega. Qed.

Delimit Scope runtime_scope with RT.
Definition runtime_mul := Z.mul. Global Infix "*" := runtime_mul : runtime_scope.
Definition runtime_add := Z.add. Global Infix "+" := runtime_add : runtime_scope. 
Definition runtime_div := Z.div. Global Infix "/" := runtime_div : runtime_scope. 
Definition runtime_modulo := Z.modulo. Global Infix "mod" := runtime_modulo : runtime_scope.
Definition runtime_fst {A B} := @fst A B.
Definition runtime_snd {A B} := @snd A B.

Module B.
  Let limb := (Z*Z)%type. (* position coefficient and run-time value *)
  Module Associational.
    Definition eval (p:list limb) : Z :=
      List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p).
    
    Lemma eval_nil : eval nil = 0. Proof. reflexivity. Qed.
    Lemma eval_cons p q : eval (p::q) = (fst p) * (snd p) + eval q. Proof. reflexivity. Qed.
    Lemma eval_app p q: eval (p++q) = eval p + eval q.
    Proof. induction p; simpl eval; rewrite ?eval_nil, ?eval_cons; nsatz. Qed.
    Create HintDb push_eval discriminated. Hint Rewrite eval_nil eval_cons eval_app : push_eval.

    Definition mul (p q:list limb) : list limb :=
      List.flat_map (fun t => List.map (fun t' => (fst t * fst t', (snd t * snd t')%RT)) q) p.
    Lemma eval_map_mul a x q : eval (List.map (fun t => (a * fst t, x * snd t)) q) = a * x * eval q.
    Proof. induction q; simpl List.map; autorewrite with push_eval cancel_pair; nsatz. Qed.
    Hint Rewrite eval_map_mul : push_eval.
    Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
    Proof. induction p; simpl mul; autorewrite with push_eval cancel_pair; try nsatz. Qed.
    Hint Rewrite eval_mul : push_eval.

    Fixpoint split (s:Z) (xs:list limb) : list limb * list limb :=
      match xs with
      | nil => (nil, nil)
      | cons x xs' =>
        let sxs' := split s xs' in
        if dec (fst x mod s = 0)
        then (fst sxs',          cons (fst x / s, snd x) (snd sxs'))
        else (cons x (fst sxs'), snd sxs')
      end.

    Lemma eval_split s p (s_nonzero:s<>0) :
      eval (fst (split s p)) + s * eval (snd (split s p)) = eval p.
    Proof. induction p;
             repeat match goal with
                    | _ => progress simpl split
                    | _ => progress autorewrite with push_eval cancel_pair
                    | _ => progress break_match
                    | H:_ |- _ => unique pose proof (Z_div_exact_full_2 _ _ s_nonzero H)
                    end; nsatz. Qed.

    Definition reduce (s:Z) (c:list limb) (p:list limb) : list limb :=
      let ab := split s p in fst ab ++ mul c (snd ab).

    Lemma reduction_rule a b s c (modulus_nonzero:s-c<>0) :
      (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
    Proof. replace (a + s * b) with ((a + c*b) + b*(s-c)) by nsatz.
           rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod; trivial. Qed.

    Lemma eval_reduce s c p (s_nonzero:s<>0) (modulus_nonzero:s-eval c<>0) :
      eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
    Proof. cbv [reduce]. rewrite eval_app, eval_mul, <-reduction_rule, eval_split; trivial. Qed.

    Definition carry (w fw:Z) : list limb -> list limb :=
      List.flat_map (fun t => if dec (fst t = w)
                              then cons (w*fw, snd t / fw) (cons (w, snd t mod fw) nil)
                              else cons t nil).
    Lemma eval_carry w fw p (fw_nonzero:fw<>0) : eval (carry w fw p) = eval p.
    Proof. induction p; simpl carry; repeat break_match; autorewrite with push_eval cancel_pair;
             try pose proof (Z.div_mod (snd a) _ fw_nonzero); nsatz.
    Qed. Hint Rewrite eval_carry eval_reduce : push_eval.

    Section Saturated.
      Context {word_max : Z} {word_max_pos : 1 < word_max} 
              {add : Z -> Z -> Z * Z}
              {add_correct : forall x y, fst (add x y) + word_max * snd (add x y) = x + y}
              {mul : Z -> Z -> Z * Z}
              {mul_correct : forall x y, fst (mul x y) + word_max * snd (mul x y) = x * y}
              {end_wt:Z} {end_wt_pos : 0 < end_wt}
      .

      (* TODO : move *)
      Fixpoint flat_map_cps {A B} (g:A->forall {T}, (list B->T)->T) (ls : list A) {T} (f:list B->T)  :=
        match ls with
        | nil => f nil
        | (x::tl)%list => g x (fun r => flat_map_cps g tl (fun rr => f (r ++ rr))%list)
        end.
      
      Definition multerm (t t' : limb) {T} (f:list limb->T) :=
        dlet tt' := mul (snd t) (snd t') in
        f ((fst t*fst t', runtime_fst tt') :: (fst t*fst t'*word_max, runtime_snd tt') :: nil)%list.

      Definition sat_mul (p q : list limb) {T} (f:list limb->T) := 
        flat_map_cps (fun t => @flat_map_cps _ _ (multerm t) q) p f.
      (* TODO (jgross): kind of an interesting behavior--it infers the type arguments like this but fails to check if I leave them implicit *)

      Lemma multerm_correct t t' : forall {T} (f:list limb->T),
       multerm t t' f = f ([(fst t*fst t', fst (mul (snd t) (snd t'))); (fst t*fst t'*word_max, snd (mul (snd t) (snd t')))]).
      Proof. reflexivity. Qed.
      Lemma flat_map_cps_correct {A B} g ls: forall {T} (f:list B->T) g',
        (forall x T h, @g x T h = h (g' x)) ->
       @flat_map_cps A B g ls T f = f (List.flat_map g' ls).
      Proof.
        induction ls; intros; [reflexivity|].
        simpl flat_map_cps. simpl flat_map.
        rewrite H; erewrite IHls by eassumption.
        reflexivity.
      Qed.
      Lemma eval_map_sat_mul t q :
        flat_map_cps (multerm t) q eval = fst t * snd t * eval q.
      Proof.
        induction q; intros; simpl flat_map_cps; [autorewrite with push_eval; nsatz|].
        rewrite multerm_correct.
        erewrite !@flat_map_cps_correct in * by apply multerm_correct.
        autorewrite with push_eval cancel_pair.
        rewrite IHq.
        repeat match goal with |- context [mul ?x ?y] =>
                               unique pose proof (mul_correct x y) end.
        nsatz.
      Qed. Hint Rewrite eval_map_sat_mul : push_eval. 
      Lemma eval_sat_mul p q : sat_mul p q eval = eval p * eval q.
      Proof.
        cbv [sat_mul];  erewrite !@flat_map_cps_correct
          by (intros; try apply flat_map_cps_correct; apply multerm_correct).
        induction p; intros; [reflexivity|].
        simpl flat_map; autorewrite with push_eval cancel_pair.
        rewrite IHp; erewrite <-flat_map_cps_correct by apply multerm_correct.
        rewrite eval_map_sat_mul; nsatz.
      Qed. Hint Rewrite eval_sat_mul : push_eval.

      Fixpoint find_remove_first'_cps {A} (g:A->forall {T}, (bool->T)->T) (acc ls:list A)
               {T} (f:option A * list A ->T) :=
        match ls with
        | [] => f (None, acc)
        | x :: tl =>
          g x (fun r =>
          if r
          then f (Some x, acc ++ tl)
          else
            find_remove_first'_cps g (acc ++ [x]) tl f)
        end.
      Definition find_remove_first_cps {A} g ls {T} f :=
        @find_remove_first'_cps A g nil ls T f.

      Lemma find_remove_first'_cps_correct
            {A} (g:A->forall {T}, (bool->T) -> T) ls {T} f
            (H: forall x {B} h, @g x B h = h (g x id)):
        forall acc,
          @find_remove_first'_cps A g acc ls T f =
          f (find_remove_first' (fun x => g x id) acc ls).
      Proof.
        induction ls; intros; simpl; try (rewrite H, IHls; break_if); reflexivity.
      Qed.
      Lemma find_remove_first_cps_correct
            {A} (g:A->forall {T}, (bool->T) -> T) ls {T} f
            (H: forall x {B} h, @g x B h = h (g x id)):
          @find_remove_first_cps A g ls T f =
          f (find_remove_first (fun x => g x id) ls).
      Proof. apply find_remove_first'_cps_correct; auto. Qed.

      Definition has_same_wt (cx a:limb) {T} (f:bool->T) :=
        if dec (fst cx = fst a) then f true else f false.
      Lemma has_same_wt_correct cx a {T} f:
        @has_same_wt cx a T f = f (if dec (fst cx = fst a) then true else false).
      Proof. cbv [has_same_wt]; break_if; reflexivity. Qed.

      Lemma find_remove_first'_cps_same_wt cx cx' p: forall acc,
        find_remove_first'_cps (has_same_wt cx) acc p fst = Some cx' ->
        fst cx' = fst cx /\
        fst cx * (snd cx + snd cx') + find_remove_first'_cps (has_same_wt cx) acc p (fun r =>eval (snd r)) = fst cx * snd cx + eval acc + eval p.
      Proof.
        cbv [has_same_wt];
        induction p; intros; simpl find_remove_first'_cps in *;
            repeat match goal with
                   | |- _ => progress (autorewrite with push_eval cancel_pair in * )
                   | H : Some _ = Some _ |- _ => progress (inversion H; subst)
                   | |- _ => erewrite (proj2 (IHp _ _)); erewrite (proj1 (IHp _ _))
                   | |- _ => break_if
                   | |- _ => split; subst 
                   | |- _ => discriminate
                   | |- _ => nsatz
                   end.
        Unshelve.
        assumption.
        2:eassumption.
      Qed.

      Lemma find_remove_first_cps_same_wt cx cx' p
        (H : find_remove_first_cps (has_same_wt cx) p fst = Some cx') :
        fst cx' = fst cx /\
        fst cx * (snd cx + snd cx') + find_remove_first_cps (has_same_wt cx) p (fun r => eval (snd r)) = fst cx * snd cx + eval p.
      Proof.
        cbv [find_remove_first_cps]; intros.
        erewrite (proj1 (find_remove_first'_cps_same_wt _ _ _ _ H)) by eauto.
        erewrite (proj2 (find_remove_first'_cps_same_wt _ _ _ _ H)) by eauto.
        autorewrite with push_eval; split; try ring.
      Qed.

      Fixpoint compact_no_carry' (acc p:list limb) {T} (f:list limb->T) :=
        match p with
        | nil => f acc
        | (cx::tl)%list =>
          find_remove_first_cps
            (has_same_wt cx) acc
            (fun r =>
               match (fst r) with
               | None => compact_no_carry' (cx::acc)%list tl f
               | Some l => compact_no_carry' ((fst cx, (snd cx + snd l)%RT)::snd r)%list tl f
               end)
        end.
      Definition compact_no_carry p {T} f := @compact_no_carry' nil p T f.
      
      Lemma eval_compact_no_carry' p {T} (f:list limb -> T) g
          (H:forall x, f x = g (eval x)):
          forall acc,
        compact_no_carry' acc p f = g (eval acc + eval p).
      Proof.
        induction p; simpl;
          repeat match goal with
                 | |- _ => rewrite @find_remove_first_cps_correct in *
                     by apply has_same_wt_correct
                 | |- _ => rewrite H
                 | |- _ => break_match
                 | |- _ => progress (intros;subst)
                 | |- _ => progress autorewrite with push_eval cancel_pair in *
                 | |- _ => rewrite IHp
                 | H : fst (find_remove_first _ _) = _ |- _ =>
                   rewrite <-find_remove_first_cps_correct in H by apply has_same_wt_correct;
                     destruct (find_remove_first_cps_same_wt _ _ _ H); clear H
                 | |- g _ = g _ => apply f_equal
                 | |- _ => nsatz
                 end.
      Qed.
      Lemma length_compact_no_carry' p: forall acc,
          (compact_no_carry' acc p (@length _) <= length p + length acc)%nat.
      Proof.
        induction p; simpl;
          repeat match goal with
                 | |- _ => progress intros
                 | |- _ => progress distr_length
                 | |- _ => rewrite @find_remove_first_cps_correct in *
                     by apply has_same_wt_correct
                 | |- _ => rewrite IHp
                 | |- _ => break_match
                 end.
      Qed.
      Lemma eval_compact_no_carry p: forall {T} (f:list limb -> T) g,
         (forall x, f x = g (eval x)) ->
         compact_no_carry p f = g (eval p).
      Proof.
        cbv [compact_no_carry]; intros.
        apply eval_compact_no_carry'; assumption.
      Qed.
      Lemma length_compact_no_carry p: (compact_no_carry p (@length _) <= length p)%nat. Proof. cbv [compact_no_carry]. rewrite length_compact_no_carry'. distr_length. Qed. Hint Rewrite length_compact_no_carry : distr_length.

      (* n is fuel, should be length of inp *)
      Fixpoint compact_cols_loop1 (carries out inp : list limb) (n:nat)
               {T} (f:list limb * list limb ->T):=
        match n with
        | O => f (carries, out)
        | S n' => 
          match inp with
          | nil => f (carries, out)
          | cons cx tl =>
            find_remove_first_cps
              (has_same_wt cx) tl
              (fun r =>
                 let found_ls := r in
                 match (fst found_ls) with
                 | None => compact_cols_loop1 carries (cx::out) tl n' f
                 | Some cx' =>
                   dlet sum_carry := add (snd cx) (snd cx') in
                   compact_no_carry
                     ((fst cx * word_max, runtime_snd sum_carry)::carries)
                              (fun rr =>
                                 compact_cols_loop1 rr out ((fst cx, runtime_fst sum_carry):: snd found_ls) n' f)
                 end)
          end
        end.
(*
      Definition p : list limb := [(1,5); (4,2); (4,3); (4,2)].
      Goal False.
        remember (sat_mul p p id) as P.
        cbv - [Let_In runtime_add runtime_mul runtime_fst runtime_snd] in HeqP.
        cbv [runtime_add runtime_mul runtime_fst runtime_snd] in HeqP.
      Abort.
      Goal False.
        remember (sat_mul p p (fun r => compact_no_carry r id)) as P.
        cbv - [Let_In runtime_add runtime_mul runtime_fst runtime_snd] in HeqP.
        cbv [runtime_add runtime_mul runtime_fst runtime_snd] in HeqP.
      Abort.
      Goal False.
        remember (sat_mul p p (fun r => compact_cols_loop1 nil nil r (length r) id)) as P.
        cbv - [Let_In runtime_add runtime_mul runtime_fst runtime_snd] in HeqP.
        cbv [runtime_add runtime_mul runtime_fst runtime_snd] in HeqP.
      Abort.
      *)
      Ltac find_continuation H :=
        intros;
        rewrite H;
        match goal with |- ?lhs = ?g ?y =>
                        match eval pattern y in lhs with
                          ?f _ =>
                          change (f y = g y)
                        end
        end;
        apply f_equal; reflexivity.

      Lemma eval_compact_cols_loop1 n 
            {T} (f:list limb * list limb ->T) g
            (H:forall x, f x = g (eval (fst x) + eval (snd x))):
        forall p (H0:length p = n) out carries,
          compact_cols_loop1 carries out p n f
          = g (eval p + eval out + eval carries).
      Proof.
        induction n; destruct p; intros; distr_length; subst;
          simpl compact_cols_loop1; cbv [Let_In];
            repeat match goal with
                   | |- _ => erewrite eval_compact_no_carry
                       by find_continuation IHn
                   | |- _ => (rewrite @find_remove_first_cps_correct in *
                               by apply has_same_wt_correct )
                   | |- _ => rewrite H 
                   | |- _ => rewrite IHn
                   | |- _ => break_match
                   | |- _ => progress subst 
                   | |- _ => progress autorewrite with
                             push_eval cancel_pair distr_length
                   | |- context[add ?x ?y] =>
                     specialize (add_correct x y)
                   | H : fst (find_remove_first _ ?p) = Some _ |- _ =>
                     unique assert (length p > 0)%nat
                       by (destruct p; (discriminate || (simpl; omega)))
                   | |- context[compact_cols_loop1 _ _ ?p _ _ ] =>
                     specialize (IHn p);
                       let H := fresh "H" in
                       match type of IHn with
                         ?P -> _ => assert P as H
                             by (intros; distr_length; break_match;
                                 (omega || discriminate));
                                      specialize (IHn H); clear H
                       end
                   | H : fst (find_remove_first _ _) = _ |- _ =>
                     rewrite <-find_remove_first_cps_correct in H
                       by apply has_same_wt_correct;
                       destruct (find_remove_first_cps_same_wt _ _ _ H);
                       clear H
                   | |- g _ = g _ => apply f_equal 
                   | |- _ => discriminate 
                   | |- _ => nsatz
                   | |- _ => omega
                   end.
      Qed. Hint Rewrite eval_compact_cols_loop1 : push_eval.

      (* TODO : move *)
      Definition fold_right_no_starter {A} (f:A->A->A) ls : option A :=
        match ls with
        | nil => None
        | cons x tl => Some (List.fold_right f x tl)
        end.
      Lemma fold_right_min ls x :
          x = List.fold_right Z.min x ls
          \/ List.In (List.fold_right Z.min x ls) ls.
      Proof.
        induction ls; intros; simpl in *; try tauto.
        match goal with |- context [Z.min ?x ?y] =>
                        destruct (Z.min_spec x y) as [[? Hmin]|[? Hmin]]
        end; rewrite Hmin; tauto.
      Qed.
      Lemma fold_right_no_starter_min ls : forall x,
        fold_right_no_starter Z.min ls = Some x ->
        List.In x ls.
      Proof.
        cbv [fold_right_no_starter]; intros; destruct ls; try discriminate.
        inversion H; subst; clear H.
        destruct (fold_right_min ls z); subst; simpl List.In; tauto.
      Qed.
      Fixpoint fold_right_cps {A B} (g:B->A->A) (a0:A) (l:list B) {T} (f:A->T) :=
        match l with
        | nil => f a0
        | cons a tl => fold_right_cps g a0 tl (fun r => f (g a r))
        end.
      Lemma fold_right_cps_correct {A B} g a0 l: forall {T} f,
        @fold_right_cps A B g a0 l T f = f (List.fold_right g a0 l).
      Proof. induction l; intros; simpl; rewrite ?IHl; auto. Qed.
      Definition fold_right_no_starter_cps {A} g ls {T} (f:option A->T) :=
        match ls with
        | nil => f None
        | cons x tl => f (Some (List.fold_right g x tl))
        end.
      Lemma fold_right_no_starter_cps_correct {A} g ls {T} f :
        @fold_right_no_starter_cps A g ls T f = f (fold_right_no_starter g ls).
      Proof.
        cbv [fold_right_no_starter_cps fold_right_no_starter]; break_match; reflexivity.
      Qed.        

      (* n is fuel, should be [length carries + length inp] *)
      Fixpoint compact_cols_loop2 (carries out inp :list limb) (n:nat)
               {T} (f:list limb->T) :=
        match n with
        | O => f (out++carries++inp)
        | S n' => 
          fold_right_no_starter_cps
            Z.min (List.map fst (inp ++ carries))
            (fun r =>
               match r with
               | None => f (out++carries++inp)
               | Some min =>
                 find_remove_first_cps
                   (has_same_wt (min, 0)) inp
                   (fun rr =>
                      let inp_found_ls := rr in
                      find_remove_first_cps
                        (has_same_wt (min, 0)) carries
                        (fun rrr =>
                           let car_found_ls := rrr in
                           match fst inp_found_ls, fst car_found_ls with
                           | None, None => f out (* never happens *)
                           | Some cx, None =>
                             compact_cols_loop2 carries (cx :: out) (snd inp_found_ls) n' f
                           | None, Some cx =>
                             compact_cols_loop2 (snd car_found_ls) (cx :: out) inp n' f
                           | Some icx, Some ccx =>
                             dlet sum_carry := add (snd icx) (snd ccx) in
                                 compact_no_carry 
                                   ((min * word_max, runtime_snd sum_carry)::(snd car_found_ls))
                                   (fun rrrr =>
                                      compact_cols_loop2
                                        rrrr
                                        ((min, runtime_fst sum_carry) :: out)
                                        (snd inp_found_ls) n' f)
                           end))
               end)
        end.

      Lemma eval_compact_cols_loop2 n
        {T} (f:list limb->T) g (H:forall x, f x = g (eval x)):
        forall out p carries,
        compact_cols_loop2 carries out p n f
        = g (eval p + eval carries + eval out).
      Proof.
        induction n; intros; simpl compact_cols_loop2; cbv [Let_In].
        { destruct p; destruct carries; distr_length;
            rewrite H; f_equal; autorewrite with push_eval distr_length;
              ring. }
        {
          rewrite fold_right_no_starter_cps_correct.
          repeat match goal with
                 | |- _ => rewrite @find_remove_first_cps_correct in *
                     by (try apply find_remove_first_cps_correct;
                         try apply has_same_wt_correct)
                 | |- _ => break_match
                 | H : fst (find_remove_first _ ?p) = Some _ |- _ =>
                   unique assert (length p > 0)%nat by (destruct p; (discriminate || (simpl; omega)))
                 | |- _ => rewrite H
                 | |- _ => erewrite eval_compact_no_carry by find_continuation IHn
                 | |- _ => rewrite IHn by
                       (try match goal with
                              |- context [length (compact_no_carry ?p)] =>
                              pose proof (length_compact_no_carry p) end;
                        distr_length; repeat break_match; (omega || congruence))
                 | |- context[add ?x ?y] =>
                   specialize (add_correct x y)
                 | H : fst (find_remove_first _ _) = Some _ |- _ =>
                   rewrite <-find_remove_first_cps_correct in H
                     by apply has_same_wt_correct;
                     destruct (find_remove_first_cps_same_wt _ _ _ H);
                     clear H
                 | |- _ => nsatz
                 | |- _ => progress (autorewrite with push_eval cancel_pair distr_length in * )
                 | H : fold_right_no_starter Z.min _ = Some _ |- _ =>
                   apply fold_right_no_starter_min in H
                 | H : fst (find_remove_first _ _) = None |- _ =>
                   apply find_remove_first_None in H
                 | H : List.In _ (List.map _ _) |- _ =>
                   apply List.in_map_iff in H;
                     destruct H as [? [? ?]]; subst
                 | H : List.In _ (_ ++ _) |- _ => apply List.in_app_or in H; destruct H
                 | H1 : fst (find_remove_first _ ?p) = None,
                        H2 : List.In ?x ?p
                   |- _ =>
                   apply (find_remove_first_None _ _ H1) in H2;
                     cbv [has_same_wt id] in H2; simpl fst in H2;
                       break_if; congruence
                 | H : _ \/ _ |- _ => destruct H
                 | |- g _ = g _ => apply f_equal
                 end.
          }
      Qed. Hint Rewrite eval_compact_cols_loop2 : push_eval.

      Definition compact_cols (p:list limb) {T} (f:list limb->T) :=
        compact_cols_loop1
          nil nil p (length p)
          (fun r => compact_cols_loop2
                      (fst r) nil (snd r) (length (fst r ++ snd r)) f).

      Lemma eval_compact_cols (p:list limb) {T} (f:list limb->T) g
        (H: forall x, f x = g (eval x)) :
        compact_cols p f = g (eval p).
      Proof.
        cbv [compact_cols];
          repeat match goal with
                 | |- _ => progress intros
                 | |- _ => progress autorewrite with push_eval cancel_pair
                 | |- _ => progress distr_length
                 | |- _ => erewrite eval_compact_cols_loop1
                 | |- _ => erewrite eval_compact_cols_loop2
                 | |- _ => rewrite H
                 | |- _ => apply f_equal; ring
                 | |- _ => reflexivity
                 end.
      Qed.
    End Saturated.
  End Associational.

  Module Positional.
    Section Positional.
      Import Associational.
      Context (weight : nat -> Z) (* [weight i] is the weight of position [i] *)
              (weight_0 : weight 0%nat = 1%Z)
              (weight_nonzero : forall i, weight i <> 0).

      (** Converting from positional to associational *)

      Definition to_associational {n:nat} (xs:tuple Z n) : list limb :=
        List.combine (List.map weight (List.seq 0 n)) (Tuple.to_list n xs).
      Definition eval {n} x := Associational.eval (@to_associational n x).
      Lemma eval_to_associational {n} x : Associational.eval (@to_associational n x) = eval x.
      Proof. reflexivity. Qed.

      (** Converting from associational to positional *)

      Program Definition zeros n : tuple Z n := Tuple.from_list n (List.map (fun _ => 0) (List.seq 0 n)) _.
      Next Obligation. autorewrite with distr_length; reflexivity. Qed.
      Lemma eval_zeros n : eval (zeros n) = 0.
      Proof. cbv [eval Associational.eval to_associational zeros]; rewrite Tuple.to_list_from_list.
             generalize dependent (List.seq 0 n); intro xs; induction xs; simpl; nsatz. Qed.

      Program Definition add_to_nth {n} i x : tuple Z n -> tuple Z n :=
        Tuple.on_tuple (ListUtil.update_nth i (runtime_add x)) _.
      Next Obligation. apply ListUtil.length_update_nth. Defined.
      Lemma eval_add_to_nth {n} (i:nat) (H:(i<n)%nat) (x:Z) (xs:tuple Z n) :
        eval (add_to_nth i x xs) = weight i * x + eval xs.
      Proof.
        cbv [eval to_associational add_to_nth Tuple.on_tuple runtime_add]; rewrite !Tuple.to_list_from_list.
        rewrite ListUtil.combine_update_nth_r at 1.
        rewrite <-(update_nth_id i (List.combine _ _)) at 2.
        rewrite <-!(ListUtil.splice_nth_equiv_update_nth_update _ _ (weight 0, 0)); cbv [ListUtil.splice_nth id];
          repeat match goal with
                 | _ => progress (apply Zminus_eq; ring_simplify)
                 | _ => progress autorewrite with push_eval cancel_pair distr_length
                 | _ => progress rewrite <-?ListUtil.map_nth_default_always, ?map_fst_combine, ?List.firstn_all2, ?ListUtil.map_nth_default_always, ?nth_default_seq_inbouns, ?plus_O_n
                 end; trivial; lia. Qed. Hint Rewrite @eval_add_to_nth eval_zeros : push_eval.

      Fixpoint place (t:limb) (i:nat) : nat * Z :=
        if dec (fst t mod weight i = 0)
        then (i, let c := fst t / weight i in (c * snd t)%RT)
        else match i with S i' => place t i' | O => (O, fst t * snd t)%RT end.
      Lemma place_in_range (t:limb) (n:nat) : (fst (place t n) < S n)%nat.
      Proof. induction n; simpl; break_match; simpl; omega. Qed.
      Lemma weight_place t i : weight (fst (place t i)) * snd (place t i) = fst t * snd t.
      Proof. induction i; simpl place; break_match; autorewrite with cancel_pair;
               try find_apply_lem_hyp Z_div_exact_full_2; nsatz || auto. Qed.

      Definition from_associational n (p:list limb) :=
        List.fold_right (fun t => let p := place t (pred n) in add_to_nth (fst p) (snd p)) (zeros n) p.
      Lemma eval_from_associational {n} p (n_nonzero:n<>O) :
        eval (from_associational n p) = Associational.eval p.

      Proof. induction p; simpl; try pose proof place_in_range a (pred n);
               autorewrite with push_eval; rewrite ?weight_place; nsatz || omega.
      Qed. Hint Rewrite @eval_from_associational : push_eval.

      Definition carry (index:nat) (p:list limb) : list limb :=
        Associational.carry (weight index) (weight (S index) / weight index) p.
      Lemma eval_carry i p : weight (S i) / weight i <> 0 ->
        Associational.eval (carry i p) = Associational.eval p.
      Proof. cbv [carry]; intros; auto using eval_carry. Qed.
      Hint Rewrite @eval_carry : push_eval.
    End Positional.
  End Positional.
End B.

Section Karatsuba.
  Context {T : Type} (eval : T -> Z)
          (sub : T -> T -> T)
          (eval_sub : forall x y, eval (sub x y) = eval x - eval y)
          (mul : T -> T -> T)
          (eval_mul : forall x y, eval (mul x y) = eval x * eval y)
          (add : T -> T -> T)
          (eval_add : forall x y, eval (add x y) = eval x + eval y)
          (scmul : Z -> T -> T)
          (eval_scmul : forall c x, eval (scmul c x) = c * eval x)
          (split : Z -> T -> T * T)
          (eval_split : forall s x, s <> 0 -> eval (fst (split s x)) + s * (eval (snd (split s x))) = eval x)
  .

  Definition karatsuba_mul s (x y : T) : T :=
      let xab := split s x in
      let yab := split s y in
      let xy0 := mul (fst xab) (fst yab) in
      let xy2 := mul (snd xab) (snd yab) in
      let xy1 := sub (mul (add (fst xab) (snd xab)) (add (fst yab) (snd yab))) (add xy2 xy0) in
      add (add (scmul (s^2) xy2) (scmul s xy1)) xy0.

  Lemma eval_karatsuba_mul s x y (s_nonzero:s <> 0) :
    eval (karatsuba_mul s x y) = eval x * eval y.
  Proof. cbv [karatsuba_mul]; repeat rewrite ?eval_sub, ?eval_mul, ?eval_add, ?eval_scmul.
         rewrite <-(eval_split s x), <-(eval_split s y) by assumption; ring. Qed.


  Definition goldilocks_mul s (xs ys : T) : T :=
    let a_b := split s xs in
    let c_d := split s ys in
    let ac := mul (fst a_b) (fst c_d) in
    (add (add ac (mul (snd a_b) (snd c_d)))
         (scmul s (sub (mul (add (fst a_b) (snd a_b)) (add (fst c_d) (snd c_d))) ac))).

  Local Existing Instances Z.equiv_modulo_Reflexive RelationClasses.eq_Reflexive Z.equiv_modulo_Symmetric Z.equiv_modulo_Transitive Z.mul_mod_Proper Z.add_mod_Proper Z.modulo_equiv_modulo_Proper.

  Lemma goldilocks_mul_correct (p : Z) (p_nonzero : p <> 0) s (s_nonzero : s <> 0) (s2_modp : (s^2) mod p = (s+1) mod p) xs ys :
    (eval (goldilocks_mul s xs ys)) mod p = (eval xs * eval ys) mod p.
  Proof. cbv [goldilocks_mul]; Zmod_to_equiv_modulo.
    repeat rewrite ?eval_mul, ?eval_add, ?eval_sub, ?eval_scmul, <-?(eval_split s xs), <-?(eval_split s ys) by assumption; ring_simplify.
    setoid_rewrite s2_modp.
    apply f_equal2; nsatz. Qed.
End Karatsuba.

Local Coercion Z.of_nat : nat >-> Z.
Import Coq.Lists.List.ListNotations. Local Open Scope list_scope.
Import B.

Goal let base10 i := 10^i in forall f0 f1 f2 f3 g0 g1 g2 g3 : Z, False. intros.
  let t := constr:(Positional.from_associational base10 7
                                   (Associational.mul
                                      (Positional.to_associational base10 (Tuple.from_list _ [f0;f1;f2;f3] eq_refl))
                                      (Positional.to_associational base10 (Tuple.from_list _ [g0;g1;g2;g3] eq_refl)))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc in Heqt.
Abort.

Goal let base2_51 i := 2 ^ (51 * i) in forall f0 f1 f2 f3 f4 g0 g1 g2 g3 g4 : Z, False. intros.
  let t := constr:(Positional.from_associational base2_51 5
                                   (Associational.reduce (2^255) [(1,19)] 
                                   (Associational.mul
                                      (Positional.to_associational base2_51 (Tuple.from_list _ [f0;f1;f2;f3;f4] eq_refl))
                                      (Positional.to_associational base2_51 (Tuple.from_list _ [g0;g1;g2;g3;g4] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc in Heqt.
Abort.

Axiom add_get_carry : Z -> Z -> Z * Z.
Axiom mul : Z -> Z -> Z * Z.

Require Import Crypto.Algebra. (* TODO: move ring_simplify_subterms_in_all to a different file? *)
Goal
  let base2_32 i := 2 ^ (32 * i) in
  forall f0 f1 f2 f3 g0 g1 g2 g3: Z, False.
  intros.
  let t := constr:(
             let f := (Positional.to_associational base2_32 (Tuple.from_list _ [f0;f1;f2;f3] eq_refl)) in
             let g := (Positional.to_associational base2_32 (Tuple.from_list _ [g0;g1;g2;g3] eq_refl)) in
             @Associational.sat_mul
               (2^32) mul f g _
               (fun r =>
                  (@Associational.compact_cols (2^32) add_get_carry r _ id)))
                                    in
  
  let t := (eval cbv -[Let_In runtime_mul runtime_add runtime_fst runtime_snd] in t) in
  let t := (eval cbv [runtime_mul runtime_add runtime_fst runtime_snd] in t) in
  remember t eqn:Heqt; rewrite ?Z.mul_1_l, ?Z.add_0_r, ?Z.add_assoc, ?Z.mul_assoc in Heqt.
Abort.

Goal let base2_25_5 i := 2 ^ (25 * (i / 2) + 26 * (i - i / 2)) in forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9: Z, False. intros.
  let t := constr:(Positional.from_associational base2_25_5 10
                                   (Associational.reduce (2^255) [(1,19)] 
                                   (Associational.mul
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] eq_refl))
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc in Heqt.
Abort.

Goal let base2_56 i := 2 ^ (56 * i) in forall f0 f1 f2 f3 f4 f5 f6 f7 g0 g1 g2 g3 g4 g5 g6 g7: Z, False. intros.
  let t := constr:(Positional.from_associational base2_56 8
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)] 
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)] 
                                   (Associational.mul
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7] eq_refl))
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7] eq_refl)))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc, !Z.mul_opp_l, !Z.add_opp_r in Heqt.
Abort.

Goal let base2_25_5 i := 2 ^ (25 * (i / 2) + 26 * (i - i / 2)) in forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9: Z, False. intros.
  let t := constr:(Positional.from_associational base2_25_5 10
                                   (Associational.reduce (2^255) [(1,19)] 
                                   (karatsuba_mul (fun x y => x ++ (List.map (fun t => (fst t, (-1 * snd t)%RT)) y)) Associational.mul (@List.app _) (fun x => List.map (fun t => (x * fst t, snd t))) Associational.split (2^102)
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] eq_refl))
                                      (Positional.to_associational base2_25_5 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] eq_refl))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; change (Zneg xH) with (Z.opp 1) in Heqt; (* TODO : make this a lemma *)
    ring_simplify_subterms_in_all.
Abort.

Goal let base2_56 i := 2 ^ (56 * i) in forall f0 f1 f2 f3 f4 f5 f6 f7 g0 g1 g2 g3 g4 g5 g6 g7: Z, False. intros.
  let t := constr:(Positional.from_associational base2_56 8
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)]
                                   (Associational.reduce (2^448) [(2^224,1);(1,-1)]
                                   (goldilocks_mul (fun x y => x ++ (List.map (fun t => (fst t, (-1 * snd t)%RT)) y)) Associational.mul (@List.app _) (fun x => List.map (fun t => (x * fst t, snd t))) Associational.split (2^224)
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [f0;f1;f2;f3;f4;f5;f6;f7] eq_refl))
                                      (Positional.to_associational base2_56 (Tuple.from_list _ [g0;g1;g2;g3;g4;g5;g6;g7] eq_refl)))))) in
  let t := (eval cbv -[runtime_mul runtime_add] in t) in
  let t := (eval cbv [runtime_mul runtime_add] in t) in
  remember t eqn:Heqt; rewrite !Z.mul_1_l, !Z.add_0_r, !Z.add_assoc, !Z.mul_assoc, !Z.mul_opp_l, !Z.add_opp_r, !Z.sub_opp_r in Heqt.
Abort.