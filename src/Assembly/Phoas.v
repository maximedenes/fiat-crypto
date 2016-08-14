Require Import ZArith List Listize Basics Bool Nsatz Basics.
Require Import QhasmUtil WordizeUtil.
Require Import Crypto.Util.Tuple.
Require Import Reflective Evaluables.

Section Types.
  Context {T: Type}.
  Context {E: Evaluable T}.

  Inductive type := TZ | Prod : type -> type -> type.

  Fixpoint interp_type (t:type) :=
    match t with
    | TZ => T
    | Prod a b => prod (interp_type a) (interp_type b)
    end.

  Ltac reify_type t :=
    lazymatch t with
    | BinInt.Z => constr:(TZ)
    | prod ?l ?r =>
      let l := reify_type l in
      let r := reify_type r in
      constr:(Prod l r)
    end.

  Inductive binop : type -> type -> type -> Type := 
    | OPZadd : binop TZ TZ TZ
    | OPZsub : binop TZ TZ TZ
    | OPZmul : binop TZ TZ TZ.

  Definition interp_binop {t1 t2 t} (op: binop t1 t2 t) :
      interp_type t1 -> interp_type t2 -> interp_type t :=
    match op with
    | OPZadd    => eadd
    | OPZsub    => esub
    | OPZmul    => emul
    end.

  Ltac reify_binop op :=
    lazymatch op with
    | @eadd T E => constr:(OPZadd)
    | @esub T E => constr:(OPZsub)
    | @emul T E => constr:(OPZmul)
    end.

  Inductive natop : type -> type -> Type := 
    | OPZmask : natop TZ TZ
    | OPZshiftr : natop TZ TZ.

  Definition interp_natop {a b} (op: natop a b) :
      interp_type a -> nat -> interp_type b :=
    match op with
    | OPZmask   => emask
    | OPZshiftr => eshiftr
    end.

  Ltac reify_natop op :=
    lazymatch op with
    | @emask T E   => constr:(OPZmask)
    | @eshiftr T E => constr:(OPZshiftr)
    end.
End Types.

Section Expressions.
  Context {T : Type} {E : Evaluable T} {V : Type}.

  Inductive arg : type -> Type :=
    | Const : @interp_type T TZ -> arg TZ
    | Var : V -> arg TZ
    | Pair : forall {t1}, arg t1 -> forall {t2}, arg t2 -> arg (Prod t1 t2).

  Inductive expr : type -> Type :=
    | LetBinop : forall {t1 t2}, binop t1 t2 TZ -> arg t1 -> arg t2 ->
      forall {tC}, (T -> expr tC) -> expr tC
    | LetNatop : forall {t}, natop t TZ -> arg t -> nat ->
      forall {tC}, (T -> expr tC) -> expr tC
    | Return : forall {t}, arg t -> expr t.

  Arguments arg _ : clear implicits.
  Arguments expr _ : clear implicits.
End Expressions.

Section Interp.
  Context {T : Type} {E : Evaluable T} {V : Type}.

  Fixpoint interp_arg {t} (varF: V -> T) (e: arg t) : @interp_type T t :=
    match e with
    | Const v => v
    | Var n => varF n
    | Pair _ e1 _ e2 => (interp_arg varF e1, interp_arg varF e2)
    end.

  Fixpoint interp {t} (varF: V -> T) (e:expr t) : @interp_type T t :=
    match e with
    | LetBinop _ _ op a b _ eC =>
      let x := interp_binop op (interp_arg varF a) (interp_arg varF b) in interp varF (eC x)
    | LetNatop _ op a k _ eC =>
      let x := interp_natop op (interp_arg varF a) k in interp varF (eC x)
    | Return _ a => interp_arg varF a
    end.
End Interp.

Section Conversion.
  Fixpoint convertArg {A ea B eb V t}  (e: @arg A V t): @arg B V t :=
    match e with
    | Const x => Const (@toT B eb (@fromT A ea x))
    | Var v => Var v
    | Pair t0 a t1 b => @Pair B V t0 (convertArg a) t1 (convertArg b)
    end.

  Fixpoint convertExpr {A ea B eb V t}  (e: @expr A V t): @expr B V t :=
    match e with
    | LetBinop _ _ op a b _ eC =>
      @LetBinop _ _ _ _ op (@convertArg A ea B eb V _ a) (@convertArg A ea B eb V _ b) _
                (fun x => convertExpr (eC (@toT A ea (@fromT B eb x))))

    | LetNatop _ op a k _ eC =>
      @LetNatop _ _ _ op (@convertArg A ea B eb V _ a) k _
                (fun x => convertExpr (eC (@toT A ea (@fromT B eb x))))

    | Return _ a => Return (convertArg a)
    end.
End Conversion.

Section RangeExample.
  Definition n := 8.

  Definition ZExpr :=
    @LetBinop Z Z _ _ OPZadd (Const 5%Z) (Const 6%Z) _ (fun v => Return (Const v)).

  Definition WordExpr :=
    @convertExpr Z ZEvaluable (@WordRangeOpt n) WordRangeOptEvaluable _ _ ZExpr.

  Definition rangeInterp {t} :=
    @interp (@WordRangeOpt n) (@WordRangeOptEvaluable n) Z t (fun _ => anyWord).

  Eval vm_compute in (evalWordRangeOpt (rangeInterp WordExpr)).

  Example example_expr : getUpperBoundOpt (rangeInterp WordExpr) = Some 10%N.
  Proof. reflexivity. Qed.
End RangeExample.

