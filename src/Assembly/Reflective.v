Require Import ZArith List Listize Basics Bool Nsatz Basics.
Require Import QhasmUtil WordizeUtil.
Require Import Crypto.Util.Tuple.

Import ListNotations.

Section Evaluability.
  Class Evaluable T := evaluator {
    ezero: T;

    (* Conversions *)
    toT: nat -> T;
    fromT: T -> nat;

    (* Operations *)
    eadd: T -> T -> T;
    esub: T -> T -> T;
    emul: T -> T -> T;
    eshiftr: T -> nat -> T;
    emask: T -> nat -> T;

    (* Comparisons *)
    eltb: T -> T -> bool;
    eeqb: T -> T -> bool
  }.
End Evaluability.

Section Conditionals.
  Inductive RCond A :=
    | RZero: A -> RCond A
    | RLt: A -> A -> RCond A
    | REq: A -> A -> RCond A.
End Conditionals.

(* Type of our Z Expressions *)
Section Expr.
  Context {T: Type}.
  Context {E: Evaluable T}.

  Inductive RExpr :=
    | RConst: T -> RExpr
    | RAdd: RExpr -> RExpr -> RExpr
    | RSub: RExpr -> RExpr -> RExpr
    | RMul: RExpr -> RExpr -> RExpr
    | RShiftr: RExpr -> nat -> RExpr
    | RMask: RExpr -> nat -> RExpr
    | REIte: RCond RExpr -> RExpr -> RExpr -> RExpr.

  Fixpoint evalExpr (x: RExpr): T :=
    match x with
    | RConst v => v
    | RAdd a b => eadd (evalExpr a) (evalExpr b)
    | RSub a b => esub (evalExpr a) (evalExpr b)
    | RMul a b => emul (evalExpr a) (evalExpr b)
    | RShiftr a k => eshiftr (evalExpr a) k
    | RMask a k => emask (evalExpr a) k
    | REIte c a b =>
      if match c with
      | RZero x => eeqb (evalExpr x) ezero
      | RLt x y => eltb (evalExpr x) (evalExpr y)
      | REq x y => eeqb (evalExpr x) (evalExpr y)
      end then (evalExpr a) else (evalExpr b)
    end.
End Expr.

(* Simple Mostly-PHOAS *)
Section Term.
  Context {T: Type}.
  Context {E: @Evaluable T}.

  Inductive RType :=
    | RBool: RType
    | RT: RType
    | RList: RType -> RType
    | RArrow: RType -> RType -> RType.

  Fixpoint Var (t: RType): Type :=
    match t with
    | RBool => bool
    | RT => @RExpr T
    | RList A => list (Var A)
    | RArrow A B => (Var A) -> (Var B)
    end.

  Inductive RTerm: RType -> Type :=
    (* Elements *)
    | RVar : forall A, Var A -> RTerm A

    (* Lists *)
    | RNth: forall A, RTerm (RList A) -> nat -> Var A -> RTerm A

    (* Functions *)
    | RApp : forall A B, RTerm (RArrow A B) -> RTerm A -> RTerm B
    | RLam : forall A B, (Var A -> RTerm B) -> RTerm (RArrow A B)

    (* Conditionals. TODO: can we make this parametric? *) 
    | RTIteList :
      RCond (RTerm RT) -> RTerm (RList RT) -> RTerm (RList RT) -> RTerm (RList RT)

    | RTIteT : RCond (RTerm RT) -> RTerm RT -> RTerm RT -> RTerm RT.

  Fixpoint denote {A} (e : RTerm A) {struct e} : Var A :=
    match e in (RTerm A) return (Var A) with
    | RVar _ v => v
    | RNth _ lst k d => nth k (denote lst) d
    | RApp _ _ f x => (denote f) (denote x)
    | RLam _ _ f => fun x => denote (f x)

    | RTIteT c a b =>
      REIte
      match c with
      | RZero x => RZero _ (denote x)
      | RLt x y => RLt _ (denote x) (denote y)
      | REq x y => REq _ (denote x) (denote y)
      end (denote a) (denote b)

    | RTIteList c a b =>
      map (fun p => REIte
      match c with
      | RZero x => RZero _ (denote x)
      | RLt x y => RLt _ (denote x) (denote y)
      | REq x y => REq _ (denote x) (denote y)
      end (fst p) (snd p))
       (List.combine (denote a) (denote b))
    end.
End Term.

Section Sig.
  Context {T: Type}.
  Context {E: @Evaluable T}.

  Definition astOf (f: ListF T T): Type :=
    {g: RTerm (RArrow (RList RT) (RList RT)) | forall x,
        map evalExpr ((denote g) (map RConst x)) = f x}.
End Sig.

Section Conversion.
  Fixpoint convertExpr {A B} {ea: Evaluable A} {eb: Evaluable B}
      (t: @RExpr A): @RExpr B :=
    match t with
    | RConst v => RConst (@toT B eb (@fromT A ea v))
    | RAdd a b => RAdd (convertExpr a) (convertExpr b)
    | RSub a b => RSub (convertExpr a) (convertExpr b)
    | RMul a b => RMul (convertExpr a) (convertExpr b)
    | RShiftr a k => RShiftr (convertExpr a) k
    | RMask a k => RMask (convertExpr a) k
    | REIte c a b =>
      match c with
      | RZero x =>
        REIte (RZero _ (convertExpr x))
              (convertExpr a) (convertExpr b)
      | RLt x y => 
        REIte (RLt _ (convertExpr x) (convertExpr y))
              (convertExpr a) (convertExpr b)
      | REq x y =>
        REIte (REq _ (convertExpr x) (convertExpr y))
              (convertExpr a) (convertExpr b)
      end
    end.

  (* TODO (rsloan): can we make this a fixpoint? *)
  Definition convertVar {A B V} {ea: Evaluable A} {eb: Evaluable B}
      (t: @Var A V): @Var B V.
    revert ea eb t; revert A B.
    induction V; intros.

    - refine t.
    - refine (convertExpr t).
    - refine (map (IHV A B ea eb) t).
    - refine (fun x => IHV2 _ _ _ _ (t (IHV1 _ _ _ _ x))).
  Defined.

  Fixpoint convertAST {A B V} {ea: Evaluable A} {eb: Evaluable B}
      (t: @RTerm A V): @RTerm B V :=
    match t with
    | RVar _ v => RVar _ (convertVar v)
    | RNth _ lst k d => RNth _ (convertAST lst) k (convertVar d)
    | RApp _ _ f x => RApp _ _ (convertAST f) (convertAST x)
    | RLam _ _ f => RLam _ _ (fun x => convertAST (f (convertVar x)))

    | RTIteT c a b =>
      RTIteT
      match c with
      | RZero x => RZero _ (convertAST x)
      | RLt x y => RLt _ (convertAST x) (convertAST y)
      | REq x y => REq _ (convertAST x) (convertAST y)
      end (convertAST a) (convertAST b)

    | RTIteList c a b =>
      RTIteList 
      match c with
      | RZero x => RZero _ (convertAST x)
      | RLt x y => RLt _ (convertAST x) (convertAST y)
      | REq x y => REq _ (convertAST x) (convertAST y)
      end (convertAST a) (convertAST b)
    end.
End Conversion.

Section ASTLemmas.
End ASTLemmas.