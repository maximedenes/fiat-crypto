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

Section ASTLemmas.

End ASTLemmas.