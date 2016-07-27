Require Import Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits ZArith Znat ZArith_dec Ndec.
Require Import List Listize Basics Bool Nsatz.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import QhasmUtil WordizeUtil.
Require Import BoundedType.
Require Import FunctionalExtensionality.

Import ListNotations.

Section AST.

  Inductive RExpr (T: Type) :=
    | RLit: nat -> RExpr T
    | RConst: T -> RExpr T
    | RAdd: RExpr T -> RExpr T -> RExpr T
    | RSub: RExpr T -> RExpr T -> RExpr T
    | RMul: RExpr T -> RExpr T -> RExpr T
    | RShiftr: RExpr T -> nat -> RExpr T
    | RMask: RExpr T -> nat -> RExpr T.

  Inductive RAST (T: Type): Type :=
    | RList: list (RExpr T) -> RAST T
    | RLet: RExpr T -> (RExpr T -> RAST T) -> RAST T.

End AST.

Section Evaluation.
  Fixpoint evalZ (x: RExpr Z) (input: list Z): Z.
    refine match x with
    | RLit k => nth k input 0%Z
    | RConst x => x
    | RAdd a b => Z.add (evalZ a input) (evalZ b input)
    | RSub a b => Z.sub (evalZ a input) (evalZ b input)
    | RMul a b => Z.mul (evalZ a input) (evalZ b input)
    | RShiftr a k => Z.shiftr (evalZ a input) (Z.of_nat k)
    | RMask a k => Z.land (evalZ a input) (Z.ones (Z.of_nat k))
    end; intuition.
  Defined.

  Fixpoint evalBZ (x: RExpr BoundedZ) (input: list BoundedZ): BoundedZ.
    refine match x with
    | RLit k => nth k input (boundedZ 0%Z 0%Z 0%Z _ _)
    | RConst x => x
    | RAdd a b => bZAdd (evalBZ a input) (evalBZ b input)
    | RSub a b => bZSub (evalBZ a input) (evalBZ b input)
    | RMul a b => bZMul (evalBZ a input) (evalBZ b input)
    | RShiftr a k => bZShiftr (evalBZ a input) k
    | RMask a k => bZMask (evalBZ a input) k
    end; intuition.
  Defined.

  Fixpoint evalN (x: RExpr BoundedN) (input: list BoundedN): BoundedN.
    refine match x with
    | RLit k => nth k input (boundedN 0%N 0%N 1%N _ _)
    | RConst x => x
    | RAdd a b => bNAdd (evalN a input) (evalN b input)
    | RSub a b => bNSub (evalN a input) (evalN b input)
    | RMul a b => bNMul (evalN a input) (evalN b input)
    | RShiftr a k => bNShiftr (evalN a input) k
    | RMask a k => bNMask (evalN a input) k
    end; try nomega; reflexivity.
  Defined.

  Fixpoint evalWord {n}
      (x: RExpr (@BoundedWord n))
      (input: list (@BoundedWord n)): @BoundedWord n.
    refine match x with
    | RLit k => nth k input (boundedWord (wzero _) 0%N 1%N false _ _)
    | RConst x => x
    | RAdd a b => bWAdd (evalWord n a input) (evalWord n b input)
    | RSub a b => bWSub (evalWord n a input) (evalWord n b input)
    | RMul a b => bWMul (evalWord n a input) (evalWord n b input)
    | RShiftr a k => bWShiftr (evalWord n a input) k
    | RMask a k => bWMask (evalWord n a input) k
    end; rewrite wordToN_zero; try nomega; reflexivity.
  Defined.
End Evaluation.

Section Equivalence.
  Definition expreq {ins} (f: Curried Z Z ins 1) :=
    {g: RExpr Z | forall x, curriedToListF 0%Z f x = [evalZ g x] }.

  Inductive ZEquiv: RAST Z -> ListF Z Z -> Prop :=
    | ZEquivList: forall lst f,
        (forall x, map (fun e => evalZ e x) lst = f x)
      -> ZEquiv (RList Z lst) f
    | ZEquivLet: forall x g f,
        ZEquiv (g x) f
      -> ZEquiv (RLet Z x g) f.

  Hint Constructors ZEquiv.

  Definition asteq {ins outs} (f: Curried Z Z ins outs) :=
    {g: RAST Z | ZEquiv g (curriedToListF 0%Z f) }.

End Equivalence.
