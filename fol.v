Require Import List.

Require Import String.
Open Scope string_scope.

Inductive folDecl :=
    | functionSymbol: string -> nat -> folDecl (* nat is arity *)
    | predicateSymbol: string -> nat -> folDecl
    | bolIndSymbol: string -> folDecl.

Definition folSignature := list folDecl.

Definition folVariable := string.
Inductive folTerm : Set :=
  | fromVar: folVariable -> folTerm
  | folIndRef: string -> folTerm
  | folFunctionApp: string -> list folTerm -> folTerm.

Inductive folFormula : Set :=
    | folForall: folVariable -> folFormula -> folFormula
    | folExists: folVariable -> folFormula -> folFormula
    | folBiimpl: folFormula -> folFormula -> folFormula
    | folImpl: folFormula -> folFormula -> folFormula
    | folDisjunction: folFormula -> folFormula -> folFormula
    | folConjunction: folFormula -> folFormula -> folFormula
    | folEq: folTerm -> folTerm -> folFormula
    | folApp: folFormula -> folTerm -> folFormula
    | folLam: (folTerm -> folFormula) -> folFormula
    | folPredicateRef: string -> folFormula.

Definition var_to_term := fun (v: string) => fromVar v.
Coercion var_to_term : string >-> folTerm.

Definition folTheory := list folFormula.

Definition folSystem := (folSignature * folTheory)%type.

Fixpoint normalizeFormula (formula: folFormula): folFormula := match formula with
| folForall      v f => folForall v    (normalizeFormula f)
| folExists      v f => folExists v    (normalizeFormula f)
| folBiimpl      f g => folBiimpl      (normalizeFormula f) (normalizeFormula g)
| folImpl        f g => folImpl        (normalizeFormula f) (normalizeFormula g)
| folDisjunction f g => folDisjunction (normalizeFormula f) (normalizeFormula g)
| folConjunction f g => folConjunction (normalizeFormula f) (normalizeFormula g)
| folEq s t          => folEq s t
| folApp (folLam f) arg => f arg
| folApp f arg => folApp (normalizeFormula f) arg
| x => x
end.

Definition normalizeTheory (thy: folTheory): folTheory := map normalizeFormula thy.
Definition normalizeSystem (sys: folSystem): folSystem := match sys with
| (sig, thy) => (sig, normalizeTheory thy)
end.

Require Import Coq.Program.Basics.
Fixpoint nth_power {X: Type} (f: X -> X) (n: nat): X -> X := match n with
| 0 => id
| S n' => compose f (nth_power f n')
end.

Definition normalizeSystemFull := nth_power normalizeSystem 15.

Definition dummyFormula := folForall "x" (folEq "todo" "todo").
