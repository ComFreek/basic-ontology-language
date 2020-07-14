Require Import List.

Require Import String.
Require Import Strings.String.
Require Import Strings.Ascii.
Open Scope string_scope.

Require Import utils.
Require Import fol.

Module TPTPSemantics.

Fixpoint termSemantics (t: folTerm): string := match t with
| fromVar v => v
| folIndRef i => i
| folFunctionApp f args => match args with
  | nil => f  (* prevent empty parentheses like `f()` *)
  | _ => f ++ "(" ++ (concat ", " (map termSemantics args)) ++ ")"
end
end.

Fixpoint formulaSemantics (f: folFormula): string := match f with
| folForall v f => "![" ++ v ++ "] " ++ formulaSemantics f
| folExists v f => "?[" ++ v ++ "] " ++ formulaSemantics f
| folBiimpl f g => "(" ++ (formulaSemantics f) ++ ") <=> (" ++ (formulaSemantics g)
| folImpl   f g => "(" ++ (formulaSemantics f) ++ ") => (" ++ (formulaSemantics g)
| folDisjunction f g => "(" ++ (formulaSemantics f) ++ ") | (" ++ (formulaSemantics g) ++ ")"
| folConjunction f g =>  "(" ++ (formulaSemantics f) ++ ") & (" ++ (formulaSemantics g) ++ ")"
| folEq s t => "(" ++ (termSemantics s) ++ ") = (" ++ (termSemantics t) ++ ")"

(* crappy code: manual uncurrying to nesting level 2

   because we cannot easily recurse on the result of an uncurrying helper function *)
| folApp f g => match f with
  | folApp h j => (formulaSemantics h) ++ "(" ++ (concat ", " (map termSemantics (j :: g :: nil))) ++ ")"
  | _ => (formulaSemantics f) ++ "(" ++ (termSemantics g) ++ ")"
  end
| folPredicateRef p => p
| folLam _ => "folLam to TPTP unsupported! Eliminate folLam first by running normalizeSystemFull."
end.

Fixpoint mapWithIndexHelper {A B: Type} (curIndex: nat) (f: nat -> A -> B) (l: list A): list B := match l with
| nil => nil
| cons x xs => cons (f curIndex x) (mapWithIndexHelper (S curIndex) f xs)
end.

Definition mapWithIndex {A B: Type} (f: nat -> A -> B) (l: list A): list B := mapWithIndexHelper 0 f l.

Fixpoint folTheorySemantics (folThy: folTheory): list string := mapWithIndex
  (fun idx => fun f => "fof(" ++ (nat_to_string idx) ++ ", axiom, " ++ (formulaSemantics f) ++ ")") folThy.

End TPTPSemantics.

(* 3. Overall Semantics *)
Definition folToTPTP (folOntology: folSystem): string := match folOntology with
| (folSig, folTheory) => concat newline (TPTPSemantics.folTheorySemantics folTheory)
end.
