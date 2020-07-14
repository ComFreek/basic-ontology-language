Require Import List.

Require Import String.
Require Import Strings.String.
Require Import Strings.Ascii.
Open Scope string_scope.

Require Import utils.
Require Import fol.

Definition TPTPTheory := list string.
Definition TPTPTerm := string.
Definition TPTPFormula := string.
Definition TPTPSystem := list string.
Definition TPTPQuery := list string.

Module TPTPSemantics.

Fixpoint termSemantics (t: folTerm): TPTPTerm := match t with
| fromVar v => v
| folIndRef i => i
| folFunctionApp f args => match args with
  | nil => f  (* prevent empty parentheses like `f()` *)
  | _ => f ++ "(" ++ (concat ", " (map termSemantics args)) ++ ")"
end
end.

Fixpoint formulaSemantics (f: folFormula): TPTPFormula := match f with
| folForall v f => "![" ++ v ++ "] : (" ++ (formulaSemantics f) ++ ")"
| folExists v f => "?[" ++ v ++ "] : (" ++ (formulaSemantics f) ++ ")"
| folBiimpl f g => "(" ++ (formulaSemantics f) ++ ") <=> (" ++ (formulaSemantics g) ++ ")"
| folImpl   f g => "(" ++ (formulaSemantics f) ++ ") => (" ++ (formulaSemantics g) ++ ")"
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

Fixpoint folTheorySemantics (folThy: folTheory): TPTPTheory:= mapWithIndex
  (fun idx => fun f => "fof(" ++ (nat_to_string idx) ++ ", axiom, " ++ (formulaSemantics f) ++ ").") folThy.

End TPTPSemantics.

(* 3. Overall Semantics *)
Definition folToTPTP (folOntology: folSystem): TPTPSystem := match folOntology with
| (folSig, folTheory) => TPTPSemantics.folTheorySemantics folTheory
end.

Definition folQueryToTPTP (query: folQuery): TPTPQuery := match query with
| (system, formula) =>
    let tptpFormula := "fof(query, conjecture, " ++ (TPTPSemantics.formulaSemantics formula) ++ ")." in
    app (folToTPTP system) (cons newline (cons tptpFormula nil))
end.

Definition tptpSystemToString := concat newline.
Definition tptpQueryToString := concat newline.
