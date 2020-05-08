Require Import List.

Require Import String.
Open Scope string_scope.

Require Import bol.
Require Import fol.

(* BOL Semantics in terms of FOL *)
(* ============================= *)

(* 1. Signature Semantics *)
Fixpoint idSemantics (id: bolID): string := match id with
| fromString str => str
end.

Fixpoint declSemantics (decl: bolDecl): folDecl := match decl with
| bolIndDecl  id => bolIndSymbol (idSemantics id)
| bolConDecl  id => predicateSymbol (idSemantics id) 1
| bolRelDecl  id => predicateSymbol (idSemantics id) 2
| bolPropDecl id _ => predicateSymbol (idSemantics id) 2
end.

Fixpoint bolSignatureSemantics (bolSig: bolSignature): folSignature := map declSemantics bolSig.

(* 2. Theory Semantics *)
Fixpoint bolConSemantics (bolCon: bolConcept): folFormula := match bolCon with
| bolAtomicCon (fromString id) => folPredicateRef id
| bolConUnion c1 c2 => folLam (fun x => folDisjunction (folApp (bolConSemantics c1) x) (folApp (bolConSemantics c2) x))
| bolConIntersect c1 c2 => folLam (fun x => folConjunction (folApp (bolConSemantics c1) x) (folApp (bolConSemantics c2) x))
end.
Fixpoint bolIndSemantics (ind: bolInd): folTerm := match ind with
| fromID (fromString id) => folIndRef id
end.
Fixpoint bolRelSemantics (rel: bolRelation): folFormula := match rel with
| bolAtomicRel (fromString id) => folPredicateRef id
| bolRelUnion R1 R2 => folLam (fun i => folLam (fun j =>

    folDisjunction
      (folApp (folApp (bolRelSemantics R1) i) j)
      (folApp (folApp (bolRelSemantics R2) i) j)

  ))
end.

Fixpoint formulaSemantics (formula: bolFormula): folFormula := match formula with
| bolEq c1 c2 => folForall "x" (folBiimpl (folApp (bolConSemantics c1) "x") (folApp (bolConSemantics c2) "x"))
| bolSub c1 c2 => folForall "x" (folImpl (folApp (bolConSemantics c1) "x") (folApp (bolConSemantics c2) "x"))
| in_bolRel c1 R c2 => folApp (folApp (bolRelSemantics R) (bolIndSemantics c1)) (bolIndSemantics c2)
| _ => folForall "x" (folEq "x" "x")
end.

Fixpoint bolTheorySemantics (bolThy: bolTheory): folTheory := map formulaSemantics bolThy.

(* 3. Overall Semantics *)
Definition bolSemantics (bolOntology: bolOntology): folSystem := match bolOntology with
| (bolSig, bolTheory) => (bolSignatureSemantics bolSig, bolTheorySemantics bolTheory)
end.