Require Import List.
Open Scope list_scope.

Require Import String.
Open Scope string_scope.

Require Import bol.
Require Import fol.

(* BOL Semantics in terms of FOL *)
(* ============================= *)

Module FOLSemantics.

(* 1. Signature Semantics *)
Fixpoint idSemantics (id: bolID): string := match id with
| fromString str => str
end.

Fixpoint declSemantics (decl: bolDecl): folDecl := match decl with
| bolIndDecl  id => folIndSymbol (idSemantics id)
| bolConDecl  id => predicateSymbol (idSemantics id) 1
| bolRelDecl  id => predicateSymbol (idSemantics id) 2
| bolPropDecl id _ => predicateSymbol (idSemantics id) 2
end.

Fixpoint bolSignatureSemantics (bolSig: bolSignature): folSignature := map declSemantics bolSig.

(* 2. Theory Semantics *)
Fixpoint bolIndSemantics (ind: bolInd): folTerm := match ind with
| fromID (fromString id) => folIndRef id
end.

Fixpoint bolConSemantics (bolCon: bolConcept): folFormula := match bolCon with
| bolAtomicCon (fromString id) => folPredicateRef id
| bolConUnion c1 c2 => folLam (fun x => folDisjunction (folApp (bolConSemantics c1) x) (folApp (bolConSemantics c2) x))
| bolConIntersect c1 c2 => folLam (fun x => folConjunction (folApp (bolConSemantics c1) x) (folApp (bolConSemantics c2) x))
| bolRelDom R => folLam (fun x => folExists "Y" (folApp (folApp (bolRelSemantics R) x) "Y"))
| bolRelCod R => folLam (fun y => folExists "X" (folApp (folApp (bolRelSemantics R) "X") y))
| bolConForall R c => folLam (fun x =>
    folForall "Y" (
      folImpl
        (folApp (folApp (bolRelSemantics R) x) "Y")
        (folApp (bolConSemantics c) "Y")
    )
  )
| bolConExists R c => folLam (fun x =>
    folExists "Y" (
      folConjunction
        (folApp (folApp (bolRelSemantics R) x) "Y")
        (folApp (bolConSemantics c) "Y")
    )
  )
end

with bolRelSemantics (rel: bolRelation): folFormula := match rel with
| bolAtomicRel (fromString id) => folPredicateRef id
| bolRelUnion R1 R2 => folLam (fun i => folLam (fun j =>
    folDisjunction
      (folApp (folApp (bolRelSemantics R1) i) j)
      (folApp (folApp (bolRelSemantics R2) i) j)
  ))
| bolRelComp R1 R2 => folLam (fun i => folLam (fun j =>
    folExists "Z" (
      folConjunction 
        (folApp (folApp (bolRelSemantics R1) i) "Z")
        (folApp (folApp (bolRelSemantics R2) "Z") j)
    )))
| bolRelInv R => folLam (fun i => folLam (fun j =>
    folApp (folApp (bolRelSemantics R) j) i
  ))
| bolRelTrans R => dummyFormula
| bolRelDiag c => folLam (fun i => folLam (fun j =>
    folConjunction (folApp (bolConSemantics c) i) (folEq i j)
  ))
end.

Fixpoint bolPropSemantics (prop: bolProp): folFormula := match prop with
| bolAtomicProp (fromString id) => folPredicateRef id
end.

Fixpoint naturalNumberSemantics (n: nat): folTerm := match n with
| 0 => folFunctionApp "z" nil
| S n' => folFunctionApp "s" (cons (naturalNumberSemantics n') nil)
end.

Fixpoint bolValueSemantics (val: bolValue): folTerm := match val with
| bolNaturalNumberValue n => naturalNumberSemantics n
| bolBoolValue true => folIndRef "true"
| bolBoolValue false => folIndRef "false"
end.

Fixpoint formulaSemantics (formula: bolFormula): folFormula := match formula with
| bolEq c1 c2 => folForall "X" (folBiimpl (folApp (bolConSemantics c1) "X") (folApp (bolConSemantics c2) "X"))
| bolSub c1 c2 => folForall "X" (folImpl (folApp (bolConSemantics c1) "X") (folApp (bolConSemantics c2) "X"))
| bolInRel c1 R c2 => folApp (folApp (bolRelSemantics R) (bolIndSemantics c1)) (bolIndSemantics c2)
| bolIsA ind c => folApp (bolConSemantics c) (bolIndSemantics ind)
| bolHasPropValue i P v => folApp (folApp (bolPropSemantics P) (bolIndSemantics i)) (bolValueSemantics v)
end.

Fixpoint bolTheorySemantics (bolThy: bolTheory): folTheory := map formulaSemantics bolThy.

End FOLSemantics.

(* 3. Overall Semantics *)
Definition bolToFol (bolOntology: bolOntology): folSystem := normalizeSystemFull (match bolOntology with
| (bolSig, bolTheory) => (FOLSemantics.bolSignatureSemantics bolSig, FOLSemantics.bolTheorySemantics bolTheory)
end).
Check fst.
Definition bolQueryToFol (query: bolQuery): folQuery := match query with
| (bolContext, bolFormula) => match (bolToFol bolContext) with
(* Problem here is that folFormula does not need to be normalized

   => pack it into a system and call normalizeSystemFull, then extract via last (TODO this is brittle)
*)
   
   (folSignature, folTheory) => let folFormula := FOLSemantics.formulaSemantics bolFormula in 
   
    match (normalizeSystemFull (folSignature, (folTheory ++ (cons folFormula nil))%list)) with
    | (_, newTheory) => ((folSignature, folTheory), last newTheory folFormula)
    end
  end
end.
