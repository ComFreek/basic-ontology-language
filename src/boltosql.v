Require Import bol.
Require Import sql.

Require Import List.
Import ListNotations.

Require Import String.
Open Scope string_scope.

(* BOL Semantics in terms of SQL *)
(* ============================= *)

Module SQLSemantics.

(* 1. Signature Semantics *)
Definition idSemantics (id: bolID): string := match id with
| fromString str => str
end.

Definition typeSemantics (tp: bolType): sqlColumnType := match tp with
| bolInt => sqlIntType
| bolString => sqlStringType
| _ => sqlUnknownType (* todo *)
end.

Definition declSemantics (decl: bolDecl): sqlDecl := match decl with
| bolIndDecl  id => sqlInsert "individuals" [(idSemantics id)]
| bolConDecl  id => sqlTableDecl (idSemantics id) [("ind", sqlStringType)]
| bolRelDecl  id => sqlTableDecl (idSemantics id) ([("sub", sqlStringType)] ++ [("obj", sqlStringType)])
| bolPropDecl id tp => sqlTableDecl (idSemantics id) ([("ind", sqlStringType)] ++ [("val", (typeSemantics tp))])
end.

Definition bolSignatureSemantics (bolSig: bolSignature): sqlSignature := map declSemantics bolSig.

(* 2. Theory Semantics *)
Definition bolIndSemantics (ind: bolInd): string := match ind with
| fromID (fromString id) => id
end.

Definition sqlDummyQuery := sqlProj sqlAllColumns (sqlTable "???").

Fixpoint bolConSemantics (bolCon: bolConcept): sqlQuery := match bolCon with
| bolAtomicCon (fromString id) => sqlProj sqlAllColumns (sqlTable id)
| bolConUnion c1 c2 => sqlUnion (bolConSemantics c1) (bolConSemantics c2)
| bolConIntersect c1 c2 => sqlIntersect (bolConSemantics c1) (bolConSemantics c2)
| bolRelDom R => sqlProj (sqlDistinct (sqlColumnList ["sub"])) (bolRelSemantics R)
| bolRelCod R => sqlProj (sqlDistinct (sqlColumnList ["obj"])) (bolRelSemantics R)
| bolConForall R c => sqlDummyQuery
| bolConExists R c => sqlDummyQuery
end

with bolRelSemantics (rel: bolRelation): sqlQuery := match rel with
| bolAtomicRel (fromString id) => sqlProj sqlAllColumns (sqlTable id)
| bolRelUnion R1 R2 => sqlUnion (bolRelSemantics R1) (bolRelSemantics R2)
| bolRelComp R1 R2 => sqlDummyQuery
| bolRelInv R => sqlProj (sqlColumnList (["obj"] ++ ["sub"])) (bolRelSemantics R)
| bolRelTrans R => sqlDummyQuery
| bolRelDiag c => sqlProj (sqlColumnList (["ind"] ++ ["ind"])) (bolConSemantics c)
end.

Definition bolPropSemantics (prop: bolProp): sqlQuery := match prop with
| bolAtomicProp (fromString id) => sqlProj sqlAllColumns id
end.

Definition bolValueSemantics (val: bolValue): sqlScalarExpression := match val with
| bolNaturalNumberValue n => sqlNaturalNumber n
| bolBoolValue true => sqlTrue
| bolBoolValue false => sqlFalse
end.

Definition formulaSemantics (formula: bolFormula): sqlQuery := match formula with
| bolEq c1 c2 => let s1 := bolConSemantics c1 in let s2 := bolConSemantics c2 in
    sqlUnion (sqlExcept s1 s2) (sqlExcept s2 s1)
| bolSub c1 c2 => sqlExcept (bolConSemantics c1) (bolConSemantics c2)
| bolInRel i1 R i2 =>
    sqlSelect sqlAllColumns (bolRelSemantics R) (sqlAnd (sqlEq "sub" (bolIndSemantics i1)) (sqlEq "obj" (bolIndSemantics i2)))
| bolIsA ind c => sqlSelect sqlAllColumns (bolConSemantics c) (sqlEq "ind" (bolIndSemantics ind))
| bolHasPropValue i P v => sqlSelect sqlAllColumns (bolPropSemantics P) (sqlAnd (sqlEq "ind" (bolIndSemantics i)) (sqlEq "val" (bolValueSemantics v)))
end.

Definition bolTheorySemantics (bolThy: bolTheory): sqlTheory := map formulaSemantics bolThy.

End SQLSemantics.

(* 3. Overall Semantics *)
Definition sqlSemantics (bolOntology: bolOntology): sqlSystem := match bolOntology with
| (bolSig, bolTheory) => (SQLSemantics.bolSignatureSemantics bolSig, SQLSemantics.bolTheorySemantics bolTheory)
end.