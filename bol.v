Require Import List.

Require Import String.

Inductive bolType := bolInt|bolFloat|bolBool|bolString.
Inductive bolID := fromString: string -> bolID.
Inductive bolInd := fromID: bolID -> bolInd.

Inductive bolConcept :=
    | bolAtomicCon: bolID -> bolConcept
    | bolConUnion: bolConcept -> bolConcept -> bolConcept
    | bolConIntersect: bolConcept -> bolConcept -> bolConcept
    | bolRelDom: bolRelation -> bolConcept
    | bolRelCod: bolRelation -> bolConcept
    | bolConForall: bolRelation -> bolConcept -> bolConcept
    | bolConExists: bolRelation -> bolConcept -> bolConcept
  with bolRelation :=
    | bolAtomicRel: bolID -> bolRelation
    | bolRelUnion: bolRelation -> bolRelation -> bolRelation
    | bolRelComp: bolRelation -> bolRelation -> bolRelation
    | bolRelInv: bolRelation -> bolRelation
    | bolRelTrans: bolRelation -> bolRelation
    | bolRelDiag: bolConcept -> bolRelation.

Inductive bolProp :=
    | bolAtomicProp: bolID -> bolProp.

Inductive bolValue :=
    | bolNaturalNumberValue: nat -> bolValue
    | bolBoolValue: bool -> bolValue.

Inductive bolDecl :=
    | bolIndDecl: bolID -> bolDecl
    | bolConDecl: bolID -> bolDecl
    | bolRelDecl: bolID -> bolDecl
    | bolPropDecl: bolID -> bolType -> bolDecl.

Inductive bolFormula :=
    | bolEq: bolConcept -> bolConcept -> bolFormula
    | bolSub: bolConcept -> bolConcept -> bolFormula
    | bolIsA: bolInd -> bolConcept -> bolFormula
    | bolInRel: bolInd -> bolRelation -> bolInd -> bolFormula
    | bolHasPropValue: bolInd -> bolProp -> bolValue -> bolFormula.

Definition string_to_bolID := fun str => fromString str.
Definition bolID_to_ind := fun id => fromID id.
Definition bolID_to_rel := fun id => bolAtomicRel id.
Definition bolID_to_con := fun id => bolAtomicCon id.
Definition bolID_to_prop := fun id => bolAtomicProp id.

Coercion string_to_bolID: string >-> bolID.
Coercion bolID_to_ind:    bolID  >-> bolInd.
Coercion bolID_to_rel:    bolID  >-> bolRelation.
Coercion bolID_to_con:    bolID  >-> bolConcept.
Coercion bolID_to_prop:   bolID  >-> bolProp.

Definition nat_to_value := fun n => bolNaturalNumberValue n.
Coercion nat_to_value: nat >-> bolValue.

Definition bolSignature := list bolDecl.
Definition bolTheory := list bolFormula.
Definition bolOntology := (bolSignature * bolTheory)%type.

Notation "'CON' i"  := (bolConDecl i) (at level 60).
Notation "'IND' i"  := (bolIndDecl i) (at level 60).
Notation "'REL' i"  := (bolRelDecl i) (at level 60).
Notation "'PROP' i 'TYPE' t" := (bolPropDecl i t) (at level 60).

Notation "c1 '==' c2" := (bolEq c1 c2) (at level 60).
Notation "c1 '<<=' c2" := (bolSub c1 c2) (at level 60).
Notation "i 'IS-A' c" := (bolIsA i c) (at level 60).
Notation "i '<.' R '.>' j" := (bolInRel i R j) (at level 60).
Notation "i 'HAS' v 'OF' P" := (bolHasPropValue i P v) (at level 60).
Notation "i 'IS' P" := (bolHasPropValue i P (bolBoolValue true)) (at level 60).
Notation "i 'IS-NOT' P" := (bolHasPropValue i P (bolBoolValue false)) (at level 60).

Notation "c1 'U' c2" := (bolConUnion c1 c2) (at level 60).
Notation "c1 'C' c2" := (bolConIntersect c1 c2) (at level 60).
Notation "'dom' R" := (bolRelDom R) (at level 60).
Notation "'cod' R" := (bolRelCod R) (at level 60).
Notation "c 'forall' R" := (bolConForall R c) (at level 60).
Notation "c 'exists' R" := (bolConExists R c) (at level 60).

Notation "R1 'u' R2" := (bolRelUnion R1 R2) (at level 60).
Notation "R1 ';' R2" := (bolRelComp R1 R2) (at level 60).
Notation "R '*'" := (bolRelTrans R) (at level 60).
Notation "'inv' R" := (bolRelInv R) (at level 60).

Notation "d1 ';;' d2" :=  (cons d1 d2) (at level 80, right associativity, only parsing). (* ended by notation END below *)
Notation "'SIGNATURE' decls 'THEORY' formulae" := (decls, formulae) (at level 80, right associativity, only parsing).
Notation "'END'" := nil (at level 60, only parsing).

Definition bolDeclId (decl: bolDecl): bolID := match decl with
| bolIndDecl id => id
| bolConDecl id => id
| bolRelDecl id => id
| bolPropDecl id _ => id
end.

Definition bolIdEq (id id': bolID): bool := match id with
| fromString s => match id' with
  | fromString s' => eqb s s'
  end
end.