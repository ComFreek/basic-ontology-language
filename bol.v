Require Import List.

Require Import String.

Inductive bolDecl :=
    | bolIndDecl: bolID -> bolDecl
    | bolConDecl: bolID -> bolDecl
    | bolRelDecl: bolID -> bolDecl
    | bolPropDecl: bolID -> bolType -> bolDecl
  with bolFormula :=
    | bolEq: bolConcept -> bolConcept -> bolFormula
    | bolSub: bolConcept -> bolConcept -> bolFormula
    | is_a: bolID -> bolConcept -> bolFormula
    | in_bolRel: bolInd -> bolRelation -> bolInd -> bolFormula
  with bolInd := fromID: bolID -> bolInd
  with bolConcept :=
    | bolAtomicCon: bolID -> bolConcept
    | bolConUnion: bolConcept -> bolConcept -> bolConcept
    | bolConIntersect: bolConcept -> bolConcept -> bolConcept
    (* missing cases *)
  with bolRelation :=
    | bolAtomicRel: bolID -> bolRelation
    | bolRelUnion: bolRelation -> bolRelation -> bolRelation
    (* missing cases *)
  with bolID :=
    | fromString: string -> bolID
  with bolType := bolInt|bolFloat|bolBool|bolString.

Definition string_to_bolID := fun str => fromString str.
Definition bolID_to_ind := fun id => fromID id.
Definition bolID_to_rel := fun id => bolAtomicRel id.
Definition bolID_to_con := fun id => bolAtomicCon id.

Coercion string_to_bolID: string >-> bolID.
Coercion bolID_to_ind:    bolID  >-> bolInd.
Coercion bolID_to_rel:    bolID  >-> bolRelation.
Coercion bolID_to_con:    bolID  >-> bolConcept.

Definition bolSignature := list bolDecl.
Definition bolTheory := list bolFormula.
Definition bolOntology := (bolSignature * bolTheory)%type.

Notation "'CON' i"  := (bolConDecl i) (at level 60).
Notation "'IND' i"  := (bolIndDecl i) (at level 60).
Notation "'REL' i"  := (bolRelDecl i) (at level 60).
Notation "'PROP' i" := (bolPropDecl i) (at level 60).

Notation "c1 '==' c2" := (bolEq c1 c2) (at level 60).
Notation "c1 '<<=' c2" := (bolSub c1 c2) (at level 60).
Notation "i 'IS-A' c" := (is_a i c) (at level 60).
Notation "i '<.' R '.>' j" := (in_bolRel i R j) (at level 60).

Notation "c1 'U' c2" := (bolConUnion c1 c2) (at level 60).
Notation "c1 'C' c2" := (bolConIntersect c1 c2) (at level 60).

Notation "r1 'u' r2" := (bolRelUnion r1 r2) (at level 60).

Notation "d1 ';;' d2" :=  (cons d1 d2) (at level 80, right associativity). (* ended by notation END below *)
Notation "'SIGNATURE' decls 'THEORY' formulae" := (decls, formulae) (at level 80, right associativity).
Notation "'END'" := nil (at level 60).