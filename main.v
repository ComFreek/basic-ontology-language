From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Import bol.
Require Import fol.
Require Import boltofol.

Definition sampleOntology : bolOntology :=
  SIGNATURE 
    CON "professor" ;;
    CON "lecturer" ;;
    CON "course" ;;
    REL "teaches" ;;
    REL "responsible for" ;;
    
    IND "FR" ;;
    IND "WuV" ;;
  END
  THEORY
    "FR" <."teaches" u "responsible for".> "WuV" ;;
    "lecturer" == "professor" ;;
  END.

Compute (normalizeSystemFull (bolSemantics sampleOntology)).
