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
Require Import sql.
Require Import boltofol.
Require Import boltosql.

Definition sampleOntology : bolOntology :=
  SIGNATURE 
    CON "professor" ;;
    CON "lecturer" ;;
    CON "course" ;;

    REL "teaches" ;;
    REL "taught-at" ;;
    REL "responsible for" ;;
    PROP "ects" TYPE bolInt ;;
    PROP "hard" TYPE bolBool ;;

    IND "FR" ;;
    IND "WuV" ;;
    IND "FAU" ;;
  END
  THEORY
    "WuV" HAS 5 OF "ects" ;;
    "WuV" IS-NOT "hard" ;;
    
    "WuV" <."taught-at".> "FAU" ;;

    "FR" IS-A "lecturer" ;;
    "FR" <."teaches" ; "taught-at".> "FAU" ;;  (* FR teaches at least one course at FAU *)
    "lecturer" <<= ("course" forall "teaches") ;; (* lecturers only teach courses, nothing else *)
  END.

Compute (folSemantics sampleOntology).
Compute (prettyPrintSqlSystem (sqlSemantics sampleOntology)).

