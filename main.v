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

(* Question:

   with logics there is usually a nice distinction between signature and theory, right? (or perhaps not if you take MMT itself as a logic?)

   I don't see why "ind IS-A concept" should be part of the signature. Isn't it more natural (also for the derivation calculus!) to be a formula? In fact, some derivation rules need to add such things to the context. But adding to a signature seems strange.

   However, in SQL the distinction matters. If you specify an ontology with "ind IS-A concept", then the table for "concept" should contain "ind" (i.e., an INSERT INTO should have been generated) whereas as a formula no INSERT INTO should be generated.
*)

