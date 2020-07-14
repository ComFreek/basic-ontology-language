From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.
Require Import Coq.Program.Basics.
Open Scope program_scope.

Require Import bol.
Require Import fol.
Require Import sql.
Require Import boltofol.
Require Import boltosql.
Require Import foltotptp.

Definition sampleOntology : bolOntology :=
  SIGNATURE 
    CON "professor" ;;
    CON "lecturer" ;;
    CON "course" ;;

    REL "teaches" ;;
    REL "taughtat" ;;
    REL "responsiblefor" ;;
    PROP "ects" TYPE bolInt ;;
    PROP "hard" TYPE bolBool ;;

    IND "fr" ;;
    IND "wuv" ;;
    IND "fau" ;;
  END
  THEORY
    "wuv" HAS 5 OF "ects" ;;
    "wuv" IS-NOT "hard" ;;
    
    "wuv" IS-A "course" ;;
    
    "wuv" <."taughtat".> "fau" ;;

    "fr" IS-A "lecturer" ;;
    "fr" <."teaches" ; "taughtat".> "fau" ;;  (* FR teaches at least one course at FAU *)
    "lecturer" <<= ("course" forall "teaches") ;; (* lecturers only teach courses, nothing else *)
  END.

Definition sampleQuery: bolQuery := 
  (sampleOntology, "wuv" IS-A "course").

Definition bolToTPTP := folToTPTP ∘ bolToFol.
Definition bolQueryToTPTP := tptpQueryToString ∘ folQueryToTPTP ∘ bolQueryToFol.

Compute (bolQueryToFol sampleQuery).
Compute (bolQueryToTPTP sampleQuery).

Compute (prettyPrintSqlSystem (sqlSemantics sampleOntology)).

(* Question:

   with logics there is usually a nice distinction between signature and theory, right? (or perhaps not if you take MMT itself as a logic?)

   I don't see why "ind IS-A concept" should be part of the signature. Isn't it more natural (also for the derivation calculus!) to be a formula? In fact, some derivation rules need to add such things to the context. But adding to a signature seems strange.

   However, in SQL the distinction matters. If you specify an ontology with "ind IS-A concept", then the table for "concept" should contain "ind" (i.e., an INSERT INTO should have been generated) whereas as a formula no INSERT INTO should be generated.
*)


(* Design Decisions

(1) Formalize contexts as lists

    not as (Decl -> Type) * (Formula -> Type) functions as that doesn't allow generating fresh names

*)

(* Issues:

   TPTP has strict naming conventions: function and predicate symbols must adhere to regex [a-z]+ while quantified variables must adhere to [A-Z]+.
   
   Hence, I changed the name generation in boltofol, but ideally, we want to do alpha-renaming on FOL formulae within foltotptp.
   
   However, that would require an alpha-renaming machinery to be implemented for fol.
*)

