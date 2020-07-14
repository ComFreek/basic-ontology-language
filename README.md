# Basic Ontology Language: an experimental ontology in Coq with many semantics

The **B**asic **O**ntology **L**anguage (BOL) is a toy language for designing ontologies made-up for educational purposes in a course on [knowledge representation and processing (WuV)](https://kwarc.info/courses/wuv/) by [Michael Kohlhase](https://kwarc.info/people/mkohlhase/) and [Florian Rabe](https://kwarc.info/people/frabe/).

This repository

- formalizes BOL
- a deductive semantics for BOL given by a derivation calculus
- a semantics BOL -> FOL
- a semantics BOL -> SQL
- a semantics FOL -> [TPTP](http://www.tptp.org/) (an interface language to feed FOL automatic theorem provers)

Sample BOL ontology as a Coq definition (and using a lot of notations):

```coq
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

Definition sampleQuery: bolQuery := (sampleOntology, "WuV" IS-A "course").

Definition bolQueryToTPTP := tptpQueryToString ∘ folQueryToTPTP ∘ bolQueryToFol.
Compute (bolQueryToTPTP sampleQuery).
```

Here, we see a semantics construction from BOL to FOL, to TPTP, and finally to a string.
The output is:

```
= "fof(0, axiom, ects(wuv, s(s(s(s(s(z))))))).
   fof(1, axiom, hard(wuv, false)).
   fof(2, axiom, course(wuv)).
   fof(3, axiom, taughtat(wuv, fau)).
   fof(4, axiom, lecturer(fr)).
   fof(5, axiom, ?[Z] : ((teaches(fr, Z)) & (taughtat(Z, fau)))).
   fof(6, axiom, ![X] : ((lecturer(X)) => (![Y] : ((teaches(X, Y)) => (course(Y)))))).

   fof(query, conjecture, course(wuv))."

     : string
```

This TPTP document can then be feed, for instance, to the [Vampire](https://vprover.github.io/) automatic theorem prover.

## Building and Usage

Install Coq and run

```
coqc utils.v -R . bol
coqc bol.v -R . bol
coqc bolcalc.v -R . bol
coqc fol.v -R . bol
coqc sql.v -R . bol

coqc boltofol.v -R . bol
coqc foltotptp.v -R . bol
coqc boltosql.v -R . bol

coqc main.v -R . bol
```

Copyable one-liner for PowerShell:

```
coqc utils.v -R . bol;coqc bol.v -R . bol;coqc bolcalc.v -R . bol;coqc fol.v -R . bol;coqc sql.v -R . bol;coqc boltofol.v -R . bol;coqc foltotptp.v -R . bol;coqc boltosql.v -R . bol;coqc main.v -R . bol;
```

Then you can seamlessly open `main.v` in CoqIDE (or other Coq IDEs) and step through it!

*TODO:* improve build system.
