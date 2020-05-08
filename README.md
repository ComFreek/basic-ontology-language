# WuV homework: BOL to FOL in Coq

The **B**asic **O**ntology **L**anguage (BOL) is a toy language for designing ontologies made-up for educational purposes in a course on [knowledge representation and processing (WuV)](https://kwarc.info/courses/wuv/) by [Michael Kohlhase](https://kwarc.info/people/mkohlhase/) and [Florian Rabe](https://kwarc.info/people/frabe/). On the other hand, **F**irst-**O**rder **L**ogic (FOL) is a well-known logic. The homework was to give semantics of BOL in terms of FOL in your favorite digital system. I chose Coq.

Sample BOL ontology as a Coq definition (and using a lot of notations):

```
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
```

The semantics interpretation applied via

```
Compute (normalizeSystemFull (bolSemantics sampleOntology)).
```

gives the following output:

```
= SIGNATURE predicateSymbol "professor" 1;;
            predicateSymbol "lecturer" 1;;
            predicateSymbol "course" 1;;
            predicateSymbol "teaches" 2;;
            predicateSymbol "responsible for" 2;;
            bolIndSymbol "FR";; bolIndSymbol "WuV";; END
  THEORY folDisjunction
           (folApp (folApp (folPredicateRef "teaches") (folIndRef "FR"))
              (folIndRef "WuV"))
           (folApp
              (folApp (folPredicateRef "responsible for")
                 (folIndRef "FR")) (folIndRef "WuV"));;
         folForall "x"
           (folBiimpl
              (folApp (folPredicateRef "lecturer") (fromVar "x"))
              (folApp (folPredicateRef "professor") (fromVar "x")));;
         END
: folSystem
```

This is a tuple of a FOL signature and a theory thereover. The numbers specified together with the predicate symbol denote their arity.

## Building and Usage

Install Coq and run

```
coqc bol.v -R . boltofol
coqc fol.v -R . boltofol
coqc boltofol.v -R . boltofol
coqc main.v -R . boltofol
```

Copyable one-liner for PowerShell:

```
$env:Path += ";C:\Coq\bin" ; coqc bol.v -R . boltofol ; coqc fol.v -R . boltofol ; coqc boltofol.v -R . boltofol ; coqc main.v -R . boltofol
```

Then you can seamlessly open `main.v` in CoqIDE (or other Coq IDEs) and step through it!

