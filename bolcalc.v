(* BOL Derivation Calculus *)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import bol.
Require Import fol.
Require Import boltofol.

Reserved Notation "Gamma '|-' f" (at level 65).

Definition context (declType: Type) (formulaType: Type) := ((declType -> Prop) * (formulaType -> Prop))%type.
Definition bolContext := context bolDecl bolFormula.

Definition ctxDeclCons {declType formulaType} ctx d: context declType formulaType := match ctx with
| (decls, formulae) => (fun e => (decls d) \/ d = e, formulae)
end.

Definition ctxFormulaCons {declType formulaType} ctx f: context declType formulaType  := match ctx with
| (decls, formulae) => (decls, fun g => (formulae f) \/ f = g)
end.

Notation "ctx ',' f" := (ctxFormulaCons ctx f) (at level 64).
Notation "ctx '+++' f" := (ctxDeclCons ctx f) (at level 64).

Inductive fresh: bolContext -> bolID -> Prop :=.

Inductive bolDerivable : bolContext -> bolFormula -> Prop :=
(*  | var: forall (decls: bolDecl -> Prop) (formulae: bolFormula -> Prop) (ctx: context bolDecl bolFormula) (f: bolFormula),
      ctx = (decls, formulae) -> formulae f -> ctx |- f*)
  | eq: forall (ctx: bolContext) (F: bolConcept -> bolFormula) c d,
      ctx |- (F c) -> ctx |- c == d -> ctx |- (F d)

  | subIntro: forall ctx c d e,
      ctx |- c <<= d -> ctx |- d <<= e -> ctx |- c <<= e
  | subElim: forall ctx ind c d,
      ctx |- c <<= d -> ctx |- ind IS-A c -> ctx |- ind IS-A d

  | conUnionIntroL: forall ctx ind c d,
      ctx |- ind IS-A c -> ctx |- ind IS-A (c U d)
  | conUnionIntroR: forall ctx ind c d,
      ctx |- ind IS-A d -> ctx |- ind IS-A (c U d)
  | conUnionElim: forall ctx ind c d f,
         ctx |- ind IS-A (c U d)
      -> ctx, ind IS-A c |- f
      -> ctx, ind IS-A d |- f
      -> ctx |- f

  | conIntersectIntro: forall ctx ind c d,
      ctx |- ind IS-A c -> ctx |- ind IS-A d -> ctx |- ind IS-A (c C d)
  | conIntersectElimL: forall ctx ind c d,
      ctx |- ind IS-A (c C d) -> ctx |- ind IS-A c
  | conIntersectElimR: forall ctx ind c d,
      ctx |- ind IS-A (c C d) -> ctx |- ind IS-A d

  | relUnionIntroL: forall ctx i j R1 R2,
      ctx |- i <.R1.> j -> ctx |- i <.R1 u R2.> j
  | relUnionIntroR: forall ctx i j R1 R2,
      ctx |- i <.R2.> j -> ctx |- i <.R1 u R2.> j
  | relUnionElim: forall ctx i j R1 R2 f,
         ctx |- i <.R1 u R2.> j
      -> ctx, i <.R1.> j |- f
      -> ctx, i <.R2.> j |- f
      -> ctx |- f

  | relInvIntro: forall ctx i j R,
      ctx |- i <.R.> j -> ctx |- j <.inv R.> i
  | relInvElim: forall ctx i j R,
      ctx |- i <.inv R.> j -> ctx |- j <.R.> i

  | relCompIntro: forall ctx i j k R1 R2,
      ctx |- i <.R1.> j -> ctx |- j <.R2.> k -> ctx |- i <.R1;R2.> k
  | relCompElim: forall ctx i j k R1 R2 f,
         ctx |- i <.R1;R2.> k
      -> fresh ctx j
      -> ctx +++ (IND j), i <.R1.> j, j <.R2.> k |- f
      -> ctx |- f

  | relDomIntro: forall ctx i j R,
      ctx |- i <.R.> j -> ctx |- i IS-A (dom R)
  | relDomElim: forall ctx i j R f,
        ctx |- i IS-A (dom R)
     -> fresh ctx j
     -> ctx +++ IND j, (i <.R.> j) |- f
     -> ctx |- f

  | relCodIntro: forall ctx i j R,
      ctx |- i <.R.> j -> ctx |- j IS-A (cod R)
  | relCodElim: forall ctx i (j: bolID) R f,
         ctx |- j IS-A (dom R)
      -> fresh ctx j
      -> ctx +++ IND j, (i <.R.> j) |- f
      -> ctx |- f

  | relForallIntro: forall ctx c R i j,
         fresh ctx j
      -> ctx +++ IND j, i <.R.> j |- j IS-A c
      -> ctx |- j IS-A (c forall R)
  | relForallElim: forall ctx c R i j,
         ctx |- i IS-A (c forall R)
      -> ctx |- i <.R.> j
      -> ctx |- j IS-A c

  | relExistsIntro: forall ctx c R i j,
         ctx |- i <.R.> j
      -> ctx |- j IS-A c
      -> ctx |- i IS-A (c exists R)
  | relExistsElim: forall ctx c R i j f,
         ctx |- i IS-A (c exists R)
      -> fresh ctx j
      -> ctx +++ IND j, i <.R.> j, j IS-A c |- f
      -> ctx |- f

  where "Gamma '|-' f" := (bolDerivable Gamma f).

Reserved Notation "Gamma '|--' f" (at level 65).
Definition folContext := context folDecl folFormula.
Inductive folDerivable : folContext -> folFormula -> Prop :=
  where "Gamma '|--' f" := (folDerivable Gamma f).

Require Import Coq.Lists.List.

Definition ctxFromSystem {declType folType: Type} (system: (list declType) * (list folType)): context declType folType := match system with
(* strangely, (sig, thy) pattern matching doesn't work here *)
| pair sig thy => pair (fun a => False) (fun b => False)
end.

Notation "'^' sys" := (ctxFromSystem sys) (at level 50).
Notation "'[[' ontology ']]'" := (bolSemantics ontology) (at level 45).

(* probably true *)
Theorem correctness: forall (ontology: bolOntology) f,
  ^ontology |- f -> ^[[ontology]] |-- formulaSemantics f.
  move => ontology f; elim => //. (* lol due to folDerivable being empty *)
Qed.

(* probably not true *)
Theorem completeness: forall (ontology: bolOntology) f,
  ^[[ontology]] |-- formulaSemantics f -> ^ontology |- f.
Admitted.