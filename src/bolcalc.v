(* BOL Derivation Calculus *)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import bol.
Require Import fol.
Require Import boltofol.

(* for dependent induction *)
Require Import Coq.Program.Equality.

Reserved Notation "Gamma '|-' f" (at level 65).

Definition context (declType: Type) (formulaType: Type) := ((declType -> Prop) * (formulaType -> Prop))%type.
Definition emptyContext {D F} : context D F := (fun _ => False, fun _ => False).

Definition bolContext := context bolDecl bolFormula.

Definition ctxDeclCons {declType formulaType} ctx d: context declType formulaType := match ctx with
| (decls, formulae) => (fun e => (decls d) \/ d = e, formulae)
end.

Definition ctxFormulaCons {declType formulaType} ctx f: context declType formulaType  := match ctx with
| (decls, formulae) => (decls, fun g => (formulae g) \/ g = f)
end.

Notation "ctx ',,' f" := (ctxFormulaCons ctx f) (at level 64).
Notation "ctx '+++' f" := (ctxDeclCons ctx f) (at level 64).

Open Scope string_scope.

Inductive fresh: bolContext -> bolID -> Prop :=
  | freshEmpty: forall id, fresh emptyContext id
  | freshDecl: forall ctx id decl,
        fresh ctx id
     -> ~(bolIdEq id (bolDeclId decl))
     -> fresh (ctx +++ decl) id.

(* Definition generateFreshID (ctx: bolContext) -> bolID := ??? *)

Inductive bolDerivable : bolContext -> bolFormula -> Prop :=
  | ax: forall (ctx: bolContext) f,
      snd ctx f -> ctx |- f

  | eqIntro: forall ctx c d i j,
         fresh ctx i
      -> fresh ctx j
      -> ctx,, i IS-A c |- i IS-A d
      -> ctx,, j IS-A d |- j IS-A c
      -> ctx |- c == d

  | eqElim: forall (ctx: bolContext) (F: bolConcept -> bolFormula) c d,
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
      -> ctx,, ind IS-A c |- f
      -> ctx,, ind IS-A d |- f
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
      -> ctx,, i <.R1.> j |- f
      -> ctx,, i <.R2.> j |- f
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
      -> ctx +++ (IND j),, i <.R1.> j,, j <.R2.> k |- f
      -> ctx |- f

  | relDomIntro: forall ctx i j R,
      ctx |- i <.R.> j -> ctx |- i IS-A (dom R)
  | relDomElim: forall ctx i j R f,
        ctx |- i IS-A (dom R)
     -> fresh ctx j
     -> ctx +++ IND j,, (i <.R.> j) |- f
     -> ctx |- f

  | relCodIntro: forall ctx i j R,
      ctx |- i <.R.> j -> ctx |- j IS-A (cod R)
  | relCodElim: forall ctx i (j: bolID) R f,
         ctx |- j IS-A (dom R)
      -> fresh ctx j
      -> ctx +++ IND j,, (i <.R.> j) |- f
      -> ctx |- f

  | relForallIntro: forall ctx c R i j,
         fresh ctx j
      -> ctx +++ IND j,, i <.R.> j |- j IS-A c
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
      -> ctx +++ IND j,, i <.R.> j,, j IS-A c |- f
      -> ctx |- f

  where "Gamma '|-' f" := (bolDerivable Gamma f).

Require Import String.
Require Import Strings.String.
Open Scope string_scope.

Theorem thm: emptyContext,, "i" IS-A "C",, ("C" <<= "D") |- ("i" IS-A "D").
Proof.
  apply: subElim.
  - apply: ax. simpl.
    by apply: or_intror.
  - apply: ax. simpl. 
    by apply: or_introl; apply: or_intror.
Qed.

Lemma doubleInvEquiv: forall ctx i R j, ctx |- i <.inv (inv R).> j <-> ctx |- i <.R.> j.
Proof.
  move => ctx i R j.
  split => [H|H].
  - by do 2! apply: relInvElim.
  - by do 2! apply: relInvIntro.
Qed.

Definition isContextSubset {declType formType: Type} (ctx ctx': context declType formType) := (forall d, ctx.1 d -> ctx'.1 d) /\ (forall f, ctx.2 f -> ctx'.2 f).

Lemma largerContext: forall ctx ctx' f, isContextSubset ctx ctx' -> ctx |- f -> ctx' |- f.
Proof.
  move => ctx ctx' f Hsubset der.
  elim: der f Hsubset ctx'.
  - 
  induction der => //.
  - admit.
  -  
  remember ctx in der.
  remember f in der.
  elim: der => //.
  - 
  dependent induction der => //.
  - by apply: ax; apply: (snd Hsubset).
  - admit.
  - admit.
  - apply: subIntro. 
    * by apply: IHder1. 
    * by apply: IHder2. 
  - apply: subElim.
    * by apply: IHder1.
    * by apply: IHder2.
  - (* ... *)
Admitted.

Create HintDb bolcalc.
Hint Immediate largerContext : bolcalc.

Lemma trivialContextSubset {declType formType: Type}: forall (ctx: context declType formType) f, isContextSubset ctx (ctx,, f).
Proof.
Admitted.

Hint Immediate trivialContextSubset : bolcalc.

Lemma trivialAx: forall ctx f, ctx,, f |- f.
Proof.
  move => ctx f.
  apply: ax.
  case: ctx; simpl.
  auto.
Qed.

Hint Immediate trivialAx : bolcalc.

Lemma subsetAsymmetry: forall ctx c d, ctx |- c <<= d -> ctx |- d <<= c -> ctx |- c == d.
Proof.
  move => ctx c d H J.
  apply: eqIntro.
  - admit.
  - admit.
  - apply: subElim.
    + apply: largerContext => //.
      * auto with bolcalc.
      * exact H.
    + apply: subElim.
      * apply: largerContext; auto with bolcalc; exact J.
      * apply: subElim.
        apply: largerContext; auto with bolcalc; exact H.
        auto with bolcalc.
  - apply: subElim.
    + apply: largerContext => //.
      * auto with bolcalc.
      * exact J.
    + apply: subElim.
      * apply: largerContext; auto with bolcalc; exact H.
      * apply: subElim.
        apply: largerContext; auto with bolcalc; exact J.
        auto with bolcalc.
Admitted.

Definition folContext := context folDecl folFormula.

Reserved Notation "Gamma '|--' f" (at level 65).

Inductive folFresh: folContext -> string -> Prop :=.

Fixpoint folSubstituteInTerm (v: folVariable) (e: folTerm) (t: folTerm): folTerm := match t with
| fromVar w => if (string_dec v w) then e else t
| x => x
end.

Fixpoint folSubstitute (v: folVariable) (e: folTerm) (f: folFormula): folFormula := match f with
| folForall      w f => folForall w    (normalizeFormula f)
| folExists      w f => folExists w    (normalizeFormula f)
| folBiimpl      f g => folBiimpl      (folSubstitute v e f) (folSubstitute v e g)
| folImpl        f g => folImpl        (folSubstitute v e f) (folSubstitute v e g)
| folDisjunction f g => folDisjunction (folSubstitute v e f) (folSubstitute v e g)
| folConjunction f g => folConjunction (folSubstitute v e f) (folSubstitute v e g)
| folEq s t          => folEq (folSubstituteInTerm v e s) (folSubstituteInTerm v e t)
| folApp f arg       => folApp (folSubstitute v e f) (folSubstituteInTerm v e arg)
| folLam _           => dummyFormula
| _                  => f
end.

Inductive folDerivable : folContext -> folFormula -> Prop :=
  | folAx: forall (ctx: folContext) f,
      snd ctx f -> ctx |-- f
      
      
  | folForallIntro: forall ctx (F: folFormula) v,
  
      folFresh ctx v -> ctx +++ (folIndSymbol v) |-- F -> ctx |-- folForall v F
      
  | folForallElim: forall ctx F v ind,
  
      ctx |-- folForall v F -> ctx |-- folSubstitute v ind F
        
  | implIntro: forall ctx f g,
      ctx,, f |-- g -> ctx |-- folImpl f g
  | implElim: forall ctx f g,
      ctx |-- folImpl f g -> ctx |-- f -> ctx |-- g

  where "Gamma '|--' f" := (folDerivable Gamma f).


(*
Inductive folDecl :=
    | functionSymbol: string -> nat -> folDecl (* nat is arity *)
    | predicateSymbol: string -> nat -> folDecl
    | bolIndSymbol: string -> folDecl.

Definition folSignature := list folDecl.

Definition folVariable := string.
Inductive folTerm : Set :=
  | fromVar: folVariable -> folTerm
  | folIndRef: string -> folTerm
  | folFunctionApp: string -> list folTerm -> folTerm.

Inductive folFormula : Set :=
    | folForall: folVariable -> folFormula -> folFormula
    | folExists: folVariable -> folFormula -> folFormula
    | folBiimpl: folFormula -> folFormula -> folFormula
    | folImpl: folFormula -> folFormula -> folFormula
    | folDisjunction: folFormula -> folFormula -> folFormula
    | folConjunction: folFormula -> folFormula -> folFormula
    | folEq: folTerm -> folTerm -> folFormula
    | folApp: folFormula -> folTerm -> folFormula
    | folLam: (folTerm -> folFormula) -> folFormula
    | folPredicateRef: string -> folFormula.*)

Require Import Coq.Lists.List.

Definition ctxFromSystem {declType folType: Type} (system: (list declType) * (list folType)): context declType folType := match system with
| (sig, thy) => (fun _ => False, fun _ => False)
end.

Notation "'^' sys" := (ctxFromSystem sys) (at level 50).
Notation "'[[' ontology ']]'" := (folSemantics ontology) (at level 45).


Definition contextSemantics {declType formType: Type} (declSemantics: bolDecl -> declType) (formSemantics: bolFormula -> formType) : bolContext -> context declType formType := fun ctx => (
  (* exists preimages under semantics *)
  fun d => exists d', fst ctx d' /\ declSemantics d' = d,
  fun f => exists f', snd ctx f' /\ formSemantics f' = f
).

Definition folContextSemantics := @contextSemantics folDecl folFormula FOLSemantics.declSemantics FOLSemantics.formulaSemantics.

Definition contextConcat {declType formType: Type} (ctx1 ctx2: context declType formType): context declType formType := (
  fun d => (fst ctx1 d) \/ (fst ctx2 d),
  fun f => (snd ctx1 f) \/ (snd ctx2 f)
).

Notation "ctx1 ':::' ctx2" := (contextConcat ctx1 ctx2) (at level 60).

Lemma emptyCtxAtBeginning: forall {declType folType: Type} system f, ~(snd (@ctxFromSystem declType folType system) f).
Proof.
  intros.
  rewrite /ctxFromSystem.
  case: system.
  intros.
  by simpl.
Qed.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma concatWithInitialContext: forall (ontology: bolOntology) ctx f, (^ ontology ::: ctx).2 f -> ctx.2 f.
Proof.
  move => ontology ctx f H.
  assert (~(^ontology).2 f). apply: emptyCtxAtBeginning.
  case: H => //.
Qed.

Lemma l: forall (ontology: bolOntology) ctx i (R: bolID) j, ctx |- i <.R.> j <-> ctx.2 (i <.R.> j) \/ ctx.2 (j <.inv R.> i).
Proof.
  move => ontology ctx i R j.
  split.
  - move => der.
    dependent induction der => //.
    * admit.
    * admit.
    * admit.
    * admit.
    * right.

Theorem correctnessHelper: forall (ontology: bolOntology) ctx f,
  ^ontology ::: ctx |- f -> ^[[ontology]] ::: folContextSemantics ctx |-- FOLSemantics.formulaSemantics f.
  move => ontology ctx f derivation.
  dependent induction derivation => //.
  - apply: folAx.
    simpl.
    apply: or_intror.
    exists f.
    split => //.
    by apply: concatWithInitialContext; exact H.
  - admit.
  - simpl.
    apply: folForallIntro.
    * admit.
    * apply: implIntro.
      apply: implElim.
      Locate "~=".
      Print JMeq.
      admit.
    admit.
  - simpl in IHderivation1.
    simpl in IHderivation2.
    assert (^ [[ontology]] ::: folContextSemantics ctx
|-- folSubstitute "x" (FOLSemantics.bolIndSemantics ind) (folImpl (folApp (FOLSemantics.bolConSemantics c) "x") (folApp (FOLSemantics.bolConSemantics d) "x"))). {
      by apply: folForallElim; apply: IHderivation1.
    }
    simpl.
    simpl in H.
    Admitted.

(* probably true *)
Theorem correctness: forall (ontology: bolOntology) f,
  ^ontology |- f -> ^[[ontology]] |-- FOLSemantics.formulaSemantics f.
  move => ontology f.
Admitted.

(* probably not true *)
Theorem completeness: forall (ontology: bolOntology) f,
  ^[[ontology]] |-- FOLSemantics.formulaSemantics f -> ^ontology |- f.
Admitted.