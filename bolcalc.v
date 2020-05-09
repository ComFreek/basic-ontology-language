(* BOL Derivation Calculus *)

Require Import bol.

Reserved Notation "Gamma '|-' f" (at level 65).

Definition bolContext := bolFormula -> Prop.
Definition ctxCons ctx f: bolContext := fun g => (ctx f) \/ f = g.

Notation "ctx ',' f" := (ctxCons ctx f) (at level 64).

Inductive bolDerivable : bolContext -> bolFormula -> Prop :=
  | var: forall (ctx: bolContext) f, ctx f -> ctx |- f
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
  | relCompElim: forall ctx i j k R1 R2 f,    (* TODO j needs to be fresh! *)
         ctx |- i <.R1;R2.> k
      -> ctx, i <.R1.> j, j <.R2.> k |- f
      -> ctx |- f

  | relDomIntro: forall ctx i j R,
      ctx |- i <.R.> j -> ctx |- i IS-A (dom R)
  | relDomElim: forall ctx (i j: bolInd) R f, (* TODO j needs to be fresh! *)
      ctx |- i IS-A (dom R) -> ctx, (i <.R.> j) |- f -> ctx |- f

  | relCodIntro: forall ctx i j R,
      ctx |- i <.R.> j -> ctx |- j IS-A (cod R)
  | relCodElim: forall ctx (i j: bolInd) R f, (* TODO i needs to be fresh! *)
      ctx |- j IS-A (dom R) -> ctx, (i <.R.> j) |- f -> ctx |- f

  | relForallElim: forall ctx c R i j,
         ctx |- i IS-A (c forall R)
      -> ctx |- i <.R.> j
      -> ctx |- j IS-A c
  | relExistsElim: forall ctx c R i j f,     (* TODO j needs to be fresh! *)
         ctx |- i IS-A (c exists R)
      -> ctx, i <.R.> j, j IS-A c |- f
      -> ctx |- f

  (* missing: forall intro, exists intro *)

  where "Gamma '|-' f" := (bolDerivable Gamma f).