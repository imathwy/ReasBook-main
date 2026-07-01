import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.9 introduces the adjoint bifunction `F⋆` attached to a
  bifunction `F`, given by the sign-twisted conjugate formula
  `F⋆ x⋆ u⋆ = - ((Function.uncurry F)⋆ (-u⋆, x⋆))`.
- `core/canonical`: the graph function is already owned by `Function.uncurry`, conjugation is
  already owned by `convexConjugate` with notation `(·)⋆`, and the Chapter 6 owner abstraction is
  already `Bifunction.adjoint`.
- `bridge/view`: the pointwise sign-twisted formula, the source-facing notation `F⋆`, and the
  zero-slice companion API are already exposed by `Definition_6_30_14`, so no parallel local copy
  belongs here.

Domain-style sampling used here:
- `Function.uncurry` from `Definition_6_29_2`;
- `convexConjugate` and postfix notation `(·)⋆` from `Chap03.Defn_12_2`;
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.adjoint_apply` and `Bifunction.objective_adjoint_apply` from
  `Definition_6_30_14`, confirming that the pointwise and zero-slice surfaces are already owned in
  Chapter 6.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: `Bifunction.adjoint XStar UStar F`, written source-facing as `F⋆` in
  `open scoped Rockafellar`;
- derived API: the pointwise evaluation formula and zero-slice formula for this owner.

Layer target: `core/canonical recall/use`. No convexity assumption is primitive for this owner:
the source item is definition-level, so the main entry in this file should be the owner
`Bifunction.adjoint` itself rather than a parallel local formula theorem.
-/

/- Definition 6.30.9: the adjoint bifunction of `F` is the Chapter 6 owner
`Bifunction.adjoint`, used source-facing as `F⋆` in `open scoped Rockafellar`, with its
defining pointwise and zero-slice companion API already provided in `Definition_6_30_14`. -/
recall Bifunction.adjoint
