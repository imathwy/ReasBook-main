import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.9 identifies the adjoint bifunction of a convex bifunction with
  the negative Fenchel conjugate of its graph function, evaluated at the sign-twisted dual pair
  `(-u⋆, x⋆)`.
- `core/canonical`: the graph function is already owned by `Function.uncurry`, the conjugate is
  already owned by `convexConjugate` with notation `(·)⋆`, and the adjoint bifunction is already
  owned by `Bifunction.adjoint`.
- `bridge/view`: the theorem is exactly the immediate pointwise companion theorem
  `Bifunction.adjoint_apply` from `Definition_6_30_14`; no second wrapper theorem is
  mathematically needed here.

Domain-style sampling used here:
- `Function.uncurry` from `Definition_6_29_2`;
- `convexConjugate` and postfix notation `(·)⋆` from `Chap03.Defn_12_2`;
- `Bifunction.adjoint` and `Bifunction.adjoint_apply` from
  `Definition_6_30_14`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: `Bifunction.adjoint F`;
- derived API: the pointwise evaluation formula identifying this owner with the negative conjugate
  of the graph function.

Layer target: `core/canonical recall/use`. The source convexity and Euclidean-space assumptions are
redundant for this identity itself, so the faithful Lean formalization reuses the existing
pairing-level theorem directly.
-/

/- Theorem 6.30.9: for the adjoint bifunction `F*` of a bifunction `F`, the value at `(x⋆, u⋆)`
is the negative Fenchel conjugate of the graph function `Function.uncurry F`, evaluated at
`(-u⋆, x⋆)`. This numbered item is exactly the existing pointwise owner theorem
`Bifunction.adjoint_apply`, so the faithful refinement is a direct recall. -/
recall Bifunction.adjoint_apply
