import ConvexAnalysis_Rockafellar_1970.Chap07.Lemma33_0_21

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.14 identifies convex bifunctions with convex graph functions on the
  product space.
- `core/canonical`: the owner layer is already the intrinsic function-space bridge
  `Function.isConvexUncurryEquiv`, built from the canonical bifunction owner notation
  `convᵇ[𝕜](F)` (definitionally `(Function.uncurry F).IsConvex 𝕜`) together with the canonical
  `Function.curry`/`Function.uncurry` operators.
- `bridge/view`: this file is recall-only; it reuses the existing chapter bridge rather than
  introducing a second owner file with the same interface.

Domain-style sampling used here:
- the direct graph-convexity owner recalled in `Definition33_0_28`;
- `Function.isConvexUncurryEquiv` from `Lemma33_0_21`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithTopBot α` and its uncurried graph function
  `f : U × X → WithTopBot α`;
- owner abstraction: `convᵇ[𝕜](F)`;
- derived API: the resulting subtype equivalence.

Layer target: `bridge/view`.
-/

/- Lemma33.0.14 is already owned by `Chap07/Lemma33_0_21.lean`. This file is bridge-only and
reuses the canonical owner directly instead of re-declaring a parallel API. -/
#check Function.isConvexUncurryEquiv
