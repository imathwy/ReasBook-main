import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_11

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.10 says that the adjoint bifunction `F⋆` of a convex bifunction
  has a closed concave graph function `g(x⋆, u⋆) = (F⋆ x⋆) u⋆`, now recalled on the
  codomain-generic pairing layer.
- `core/canonical`: the graph function is already owned by `Function.uncurry`, the adjoint
  bifunction is already owned by `Bifunction.adjoint`, and the chapter already exposes the
  canonical closed-concavity theorem `Bifunction.adjointFunction_isClosedConcave`.
- `bridge/view`: the source’s explicit graph function `g(x⋆, u⋆) = (F⋆ x⋆) u⋆` is exactly
  `Function.uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)`, so no second graph-function owner
  belongs in
  this file.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Function.uncurry` as the graph-function owner;
- `Bifunction.adjointFunction_isClosedConcave` from `Theorem_6_30_11`;
- `LowerSemicontinuous` as the closedness surface.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner: `F⋆`;
- derived API: the graph-function view
  `Function.uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)` and its
  closed-concavity theorem, with chapter-facing `EReal`/`ℝ` use recovered by specialization.

Layer target: `core/canonical recall/use`.
-/

/- Theorem 6.30.10 is exactly the canonical graph-function closed-concavity theorem already owned
by `Bifunction.adjointFunction_isClosedConcave`; the source’s named graph function
`g(x⋆, u⋆) = (F⋆ x⋆) u⋆` is just `Function.uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)`. -/
recall Bifunction.adjointFunction_isClosedConcave
