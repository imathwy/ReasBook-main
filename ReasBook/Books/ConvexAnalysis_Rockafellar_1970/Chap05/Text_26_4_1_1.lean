import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_26_4_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_1

noncomputable section

open AffineMap Filter
open scoped Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.4.1.1 explains how, for an essentially smooth closed proper convex
  function `f`, the Fenchel conjugate `f⋆` is the closed proper convex extension of its
  Legendre-side restriction to the canonical set `D = dom∂((f⋆ : E → EReal))`.
- `core/canonical`: the owner declarations already present upstream are Fenchel conjugation `f⋆`,
  the canonical Legendre-side set owner `dom∂(·)`, the conjugate-side sandwich theorem
  `Function.IsClosedProperConvex
    .convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between`,
  the relative-domain notation `riDom(·)`, and the segment-limit theorem
  `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull`.
- `bridge/view`: the source wording about the Legendre conjugate `g` on `D` is interpreted as the
  restriction of `f⋆` to `D`; the nontrivial extension content is therefore the boundary-limit
  behavior and the `+∞` value outside `closure D`, rather than a new wrapper around that
  restriction.

Domain-style sampling used here:
- `Function.IsClosedProperConvex
    .convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between`;
- `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull` from Theorem 7.5;
- `dom(·)` and `riDom(·)` from Definition 4.4;
- `closure` and `frontier` on the canonical set owner `D`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f`, its conjugate `f⋆`, and the
  canonical Legendre-side set `D = dom∂((f⋆ : E → EReal))`;
- derived API: the exterior formula `f⋆ = +∞` off `closure D`, together with the segment-limit
  formula from points of `ri(dom f⋆)` to arbitrary endpoints; the source frontier hypothesis is a
  redundant specialization of that second statement.

Layer target: `bridge/view`. The item does not introduce a new Legendre-transform owner; it
records the extension behavior of the already canonical conjugate owner `f⋆`.
-/

namespace Function.IsClosedProperConvex

variable {f : E → EReal}

local notation "fStar" => (f⋆ : E → EReal)
local notation "D" => dom∂(fStar)

-- Proof sketch: build the canonical owner `hf : f.IsClosedProperConvex` from `hclosed` and the
-- convexity/properness fields already carried by `hess`. Then `hf.convexConjugate` makes `fStar`
-- closed proper convex. Corollary 26.4.1 gives the exact conjugate-side sandwich
-- `riDom(fStar) ⊆ D ⊆ dom(fStar)` under these hypotheses, so
-- `closure D = closure (dom(fStar))` by convexity of `dom(fStar)`. Use the standard closed
-- proper convex exterior formula for points outside that closure.
/-- Text 26.4.1.1, exterior clause: for an essentially smooth closed proper convex function `f`,
let `D = dom∂(fStar)` for `fStar = f⋆`. Then the conjugate takes the value `+∞` at every point
outside `closure D`. -/
theorem convexConjugate_eq_top_outside_closure_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) {xStar : E}
    (hxStar : xStar ∉ closure D) :
    fStar xStar = ⊤ := sorry

-- Proof sketch: with `hf : f.IsClosedProperConvex` as above, the canonical conjugate owner
-- `hf.convexConjugate` makes `fStar` closed proper convex. Apply Theorem 7.5 to `fStar`, using
-- the base point `uStar ∈ riDom(fStar)` and the arbitrary endpoint `xStar`. Since `fStar` is
-- closed, `cl(fStar) = fStar`, so the segment values converge to the actual conjugate value at
-- `xStar`; the source frontier condition is therefore redundant in the Lean API.
/-- Text 26.4.1.1, boundary clause: for `fStar = f⋆` and `D = dom∂(fStar)`, if
`uStar ∈ riDom(fStar)`, then the values of `fStar` along the segment
`t ↦ lineMap uStar xStar t` converge to `fStar xStar` as `t → 1` from the left. The source
specialization `xStar ∈ frontier D` is redundant for this conclusion. -/
theorem tendsto_convexConjugate_lineMap_to_frontier_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) {uStar xStar : E}
    (huStar : uStar ∈ riDom(fStar)) :
    Tendsto (fun t : ℝ ↦ fStar (lineMap uStar xStar t))
      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
      (nhds (fStar xStar)) := sorry

end Function.IsClosedProperConvex

end
