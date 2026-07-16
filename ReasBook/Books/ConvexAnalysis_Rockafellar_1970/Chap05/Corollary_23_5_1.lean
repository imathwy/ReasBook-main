import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function.IsClosedProperConvex

variable {f : E → EReal} {x xStar : E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.1 states that, for a closed proper convex function, the
  subdifferential of the Fenchel conjugate is the inverse set-valued mapping of the
  subdifferential of the original function.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.subdifferentialAt`, the Fenchel conjugate notation `f⋆`, and the bundled hypothesis
  `f.IsClosedProperConvex`.
- `bridge/view`: this corollary is a one-step specialization of Theorem 23.5 from the
  closure-normalized equivalence to the closed case, using the canonical
  closed/proper/convex owner instead of carrying a separate hypothesis `cl(f) x = f x`.

Domain-style sampling used here:
- `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `Function.IsClosedProperConvex` from `Chap03/Text_12_3_6`;
- `lowerSemicontinuousHull_eq_self` on lower-semicontinuous functions;
- `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_
  conjugate_subdifferentialAt_of_closure_eq` from `Chap05/Theorem_23_5`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the primal point `x`, the dual point `xStar`, and the owner
  hypothesis `hf : f.IsClosedProperConvex`;
- derived surface: the inverse-graph equivalence
  `x ∈ subdifferentialAt (f⋆) xStar ↔ xStar ∈ subdifferentialAt f x`.

Layer target: `source-facing`, stated directly on the canonical Chapter 23 owners
`Function.subdifferentialAt` and `Function.IsClosedProperConvex`, with no surrogate
inverse-relation package.
-/

-- Proof sketch: Theorem 23.5 already places the two membership clauses
-- `xStar ∈ subdifferentialAt f x` and `x ∈ subdifferentialAt (f⋆) xStar` in the same TFAE class
-- once the closure normalization `cl(f) x = f x` is available. For a closed proper convex
-- function, lower semicontinuity identifies `cl(f) = f`, so that normalization is automatic, and
-- the two clauses become equivalent.
/-- Corollary 23.5.1: if `f` is closed proper convex, then the subdifferential of the Fenchel
conjugate is the inverse of the subdifferential of `f` as a set-valued mapping; equivalently,
`x ∈ ∂f⋆(xStar)` if and only if `xStar ∈ ∂f(x)`. -/
theorem mem_subdifferentialAt_convexConjugate_iff
    (hf : f.IsClosedProperConvex) :
    x ∈ subdifferentialAt (f⋆) xStar ↔ xStar ∈ subdifferentialAt f x := by
  have hclx : cl(f) x = f x := by
    simpa using congrFun (lowerSemicontinuousHull_eq_self hf.closed) x
  exact
    (subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq
      hf.convex hf.proper hclx).out 4 0

end Function.IsClosedProperConvex

end
