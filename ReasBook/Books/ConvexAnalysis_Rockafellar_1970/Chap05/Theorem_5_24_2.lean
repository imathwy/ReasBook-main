import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_1

noncomputable section

namespace Function

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.2 identifies the one-dimensional scalar-line subdifferential
  `∂[𝕜]f(x)` with the interval of scalar slopes lying between the left and right derivatives from
  Theorem 5.24.1.
- `core/canonical`: the relevant owners already exist as `_root_.subdifferentialAt`,
  `Function.leftDerivative`, and `Function.rightDerivative`.
- `bridge/view`: the theorem is the one-dimensional comparison between the Chapter 23
  subdifferential owner and the Chapter 24 one-sided derivative owners, not a new interval-valued
  wrapper.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and
  `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` from
  `Items/Chap05/Theorem_23_2.lean`;
- `Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point` and
  `Function.directionalDerivativeAt_zero_of_finite_point` from
  `Items/Chap05/Theorem_23_1.lean`;
- `Function.leftDerivative`, `Function.rightDerivative`,
  `Function.rightDerivative_eq_directionalDerivativeAt_one`, and
  `Function.leftDerivative_eq_neg_directionalDerivativeAt_neg_one`,
  `Function.leftDerivative_eq_top_of_not_mem_dom_of_nonempty_inter_Iio`, and
  `Function.rightDerivative_eq_bot_of_not_mem_dom_of_nonempty_inter_Ioi` from
  `Items/Chap05/Theorem_5_24_1.lean`;
- the ambient closed/proper/convex owner `Function.IsClosedProperConvex` from
  `Items/Chap03/Text_12_3_6.lean`, reused through Theorem 5.24.1.

Primitive data vs derived API:
- primitive data: a convex function `f : 𝕜 → WithTopBot 𝕜`, a point `x : 𝕜`, and the finite-point
  guards `x ∈ dom(f)` and `f x ≠ ⊥`;
- primitive owners reused from upstream: `subdifferentialAt`, `leftDerivative`, `rightDerivative`;
- derived API: the interval description of the one-dimensional fiber `∂f(x)`.

Layer target: `bridge/view`.

Scalar-layer note:
- the theorem is one-dimensional but not intrinsically real; it is stated on an ordered scalar
  line `𝕜` and reuses the canonical scalar-line pairing `⟪u, v⟫ₚ = u * v` only as a thin bridge to
  the Chapter 23 subdifferential owner.
- closedness/properness are not part of the primitive bridge data here: they are only needed
  upstream for the global continuity/off-domain consequences in Theorem 5.24.1, while the local
  interval fiber description itself only uses convexity and finiteness at `x`.
-/

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]

/-- The canonical one-dimensional pairing on a scalar line is ordinary multiplication. -/
local instance instHasPairingScalarLine_5242 : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

-- Proof sketch: specialize `mem_subdifferentialAt_iff_le_directionalDerivativeAt` to `E = 𝕜`,
-- `Y = 𝕜` with scalar-line pairing `⟪u, v⟫ₚ = u * v`, where directions `1` and `-1` recover the
-- endpoint slope inequalities.
/-- Theorem 5.24.2, atomic membership form: a scalar slope belongs to the one-dimensional
subdifferential at `x` exactly when it lies between the left and right derivatives at `x`. -/
@[simp] theorem mem_subdifferentialAt_iff_mem_Icc_leftDerivative_rightDerivative
    {f : 𝕜 → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜)
    (x : 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) (xStar : 𝕜) :
    xStar ∈ (∂[𝕜]f(x)) ↔
      ((xStar : WithTopBot 𝕜) ∈ Set.Icc (f′- x) (f′+ x)) := by
  sorry

/-- Theorem 5.24.2: for a convex extended-valued function finite at `x`, the one-dimensional
scalar-line subdifferential `∂[𝕜]f(x)` is exactly the set of scalar slopes lying between the left
and right derivatives at `x`. -/
theorem subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative
    {f : 𝕜 → WithTopBot 𝕜} (hf_convex : f.IsConvex 𝕜)
    (x : 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    (∂[𝕜]f(x)) =
      {xStar : 𝕜 |
        (xStar : WithTopBot 𝕜) ∈ Set.Icc (f′- x) (f′+ x)} := by
  ext xStar
  exact
    (mem_subdifferentialAt_iff_mem_Icc_leftDerivative_rightDerivative
      hf_convex x hx hx_bot xStar)

end

end Function
