import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.3 studies an extended-valued function `φ` on an ordered scalar
  line, squeezed pointwise between the source one-sided derivatives `f′-` and `f′+` of a proper
  convex function `f`, then identifies the source one-sided limit functions `φ_-` and `φ_+`,
  including the scalar-line subdifferential interval corollary.
- `core/canonical`: the relevant owner declarations already exist as the one-sided limit owners
  `Function.leftLim`, `Function.rightLim` and the Chapter 24 one-sided derivative owners
  `Function.leftDerivative`, `Function.rightDerivative`; the subgradient consequence is routed
  through the canonical interval theorem
  `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative`, not
  through a new
  selector package.
- `bridge/view`: this item is a theorem-level bridge from the order bounds
  `f′- x ≤ φ x ≤ f′+ x` to monotonicity and one-sided-limit identification.

Domain-style sampling used here:
- `Function.leftLim` and `Function.rightLim` from mathlib's canonical one-sided-limit API in
  `Topology/Order/LeftRightLim`;
- `Monotone.tendsto_leftLim` and `Monotone.tendsto_rightLim` from the same file, which are the
  canonical generic one-sided-limit theorems for a monotone profile;
- `Function.leftDerivative` and `Function.rightDerivative` from
  `Items/Chap05/Theorem_5_24_1.lean`;
- `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative` from
  `Items/Chap05/Theorem_5_24_2.lean`.

Primitive data vs derived API:
- primitive theorem inputs: `f`, `φ`, the pointwise sandwich assumption
  `f′- x ≤ φ x ≤ f′+ x`, and the minimal convexity data needed by each
  clause (`f.IsConvex 𝕜` for monotonicity, and `f.IsConvex 𝕜` + `f.IsProper` for one-sided-limit
  identification on `interior (dom(f))`; the subdifferential interval clause uses the scalar-line
  pairing owner `∂[𝕜]f(x)` with `⟪u, v⟫ₚ = u * v`);
- derived conclusions: monotonicity of `φ`, identification of its one-sided limits, and the
  resulting interval description of the one-dimensional subdifferential.

Layer target: `bridge/view`.

Scalar/ambient minimization note:
- clauses (1)–(3) use the ordered scalar-line layer already exposed by the upstream one-sided
  derivative owners `leftDerivative` and `rightDerivative`;
- clause (4) now uses the same scalar-line abstraction layer as clauses (1)–(3), via the upstream
  interval-fiber theorem
  `Function.subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative` and the scalar-line
  subdifferential owner `∂[𝕜]f(x)`;
- clauses (2)–(4) do not use the stronger bundled owner `IsClosedProperConvex`; they expose only
  the upstream primitive assumptions actually used (`IsConvex _`, `IsProper`, and local point
  data).
-/

namespace Function

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

variable {f : 𝕜 → WithBotTop 𝕜}
variable {φ : 𝕜 → WithBotTop 𝕜}

-- Proof sketch: for `x < y`, use the one-dimensional convex secant-slope order
-- `f′+ x ≤ f′- y`. Insert the bounds `φ x ≤ f′+ x` and `f′- y ≤ φ y` to obtain `φ x ≤ φ y`.
/-- Theorem 5.24.3 (1): any extended-valued function on an ordered scalar line lying pointwise
between the left and right derivatives of a convex function is nondecreasing. -/
theorem monotone_of_leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    : Monotone φ := by
  sorry

section Topological

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

-- Proof sketch: clause (1) gives monotonicity of `φ`, so the canonical one-sided-limit owner
-- theorem `Monotone.tendsto_rightLim` identifies the right-hand asymptotic profile of `φ`.
-- Squeezing `φ z` between `f′- z` and `f′+ z` for `z > x`, and then
-- using the right-hand one-sided continuity of the derivative bounds, forces that limit to be
-- `f′+ x`.
/-- Theorem 5.24.3 (2), pointwise interior-domain form: the right one-sided limit of `φ` agrees with
the source right derivative. -/
theorem rightLim_eq_rightDerivative_of_leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    {x : 𝕜} (hx : x ∈ interior (dom(f)))
    : φ.rightLim x = f′+ x := by
  sorry

-- Proof sketch: clause (1) gives monotonicity of `φ`, so `Monotone.tendsto_leftLim` supplies the
-- canonical left-hand limit of `φ`. Squeezing `φ z` between `f′- z` and `f′+ z` for `z < x`, and
-- using the left-hand one-sided continuity of the derivative bounds, identifies that limit with
-- `f′- x`.
/-- Theorem 5.24.3 (3), pointwise interior-domain form: the left one-sided limit of `φ` agrees with
the source left derivative. -/
theorem leftLim_eq_leftDerivative_of_leftDerivative_le_rightDerivative
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    {x : 𝕜} (hx : x ∈ interior (dom(f)))
    : φ.leftLim x = f′- x := by
  sorry

end Topological

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]

variable {f : 𝕜 → WithBotTop 𝕜}
variable {φ : 𝕜 → WithBotTop 𝕜}

/-- The canonical one-dimensional pairing on a scalar line is ordinary multiplication. -/
local instance instHasPairingScalarLine_5243 : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

-- Proof sketch: start from the one-dimensional interval description by left/right derivatives
-- (Theorem 5.24.2), then rewrite both interval endpoints by identified one-sided limits.
/-- Primitive clause-(4) bridge: if the one-sided limits of `φ` are already identified with the
source one-sided derivatives at `x`, then the subdifferential is the interval between those limits.
-/
theorem subdifferentialAt_eq_setOf_mem_Icc_of_leftLim_eq_and_rightLim_eq
    (hf_convex : f.IsConvex 𝕜)
    {x : 𝕜} (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hleft : φ.leftLim x = f′- x)
    (hright : φ.rightLim x = f′+ x) :
    (∂[𝕜]f(x)) =
      {xStar : 𝕜 | (xStar : WithBotTop 𝕜) ∈ Set.Icc (φ.leftLim x) (φ.rightLim x)} := by
  simpa [hleft, hright] using
    (subdifferentialAt_eq_setOf_mem_Icc_leftDerivative_rightDerivative hf_convex x hx hx_bot)

variable [OrderTopology 𝕜] [OrderTopology (WithBotTop 𝕜)]

/-- Theorem 5.24.3 (4), source-facing corollary: on `interior (dom(f))`, the subdifferential is
the interval of scalar slopes between the one-sided limits `φ_-` and `φ_+`. -/
theorem subdifferentialAt_eq_setOf_mem_Icc_leftLim_rightLim
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hφ : ∀ x : 𝕜, φ x ∈ Set.Icc (f′- x) (f′+ x))
    {x : 𝕜} (hx_int : x ∈ interior (dom(f))) (hx_bot : f x ≠ ⊥) :
    (∂[𝕜]f(x)) =
      {xStar : 𝕜 | (xStar : WithBotTop 𝕜) ∈ Set.Icc (φ.leftLim x) (φ.rightLim x)} := by
  have hx : x ∈ dom(f) := interior_subset hx_int
  have hright :
      φ.rightLim x = f′+ x :=
    rightLim_eq_rightDerivative_of_leftDerivative_le_rightDerivative hf_convex hf_proper hφ hx_int
  have hleft :
      φ.leftLim x = f′- x :=
    leftLim_eq_leftDerivative_of_leftDerivative_le_rightDerivative hf_convex hf_proper hφ hx_int
  exact subdifferentialAt_eq_setOf_mem_Icc_of_leftLim_eq_and_rightLim_eq
    hf_convex hx hx_bot hleft hright

end

end Function
