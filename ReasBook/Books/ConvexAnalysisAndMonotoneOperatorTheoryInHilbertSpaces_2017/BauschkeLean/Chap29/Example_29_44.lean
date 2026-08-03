import BauschkeLean.Chap29.Example_29_43

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (C : Set H)
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/- Source/core/bridge triage:
- `source-facing`: Example 29.44 is the `p = 1` instance of the distance-power
  subgradient-projector formula, so its content is that the resulting projector is the metric
  projection onto `C`.
- `core/canonical`: the owner abstraction is the Chapter 29 operator
  `distancePowerSubgradientProjector`.
- `bridge/view`: this file is only the `p = 1` specialization of the source-facing owner theorem
  `distancePowerSubgradientProjector_eq_affine_projection` from Example 29.43.

Primitive data: the closed convex set `C` together with its standard nonempty/closed/convex
hypotheses.
Derived API: the pointwise evaluation formula, which is omitted here because it is a direct
specialization of Example 29.43's canonical apply theorem. -/
local notation "P_C" =>
  P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex]

/-- Example 29.44: if `C` is a nonempty closed convex subset of a real Hilbert space, then the
subgradient projector onto `C` associated with `(d_C, 0)` is the metric projection `P_C`. -/
theorem distanceSubgradientProjector_eq_metricProjection :
    distancePowerSubgradientProjector C 1 hC_nonempty hC_closed hC_convex =
      P_C := by
  simpa using
    distancePowerSubgradientProjector_eq_affine_projection
      C 1 hC_nonempty hC_closed hC_convex (by norm_num)

end
