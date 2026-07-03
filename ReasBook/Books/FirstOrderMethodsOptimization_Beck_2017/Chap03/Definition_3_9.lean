import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.9 is `source-facing` at the Chapter 3 owners `directional_derivative` and
`subdifferential`: the public statement is the textbook maximum formula for the directional
derivative. The Chapter 2 support-function owner is only a downstream bridge reformulation, so it
is not re-exported from this source-facing file. -/
recall directional_derivative
recall subdifferential

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: combine the convex subgradient inequality with the interior-point nonemptiness and
-- compactness properties of the finite-dimensional subdifferential to show that the pairing map
-- `g ↦ g d` attains its maximum on `subdifferential f x`, and that this maximum equals the
-- directional derivative. The interior-point hypothesis already forces `effective_domain f` to be
-- nonempty, so the only extra properness ingredient needed here is that `f` never takes the value
-- `⊥`.
/-- Definition 3.9: for a convex extended-real-valued function that never takes the value `⊥`, the
directional derivative at an interior point of the effective domain is the maximum of the
subgradient pairings `g d` over all `g ∈ ∂ f(x)`. -/
theorem directional_derivative_isGreatest_subgradient_pairings_at_interior_point
    {f : E → EReal} {x d : E} (h_ne_bot : ∀ y, f y ≠ ⊥) (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    IsGreatest ((fun g : Module.Dual ℝ E ↦ (g d : EReal)) '' subdifferential f x)
      (directional_derivative f x d) := sorry

end
