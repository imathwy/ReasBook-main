import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap25.Example_25_13

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction
open SetValuedOperator

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Set H}

/-- Helper for Example 25.14: the indicator `ι[C]` is proper as soon as `C` is nonempty. -/
private theorem setIndicator_isProper {X : Type u} {C : Set X} (hC_nonempty : C.Nonempty) :
    ERealFunction.IsProper (ι[C] : X → EReal) := by
  refine ⟨fun x ↦ ne_of_gt (ι[C] x).property, ?_⟩
  rcases hC_nonempty with ⟨x, hx⟩
  exact ⟨x, by simp [ERealFunction.indicator_apply, hx]⟩

/- Source/core/bridge triage:
- `source-facing`: Example 25.14 is the chapter statement about the normal cone `N[C]`; the source
  phrases it for closed convex sets, but those hypotheses are redundant for `3*` monotonicity.
- `core/canonical`: the owner abstraction is `SetValuedOperator.IsThreeStarMonotone`, with the
  normal cone reached through the canonical bridge `∂ ι[C] = N[C]`.
- `bridge/view`: for nonempty `C`, the indicator `ι[C]` is proper, so Example 25.13 gives
  `(∂ ι[C]).IsThreeStarMonotone`; the empty-set case is vacuous because `N[∅]` has empty domain. -/

/-- Example 25.14: the normal cone operator `N[C]` is `3*` monotone. For nonempty `C`, this is
the subdifferential example applied to the proper indicator `ι[C]`; for `C = ∅`, the claim is
vacuous, so no closedness or convexity hypothesis is needed here. -/
theorem normalCone_isThreeStarMonotone :
    SetValuedOperator.IsThreeStarMonotone (N[C] : SetValuedOperator H H) := by
  by_cases hC_nonempty : C.Nonempty
  · rw [← subdifferential_setIndicator_eq_normalCone C hC_nonempty]
    exact subdifferential_isThreeStarMonotone (setIndicator_isProper hC_nonempty)
  · rw [SetValuedOperator.isThreeStarMonotone_iff]
    rw [Set.not_nonempty_iff_eq_empty] at hC_nonempty
    simp [SetValuedOperator.dom, Set.normalCone, hC_nonempty]

end

end Set
