module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

namespace Circle

/-- Exercise 53.5. For every nonzero natural number `n`, the map `z ↦ z ^ n` on the complex
unit circle is a covering map in Munkres's surjective sense. -/
theorem isCoveringMap_npow_surjective (n : ℕ) [NeZero n] :
    IsCoveringMap (· ^ n : Circle → Circle) ∧ Function.Surjective (· ^ n : Circle → Circle) :=
  ⟨(isQuotientCoveringMap_npow n).isCoveringMap,
    (isQuotientCoveringMap_npow n).surjective⟩

/- The squaring map from Example 53.3 is the case `n = 2`. -/
#check isCoveringMap_npow_surjective 2

end Circle
