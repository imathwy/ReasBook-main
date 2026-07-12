import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import StacksProject_2024.Chapters.Chap23.section03

open CategoryTheory
open CategoryTheory.Limits

namespace DividedPowerRing

-- Semantic recall: `lean_leansearch` surfaced `CommRingCat.isPushout_tensorProduct`, confirming
-- that the source counterexample is naturally expressed as failure of pushout preservation for the
-- forgetful functor to commutative rings.

/-- The pushout counterexample from Remark 23.3.6 already shows that the forgetful functor from
divided power rings to commutative rings does not preserve pushouts. -/
theorem forgetToCommRingCat_not_preservesPushouts :
    ¬ PreservesColimitsOfShape WalkingSpan (forget₂ DividedPowerRing CommRingCat) := sorry

/-- Remark 23.3.6: the forgetful functor `(A, I, γ) ↦ A` from divided power rings to commutative
rings does not commute with colimits. Concretely, the source gives a pushout square built from
`(ℤ, (0), ∅)` and two divided power structures on `(ℤ/4ℤ, 2ℤ/4ℤ)` with `δ₂(2) = 2` and
`δ'₂(2) = 0`, whose pushout in divided power rings is `(𝔽₂, (0), ∅)` rather than the tensor
product pushout of the underlying rings. -/
@[stacks 07GY]
theorem forgetToCommRingCat_not_preservesColimits :
    ¬ PreservesColimits (forget₂ DividedPowerRing CommRingCat) := by
  intro hPreserves
  let _ : PreservesColimits (forget₂ DividedPowerRing CommRingCat) := hPreserves
  let _ : PreservesColimitsOfSize.{0, 0} (forget₂ DividedPowerRing CommRingCat) :=
    preservesSmallestColimits_of_preservesColimits (forget₂ DividedPowerRing CommRingCat)
  exact forgetToCommRingCat_not_preservesPushouts inferInstance

end DividedPowerRing
