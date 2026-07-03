import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0020_Definition_II_1_extra_11»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set
open scoped Interval

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Proof sketch: cover the compact rectangle by finitely many open patches on which `δ` lands in a
-- neighborhood admitting a primitive of `ω`, glue the resulting local pullback primitives first
-- along one coordinate direction and then along the other, and compare two global primitives by
-- showing their difference is locally constant and hence constant on the connected rectangle.
/-- Lemma II.1-extra-12: if every point of the closed rectangle has a neighborhood on which `δ`
lands in a domain where `ω` admits a primitive, then there exists a primitive of `ω` following `δ`
on the whole rectangle, and it is unique up to addition of a constant on that rectangle. -/
theorem primitive_following_on_rectangle_exists_and_unique_up_to_constant
    {ω : E → E →L[ℝ] F} {D : Set E} {a a' b b' : ℝ}
    {δ : C([[(a, a'), (b, b')]], E)}
    (hlocal : ∀ p : [[(a, a'), (b, b')]], HasPrimitiveWithinAt D ω (δ p)) :
    ∃ f : C([[(a, a'), (b, b')]], F),
      IsPrimitiveFollowingOnRectangle ω D δ f ∧
        ∀ g : C([[(a, a'), (b, b')]], F), IsPrimitiveFollowingOnRectangle ω D δ g →
          ∃ c : F, g = f + ContinuousMap.const _ c := by
  sorry
