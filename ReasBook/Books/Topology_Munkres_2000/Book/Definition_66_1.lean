module

public import Topology_Munkres_2000.Book.Definition_66_1.WindingNumber

public section

namespace PlaneLoop

/-- Definition 66.1: Every real lift of the normalized loop through the standard covering has
endpoint displacement equal to the winding number. -/
theorem windingNumber_spec {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (Γ : C(unitInterval, ℝ))
    (hΓ : ∀ t, standardCircleCovering (Γ t) = normalizedLoop f a h_avoid t) :
    Γ 1 - Γ 0 = (windingNumber f a h_avoid : ℝ) := by
  -- Transport the lift to `UnitAddCircle` and use the additive-circle specification.
  apply windingNumber_spec_angularLoop f a h_avoid Γ
  intro t
  apply (AddCircle.homeomorphCircle one_ne_zero).injective
  rw [← standardCircleCovering_apply, homeomorphCircle_angularLoop_apply]
  exact hΓ t

end PlaneLoop

#check PlaneLoop.normalizedLoop
#check PlaneLoop.standardCircleCovering
#check PlaneLoop.angularLift
#check PlaneLoop.windingNumber
#check PlaneLoop.windingNumber_spec
