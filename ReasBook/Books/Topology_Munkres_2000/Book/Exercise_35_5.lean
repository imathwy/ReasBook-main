module

public import Topology_Munkres_2000.Book.Exercise_35_5.Retract
public import Topology_Munkres_2000.Book.Definition_35_1.Retraction

public section

universe u v w

/- Exercise 35.5 (1). For every index type `J`, the product `J → ℝ` has the
universal extension property. -/
#check fun (J : Type u) ↦ (inferInstance : UniversalExtensionProperty.{w} (J → ℝ))

namespace UniversalExtensionProperty

/-- Exercise 35.5 (2). A space homeomorphic to a retract of `J → ℝ` has the
universal extension property. -/
theorem ofHomeoRetractPi {J : Type u} {Y : Type v} [TopologicalSpace Y]
    {A : Set (J → ℝ)} (hA : Set.IsRetract A) (e : Y ≃ₜ A) :
    UniversalExtensionProperty.{w} Y := by
  obtain ⟨r, hr⟩ := (Set.isRetract_iff A).1 hA
  apply ofRetract ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, J → ℝ)).comp e)
    ((e.symm : C(A, Y)).comp r)
  ext y
  change e.symm (r (e y : J → ℝ)) = y
  rw [hr (e y)]
  simp

end UniversalExtensionProperty
