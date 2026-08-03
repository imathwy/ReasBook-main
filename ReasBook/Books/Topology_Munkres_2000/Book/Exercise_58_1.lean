module

public import Topology_Munkres_2000.Book.Exercise_58_1.Composition

public section

universe u

namespace Set

variable {X : Type u} [TopologicalSpace X] {A B : Set X}

/-- Exercise 58.1: A deformation retract of a deformation retract is a deformation retract
of the original space. -/
theorem IsDeformationRetract.trans (hA : IsDeformationRetract A) (hBA : B ⊆ A)
    (hB : IsDeformationRetract (Subtype.val ⁻¹' B : Set A)) :
    IsDeformationRetract B := by
  -- Use the public existence characterization to expose the concrete data.
  rw [isDeformationRetract_iff] at hA hB ⊢
  obtain ⟨r_A, ⟨F_A⟩⟩ := hA
  obtain ⟨r_B, ⟨F_B⟩⟩ := hB
  let H_A : DeformationRetraction A := ⟨r_A, F_A⟩
  let H_B : DeformationRetraction (Subtype.val ⁻¹' B : Set A) := ⟨r_B, F_B⟩
  -- Compose the two deformation retractions and return its public components.
  let H := H_A.trans hBA H_B
  exact ⟨H.toRetraction, ⟨H.toHomotopyRel⟩⟩

end Set
