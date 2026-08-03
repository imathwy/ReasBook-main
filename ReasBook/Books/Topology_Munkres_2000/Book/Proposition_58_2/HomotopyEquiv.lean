module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Mathlib.Topology.Homotopy.Equiv

public section

universe u

namespace Set.DeformationRetraction

open scoped ContinuousMap

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- Helper for Proposition 58.2: composing a retraction with the subtype inclusion is the
identity map on the retract. -/
private lemma retractionCompInclusion_eq_id (r : Set.Retraction A) :
    r.toContinuousMap.comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) = ContinuousMap.id A := by
  -- Compare the maps pointwise using the left-inverse law in the subtype.
  ext a
  exact congrArg Subtype.val (r.leftInverse a)

/-- Helper for Proposition 58.2: a retraction followed by the subtype inclusion is homotopic to
the identity on the retract. -/
private lemma retractionCompInclusionHomotopicId (r : Set.Retraction A) :
    (r.toContinuousMap.comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).Homotopic
        (ContinuousMap.id A) := by
  -- Replace the composite by the strict identity equation.
  rw [retractionCompInclusion_eq_id r]

/-- Helper for Proposition 58.2: the ambient endpoint map of a deformation retraction is
homotopic to the identity. -/
private lemma ambientRetractionHomotopicId (H : Set.DeformationRetraction A) :
    H.toRetraction.toAmbient.Homotopic (ContinuousMap.id X) := by
  -- Reverse the defining homotopy and forget its relative condition.
  exact ⟨H.toHomotopyRel.symm.toHomotopy⟩

/-- A deformation retraction determines a homotopy equivalence from the retract to the ambient
space. -/
def toHomotopyEquiv (H : Set.DeformationRetraction A) : A ≃ₕ X where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := H.toRetraction.toContinuousMap
  left_inv := retractionCompInclusionHomotopicId H.toRetraction
  right_inv := ambientRetractionHomotopicId H

/-- The forward map of the homotopy equivalence induced by a deformation retraction is the
subtype inclusion. -/
theorem toHomotopyEquiv_apply (H : Set.DeformationRetraction A) (a : A) :
    H.toHomotopyEquiv a = a := by
  -- The forward continuous map is definitionally the subtype inclusion.
  rfl

/-- The inverse map of the homotopy equivalence induced by a deformation retraction is its stored
retraction. -/
theorem toHomotopyEquiv_symm_apply (H : Set.DeformationRetraction A) (x : X) :
    H.toHomotopyEquiv.symm x = H.toRetraction.apply x := by
  -- The inverse continuous map is definitionally the stored retraction.
  rfl

end Set.DeformationRetraction

namespace Set.IsDeformationRetract

open scoped ContinuousMap

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A deformation retract admits a homotopy equivalence from the retract to the ambient space. -/
theorem nonempty_homotopyEquiv (hA : Set.IsDeformationRetract A) :
    Nonempty (A ≃ₕ X) := by
  rw [Set.isDeformationRetract_iff] at hA
  obtain ⟨r, ⟨H⟩⟩ := hA
  exact ⟨Set.DeformationRetraction.toHomotopyEquiv ⟨r, H⟩⟩

end Set.IsDeformationRetract
