module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Definition_58_3.HomotopyType

public section

universe u

open scoped ContinuousMap

namespace Set.Retraction

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- Helper for Proposition 58.2: composing a retraction with the subtype inclusion is the
identity map on the retract. -/
private lemma compInclusion_eq_id (r : Set.Retraction A) :
    r.toContinuousMap.comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) = ContinuousMap.id A := by
  -- Pointwise equality is exactly the left-inverse property of a retraction.
  ext a
  exact congrArg Subtype.val (r.leftInverse a)

/-- Helper for Proposition 58.2: a retraction composed with the subtype inclusion is homotopic
to the identity map on the retract. -/
private lemma compInclusionHomotopicId (r : Set.Retraction A) :
    (r.toContinuousMap.comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).Homotopic
        (ContinuousMap.id A) := by
  -- Replace the composite by its strict identity equation, then use the constant homotopy.
  rw [r.compInclusion_eq_id]

end Set.Retraction

namespace Set.DeformationRetraction

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- Helper for Proposition 58.2: the inclusion composed with the endpoint retraction is
homotopic to the identity map on the ambient space. -/
private lemma inclusionCompRetractionHomotopicId (H : Set.DeformationRetraction A) :
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp
      H.toRetraction.toContinuousMap).Homotopic (ContinuousMap.id X) := by
  -- Reverse the deformation homotopy and then forget that it fixes `A` pointwise.
  have hAmbient : H.toRetraction.toAmbient.Homotopic (ContinuousMap.id X) :=
    ⟨H.toHomotopyRel.symm.toHomotopy⟩
  simpa only [Set.Retraction.toAmbient] using hAmbient

end Set.DeformationRetraction

namespace Set.IsDeformationRetract

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- Proposition 58.2: If `A` is a deformation retract of `X`, then `A` and `X` have the same
homotopy type. -/
theorem sameHomotopyType (hA : Set.IsDeformationRetract A) :
    SameHomotopyType A X := by
  -- Unpack the opaque predicate through its characterization by retraction data.
  obtain ⟨r, ⟨H⟩⟩ := (Set.isDeformationRetract_iff A).mp hA
  let deformation : Set.DeformationRetraction A :=
    Set.DeformationRetraction.ofHomotopyRel r H
  -- Assemble the inclusion and retraction with the two homotopy-inverse laws proved above.
  let equivalence : A ≃ₕ X :=
    { toFun := ⟨Subtype.val, continuous_subtype_val⟩
      invFun := deformation.toRetraction.toContinuousMap
      left_inv := deformation.toRetraction.compInclusionHomotopicId
      right_inv := deformation.inclusionCompRetractionHomotopicId }
  exact SameHomotopyType.ofHomotopyEquiv equivalence

end Set.IsDeformationRetract
