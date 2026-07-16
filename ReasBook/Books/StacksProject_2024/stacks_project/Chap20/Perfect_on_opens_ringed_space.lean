import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "Cpx[" U "]" => CochainComplex (openSubspaceModuleCategory X U) ℤ

open _root_.AlgebraicGeometry.RingedSpace.CochainComplex

namespace DerivedCategory

-- Proof sketch: a perfect representative gives strictly perfect local models after restricting the
-- representative complex to the chosen open cover, while conversely local strictly perfect models
-- for the restricted derived object can be transported to a representative complex of the ambient
-- derived object.
/-- A derived `𝒪_X`-module is perfect exactly when it admits an open covering on which
its restrictions are represented by strictly perfect complexes. This is the local-cover companion
to the source-facing owner `DerivedCategory.IsPerfect`. -/
theorem isPerfect_iff_exists_openCover
    (E : DModX) :
    IsPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, ∃ Ei : Cpx[U i],
            ∃ _ : DerivedCategory.Q.obj Ei ≅ E↾[U i],
              IsStrictlyPerfect Ei := by
  sorry

end DerivedCategory

end AlgebraicGeometry.RingedSpace
