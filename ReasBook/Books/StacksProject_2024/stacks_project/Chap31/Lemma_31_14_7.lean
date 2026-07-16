import Mathlib
import StacksProject_2024.stacks_project.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.stacks_project.Chap20.Lemma_20_36_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_14_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite
open scoped AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

-- Semantic recall note: the regular-section owner for Chapter 31 is
-- `LocallyRingedSpace.IsRegularSection` from Definition 31.14.6. This file specializes that
-- owner to the structure sheaf and combines it with the Chapter 20 multiplication-by-a-global-
-- section API and mathlib's `IsSMulRegular`, `Γ(X, U)`, and `IsAffineOpen` surfaces.

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "𝒪X" =>
  (SheafOfModules.unit X.toRingedSpace.ringCatSheaf : ModX)

private instance structureSheaf_tensorRight_isEquivalence :
    Functor.IsEquivalence (tensorRight 𝒪X) := by
  let η : 𝒪X ≅ 𝟙_ ModX := SheafOfModules.unitIsoTensorUnit
  exact
    (tensorRight_isEquivalence_iff_exists_tensor_inverse 𝒪X).2
      ⟨𝒪X, ⟨(η ▷ᵢ 𝒪X) ≪≫ λ_ 𝒪X ≪≫ η⟩, ⟨(Iso.refl 𝒪X ⊗ᵢ η) ≪≫ ρ_ 𝒪X ≪≫ η⟩⟩

/-- Lemma 31.14.7 (1): a global section of the structure sheaf of a locally ringed space is
regular if and only if its germ in every stalk is a nonzerodivisor. -/
theorem isRegularSection_iff_stalkwise
    (f : X.presheaf.obj (op ⊤)) :
    LocallyRingedSpace.IsRegularSection 𝒪X
      ((𝒪X).unitHomEquiv (RingedSpace.globalSectionMul f 𝒪X)) ↔
      ∀ x : X, IsSMulRegular (X.presheaf.stalk x) (X.presheaf.germ ⊤ x (by trivial) f) := sorry

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable [MonoidalCategory X.Modules]

local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)

local instance schemeToRingedSpaceModulesMonoidal :
    MonoidalCategory (RingedSpace.Modules X.toRingedSpace) := by
  simpa using (inferInstance : MonoidalCategory X.Modules)

private instance structureSheaf_tensorRight_isEquivalence :
    Functor.IsEquivalence (tensorRight 𝒪X) := by
  let η : 𝒪X ≅ 𝟙_ X.Modules := SheafOfModules.unitIsoTensorUnit
  exact
    (tensorRight_isEquivalence_iff_exists_tensor_inverse 𝒪X).2
      ⟨𝒪X, ⟨(η ▷ᵢ 𝒪X) ≪≫ λ_ 𝒪X ≪≫ η⟩, ⟨(Iso.refl 𝒪X ⊗ᵢ η) ≪≫ ρ_ 𝒪X ≪≫ η⟩⟩

/-- Lemma 31.14.7 (2): for a scheme, a global section is regular if and only if on every affine
open subset its restriction is a nonzerodivisor in the affine coordinate ring. -/
theorem isRegularSection_iff_forall_affineOpen
    (f : Γ(X, ⊤)) :
    LocallyRingedSpace.IsRegularSection 𝒪X
      ((𝒪X).unitHomEquiv (RingedSpace.globalSectionMul f 𝒪X)) ↔
      ∀ U : X.Opens, IsAffineOpen U →
        IsSMulRegular Γ(X, U) (X.presheaf.map (TopologicalSpace.Opens.leTop U).op f) := sorry

/-- Lemma 31.14.7 (3): for a scheme, requiring the restriction of a global section to be a
nonzerodivisor on every affine open is equivalent to requiring this on some affine open cover. -/
theorem forall_affineOpen_iff_exists_affineOpenCover
    (f : Γ(X, ⊤)) :
    (∀ U : X.Opens, IsAffineOpen U →
      IsSMulRegular Γ(X, U) (X.presheaf.map (TopologicalSpace.Opens.leTop U).op f)) ↔
      ∃ 𝒰 : X.OpenCover,
        (∀ i, IsAffineOpen ((𝒰.f i).opensRange)) ∧
          ∀ i,
            IsSMulRegular Γ(X, (𝒰.f i).opensRange)
              (X.presheaf.map (TopologicalSpace.Opens.leTop ((𝒰.f i).opensRange)).op f) := sorry

end AlgebraicGeometry.Scheme
