import Mathlib
import StacksProject_2024.Chap20.Definition_20_48_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, HasCountableCoproducts (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, MonoidalCategory (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, MonoidalPreadditive (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, HasColimits (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, (curriedTensor (openSubspaceModuleCategory X U)).Additive]
variable [∀ U : Opens X.carrier,
  ∀ ℱ : openSubspaceModuleCategory X U,
    ((curriedTensor (openSubspaceModuleCategory X U)).obj ℱ).Additive]
variable [∀ U : Opens X.carrier,
  ∀ (ℱ 𝒢 : CochainComplex (openSubspaceModuleCategory X U) ℤ),
    CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (openSubspaceModuleCategory X U))]
variable [∀ U : Opens X.carrier,
  CategoryWithHomology (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  HasCountableCoproducts (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  MonoidalCategory (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  MonoidalPreadditive (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  HasColimits (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  (curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding))).Additive]
variable [∀ U : Opens X.carrier,
  ∀ ℱ : RingedSpace.Modules (X.restrict U.isOpenEmbedding),
    ((curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding))).obj ℱ).Additive]
variable [∀ U : Opens X.carrier,
  ∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules (X.restrict U.isOpenEmbedding)) ℤ),
    CochainComplex.HasMapBifunctor ℱ 𝒢
      (curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding)))]

/-- A complex on an open subspace is strictly perfect when it is bounded and each term is a
retract of a finite free module sheaf. -/
def CochainComplex.IsStrictlyPerfectRelativeToOpen {U : Opens X.carrier}
    (K : CochainComplex (openSubspaceModuleCategory X U) ℤ) : Prop :=
  (∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) ∧
    ∀ j : ℤ, ∃ I : Type u, Finite I ∧
      Nonempty
        (Retract (K.X j) (SheafOfModules.free.{u} I : openSubspaceModuleCategory X U))

namespace DerivedCategory

local notation "DMod" => DerivedCategory (Modules X)
local notation "OpenComplex" U => CochainComplex (openSubspaceModuleCategory X U) ℤ

/-- A derived `\mathcal O_X`-module has a local strictly perfect presentation when it is
represented on some open cover by quasi-isomorphisms from strictly perfect complexes. -/
def HasLocalStrictlyPerfectPresentation (E : DMod) : Prop :=
  ∃ K : CochainComplex (Modules X) ℤ,
    ∃ _ : E ≅ ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DMod).obj K),
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        iSup U = ⊤ ∧
          ∀ i : ι, ∃ Ki : OpenComplex (U i),
            ∃ α : Ki ⟶
                (((moduleRestrictionToOpen X (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  K),
              CochainComplex.IsStrictlyPerfectRelativeToOpen Ki ∧ QuasiIso α

/-- A derived `\mathcal O_X`-module has a local pseudo-coherent presentation when one chosen
representative admits, for every degree bound `m`, a local strictly perfect approximation that is
cohomologically an isomorphism above `m` and an epimorphism in degree `m`. -/
def HasLocalPseudoCoherentPresentation (E : DMod) : Prop :=
  ∃ K : CochainComplex (Modules X) ℤ,
    ∃ _ : E ≅ ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DMod).obj K),
      ∀ m : ℤ,
        ∃ (ι : Type u) (U : ι → Opens X.carrier),
          iSup U = ⊤ ∧
            ∀ i : ι, ∃ Ki : OpenComplex (U i),
              ∃ α : Ki ⟶
                  (((moduleRestrictionToOpen X (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                    K),
                CochainComplex.IsStrictlyPerfectRelativeToOpen Ki ∧
                  (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
                    Epi (HomologicalComplex.homologyMap α m)

-- Proof sketch: if `E` has a local strictly perfect presentation, then those local models give
-- pseudo-coherent approximations in every degree and finite tor amplitude on each open by the
-- strictly perfect case. Conversely, refine to an open cover with bounded tor amplitude, use the
-- pseudo-coherent presentations in degree `a - 1`, and apply the local perfection criterion of
-- the source proof on each member of the cover.
/-- Lemma 20.49.5: for an object `E` of `D(\mathcal O_X)`, perfection is equivalent to being
pseudo-coherent and locally of finite tor dimension. -/
theorem perfect_iff_pseudoCoherent_and_locallyHasFiniteTorDimension
    (E : DMod) :
    HasLocalStrictlyPerfectPresentation E ↔
      HasLocalPseudoCoherentPresentation E ∧ LocallyHasFiniteTorDimension E := sorry

end DerivedCategory

end

end AlgebraicGeometry.RingedSpace
