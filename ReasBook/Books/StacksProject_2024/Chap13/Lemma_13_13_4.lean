import Mathlib
import stacks_project.Chap12.Lemma_12_16_2
import stacks_project.Chap13.Definition_13_13_2
import stacks_project.Chap13.Lemma_13_13_3
import stacks_project.Chap13.Lemma_13_6_3
import stacks_project.Chap13.Lemma_13_6_11
import stacks_project.Chap13.Lemma_13_6_6
import stacks_project.Chap13.Lemma_13_6_10
import stacks_project.Chap13.Lemma_13_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)
local notation "KFilt" => HomotopyCategory FilF (ComplexShape.up ℤ)

local instance finiteFiltered_hasFiniteBiproducts_13_13_4 : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance finiteFiltered_hasBinaryBiproducts_13_13_4 : HasBinaryBiproducts FilF :=
  Limits.hasBinaryBiproducts_of_finite_biproducts _

local notation "H0gr" =>
  filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) 0

local instance filteredAssociatedGradedZeroHomology_isHomological :
    (H0gr).IsHomological := by
  infer_instance

/- Domain-style sampling for Lemma `13.13.4`.
- primary domain: triangulated localizations defined by the homological kernel of a homological
  functor on a homotopy category;
- sampled owner declarations in this domain:
  `filteredAssociatedGradedHomotopyFunctor 𝒜`,
  `HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0`,
  `Functor.homologicalKernel`,
  `ObjectProperty.trW`,
  `MorphismProperty.Q`;
- best owner abstraction: the canonical homological-kernel owner
  `((filteredAssociatedGradedHomotopyFunctor 𝒜) ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0).homologicalKernel`,
  together with its derived Verdier morphism property and localization functor;
- primitive data: the canonical composite `H^0 ∘ gr` built from
  `filteredAssociatedGradedHomotopyFunctor 𝒜` and the degree-zero homology functor;
- derived API: its homological kernel, the induced morphism property `.trW`, and the localization
  functor `.Q`;
- source/core/bridge triage:
  `source-facing`: the filtered acyclic object property `FAc(𝒜)` and the filtered
    quasi-isomorphism property `FQis(𝒜)`;
  `core/canonical`: `Functor.homologicalKernel`, `ObjectProperty.trW`, and `MorphismProperty.Q`;
  `bridge/view`: the identifications in this file between `FAc(𝒜)`, `FQis(𝒜)`, and the canonical
    homological-kernel localization package.

This file therefore keeps the source-facing `FAc(𝒜)`/`FQis(𝒜)` statements while using the
canonical composite `H^0 ∘ gr` directly, without any parallel local wrapper around that owner or
around the localization functor `(FQis(𝒜) : MorphismProperty KFilt).Q`. The only inverted-morphism
input needed below is the canonical bridge
`Functor.homologicalKernel_trW_isInvertedBy` from Lemma `13.6.11`. -/

/-- The filtered acyclic objects are exactly the homological kernel of `H^0 ∘ gr`. -/
theorem filteredAcyclic_eq_homologicalKernel :
    (FAc(𝒜) : ObjectProperty KFilt) = (H0gr).homologicalKernel :=
  sorry

/-- The Verdier morphism property of filtered acyclic objects is the filtered quasi-isomorphism
property. -/
theorem filteredAcyclic_trW_eq_filteredQuasiIso :
    (FAc(𝒜) : ObjectProperty KFilt).trW =
      (FQis(𝒜) : MorphismProperty KFilt) := sorry

/-- Lemma 13.13.4 (1): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is strictly full. -/
instance filteredAcyclic_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

/-- Lemma 13.13.4 (2): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is saturated. -/
instance filteredAcyclic_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

/-- Lemma 13.13.4 (3): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is triangulated. -/
instance filteredAcyclic_isTriangulated :
    ObjectProperty.IsTriangulated
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

/-- Lemma 13.13.4 (4): the corresponding saturated multiplicative system of
`K(Fil^f(𝒜))` is the set `FQis(𝒜)` of filtered quasi-isomorphisms. -/
instance filteredQuasiIso_isSaturatedMultiplicativeSystem :
    IsSaturatedMultiplicativeSystem (FQis(𝒜) : MorphismProperty KFilt) := by
  sorry

-- Proof sketch: apply Lemma `13.6.10` to the triangulated subcategory
-- `FAc(𝒜) = (H^0 ∘ gr).homologicalKernel`, whose associated
-- multiplicative system is by definition `FQis(𝒜)`.
/-- Lemma 13.13.4 (5): the kernel of the localization functor
`Q : K(Fil^f(𝒜)) ⥤ FQis(𝒜)⁻¹K(Fil^f(𝒜))` is `FAc(𝒜)`. -/
theorem kernel_filteredQuasiIsomorphismLocalizationFunctor :
    Functor.kernel
        (((FQis(𝒜) : MorphismProperty KFilt).Q) :
          KFilt ⥤
            (FQis(𝒜) : MorphismProperty KFilt).Localization) =
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

-- Proof sketch: the canonical composite `H^0 ∘ gr` is homological by
-- Lemma `13.13.3`, so `Functor.mem_homologicalKernel_trW_iff` shows that the canonical
-- morphism property `((H^0 ∘ gr).homologicalKernel).trW` is inverted. The required factorization
-- is then the direct canonical localization lift through the quotient functor
-- `(FQis(𝒜) : MorphismProperty KFilt).Q`.
/-- Lemma 13.13.4 (6): the functor `H^0 ∘ gr` factors through the localization functor
`Q : K(Fil^f(𝒜)) ⥤ FQis(𝒜)⁻¹K(Fil^f(𝒜))`. -/
theorem exists_filteredGradedZeroHomologyFunctor_factorization :
    ∃ H' :
        (FQis(𝒜) : MorphismProperty KFilt).Localization ⥤
          GradedObject ℤ 𝒜,
      (((FQis(𝒜) : MorphismProperty KFilt).Q) :
          KFilt ⥤
        (FQis(𝒜) : MorphismProperty KFilt).Localization) ⋙
          H' =
        H0gr := by
  sorry

end CategoryTheory
