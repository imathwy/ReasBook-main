import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap13.Lemma_13_17_1
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap20.Lemma_20_33_6
import StacksProject_2024.Chap20.Lemma_20_34_1

open CategoryTheory
open CategoryTheory.Adjunction
open CategoryTheory.ObjectProperty
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceClosedSubsetDerived
open scoped DerivedCategoryWithCohomologyIn

/- Domain-style sampling for Lemma 20.34.2:
- primary domain: the full derived subcategory `D_Z(𝒪_X)` cut out by cohomology support
  on a closed subset, together with the equivalence induced by closed-subset pushforward;
- sampled owner declarations:
  `moduleSupportedOn`,
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `closedSubsetSupportedDerived`,
  `ModuleDerived`,
  `closedSubsetModuleDerived`,
  `closedSubsetModulePushforwardDerived`,
  `closedSubsetModuleSectionsWithSupportDerived`,
  `moduleSupport`;
- best owner abstraction: Chapter 13 already owns the canonical derived full subcategory
  `D_{P}` for a module-level object property `P`; here the relevant source-facing specialization
  is the named support owner `moduleSupportedOn X Z` from Definition `17.5.1`, with derived
  subcategory
  `closedSubsetSupportedDerived X Z` and notation `D_Z[Z]`, while the closed-subset derived
  functors already belong to the Chapter 20 owner file `Lemma_20_34_1`; this file is therefore
  the `bridge/view` layer from those owners to the support-specialized `D_{P}`;
- primitive data: the closed subset `Z`, the closed-subset pushforward/sections-with-support
  derived functors from `20.34.1`, the Chapter 17 support owner `moduleSupport`, and the
  Chapter 13 full-subcategory owner `D_{P}` specialized through `moduleSupportedOn X Z`;
- derived API: the pushforward functor `D(𝒪_X|_Z) ⥤ D_Z(𝒪_X)`, the induced
  equivalence, and the right adjoint to the inclusion.

Source/core/bridge triage:
- `source-facing`: the supported derived subcategory `D_Z(𝒪_X)` and the equivalence
  `D(𝒪_X|_Z) ≌ D_Z(𝒪_X)`;
- `core/canonical`: `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`, `ModuleDerived`, `closedSubsetModuleDerived`,
  `closedSubsetModulePushforwardDerived X Z`, `closedSubsetModuleSectionsWithSupportDerived`,
  `moduleSupport`;
- `bridge/view`: the support-specialized lifts below, built directly from those owners without
  reintroducing a parallel full-subcategory owner. -/

section

variable (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)

/-- The full derived subcategory `D_Z(𝒪_X) ⊆ D(𝒪_X)` cut out by requiring
every cohomology sheaf to be supported on `Z`. -/
abbrev closedSubsetSupportedDerived (X : RingedSpace.{u}) (Z : Set X) :=
  D_{moduleSupportedOn X Z}

namespace ClosedSubsetDerived

/- Textbook surface notation for the supported derived subcategory `D_Z(𝒪_X)`. The
ambient ringed space is recovered from the subset `Z`. -/
@[inherit_doc AlgebraicGeometry.RingedSpace.closedSubsetSupportedDerived]
scoped[RingedSpaceClosedSubsetDerived] notation:max "D_Z[" Z:arg "]" =>
  AlgebraicGeometry.RingedSpace.closedSubsetSupportedDerived _ Z

end ClosedSubsetDerived

/-- The inclusion `D_Z(𝒪_X) ↪ D(𝒪_X)` of the supported derived full
subcategory. -/
abbrev closedSubsetSupportedDerivedInclusion
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetSupportedDerived X Z ⥤ ModuleDerived X :=
  (derivedCategoryCohomologyInProperty (moduleSupportedOn X Z)).ι

-- Proof sketch: identify `R𝓗_Z(i_* K)` with `K` by Lemma `20.34.1`; then the cohomology
-- sheaves of `i_*K` are pushforwards from `Z`, so their stalks vanish off `Z`. Equivalently,
-- `i_*K` lies in the full subcategory cut out by cohomology support on `Z`.
/-- Lemma 20.34.2 (1): for `K ∈ D(𝒪_X|_Z)`, the derived pushforward `i_* K` has cohomology
supported on `Z`, hence defines an object of `D_Z(𝒪_X)`. -/
@[stacks 0AEF]
theorem closedSubsetModulePushforwardDerived_obj_mem_supported
    (K : closedSubsetModuleDerived X Z) :
    derivedCategoryCohomologyInProperty (moduleSupportedOn X Z) ((i⋆[hZ]).obj K) := sorry

/-- The derived pushforward `i_*` viewed as a functor `D(𝒪_X|_Z) ⥤ D_Z(𝒪_X)`. -/
abbrev closedSubsetSupportedDerivedPushforward
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    closedSubsetModuleDerived X Z ⥤
      D_Z[Z] :=
  (derivedCategoryCohomologyInProperty (moduleSupportedOn X Z)).lift
    (i⋆[hZ])
    (fun K ↦ closedSubsetModulePushforwardDerived_obj_mem_supported X hZ K)

-- Proof sketch: Lemma `20.34.1` gives the adjunction between derived pushforward and derived
-- sections with support. The unit is an isomorphism on `D(𝒪_X|_Z)`, and for an object of
-- `D_Z(𝒪_X)` the counit is an isomorphism because all cohomology sheaves are already
-- supported on `Z`. Therefore the lifted functor to the supported full subcategory is an
-- equivalence.
/-- The derived pushforward into `D_Z(𝒪_X)` is an equivalence. -/
instance closedSubsetSupportedDerivedPushforward_isEquivalence
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    Functor.IsEquivalence (closedSubsetSupportedDerivedPushforward X Z hZ) := sorry

/-- The composite `i_* ∘ R𝓗_Z : D(𝒪_X) ⥤ D_Z(𝒪_X)`. -/
abbrev closedSubsetSupportedDerivedRightAdjoint
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    ModuleDerived X ⥤
      D_Z[Z] :=
  R𝓗[hZ] ⋙ closedSubsetSupportedDerivedPushforward X Z hZ

-- Proof sketch: start from the adjunction of Lemma `20.34.1`, then restrict its right adjoint to
-- the supported full subcategory using part (1). Part (2) identifies the supported subcategory
-- with the essential image of `i_*`, so this restricted composite is exactly the right adjoint to
-- the inclusion `D_Z(𝒪_X) ↪ D(𝒪_X)`.
/-- Lemma 20.34.2 (3): the inclusion `D_Z(𝒪_X) ↪ D(𝒪_X)` is a left adjoint, with
source-facing right adjoint `i_* ∘ R𝓗_Z` as in
`closedSubsetSupportedDerivedRightAdjoint X Z hZ`. -/
@[stacks 0AEF]
theorem closedSubsetSupportedDerivedInclusion_isLeftAdjoint
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (closedSubsetSupportedDerivedInclusion X Z).IsLeftAdjoint := by
  sorry

/-- Companion to Lemma 20.34.2 (3): the composite
`i_* ∘ R𝓗_Z : D(𝒪_X) ⥤ D_Z(𝒪_X)` is right adjoint. -/
instance closedSubsetSupportedDerivedRightAdjoint_isRightAdjoint
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (closedSubsetSupportedDerivedRightAdjoint X Z hZ).IsRightAdjoint :=
  by
    sorry

end

end AlgebraicGeometry.RingedSpace
