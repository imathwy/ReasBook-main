import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap20.Lemma_20_33_6

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The ambient derived category `D(\mathcal O_X)` of module sheaves on a ringed space. -/
abbrev ringedSpaceModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The inclusion of a closed subset into the ambient topological space underlying a ringed
space. -/
private abbrev closedSubsetInclusion
    (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inverse-image map on opens induced by the closed-subset inclusion is continuous for the
canonical Grothendieck topologies. -/
private instance closedSubsetInclusion_opensMap_isContinuous
    (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The restricted sheaf of rings `\mathcal O_X|_Z` on the closed subset `Z`. -/
private abbrev closedSubsetRestrictedRingCatSheaf
    (X : RingedSpace.{u}) (Z : Set X) :
    TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X)

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
private abbrev closedSubsetModuleCategory
    (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRestrictedRingCatSheaf X Z)

/-- The derived category `D(\mathcal O_X|_Z)` of module sheaves on the closed subset `Z`. -/
abbrev closedSubsetModuleDerived (X : RingedSpace.{u}) (Z : Set X) :=
  DerivedCategory (closedSubsetModuleCategory X Z)

/-- The localization functor from cochain complexes of `\mathcal O_X`-modules to
`D(\mathcal O_X)`. -/
private abbrev ringedSpaceModuleQ
    (X : RingedSpace.{u}) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ ringedSpaceModuleDerived X :=
  DerivedCategory.Q

/-- The localization functor from cochain complexes of `\mathcal O_X|_Z`-modules to
`D(\mathcal O_X|_Z)`. -/
private abbrev closedSubsetModuleQ
    (X : RingedSpace.{u}) (Z : Set X) :
    CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤ closedSubsetModuleDerived X Z :=
  DerivedCategory.Q

/-- The quasi-isomorphisms in cochain complexes of `\mathcal O_X`-modules. -/
private abbrev ringedSpaceModuleQis
    (X : RingedSpace.{u}) :=
  HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- Pushforward of `\mathcal O_X|_Z`-modules along the closed-subset inclusion `i : Z ↪ X`. -/
noncomputable abbrev closedSubsetModulePushforward
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} (closedSubsetInclusion X Z)).unit.app
      (RingedSpace.ringCatSheaf X))

-- Proof sketch: the module pushforward along `i : Z ↪ X` is the usual closed-subset pushforward on
-- sheaves together with restriction of scalars along the pulled-back structure sheaf. The
-- classical sections-with-support construction on a closed subset provides the corresponding right
-- adjoint.
/-- Pushforward from a closed subset is a left adjoint on sheaves of modules. -/
theorem closedSubsetModulePushforward_isLeftAdjoint
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetModulePushforward X Z).IsLeftAdjoint := sorry

/-- Pushforward from the closed subset is additive on sheaves of modules. -/
instance closedSubsetModulePushforward_additive
    (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModulePushforward X Z).Additive := sorry

/-- Pushforward from the closed subset preserves finite limits on sheaves of modules. -/
instance closedSubsetModulePushforward_preservesFiniteLimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteLimits (closedSubsetModulePushforward X Z) := sorry

/-- Pushforward from the closed subset preserves finite colimits on sheaves of modules. -/
instance closedSubsetModulePushforward_preservesFiniteColimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteColimits (closedSubsetModulePushforward X Z) := sorry

/-- The underived sections-with-support functor on `\mathcal O_X`-modules along the closed subset
`Z`, realized as the chosen right adjoint to pushforward from `Z`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (RingedSpace.Modules X) ⥤ closedSubsetModuleCategory X Z :=
  letI : (closedSubsetModulePushforward X Z).IsLeftAdjoint :=
    closedSubsetModulePushforward_isLeftAdjoint X hZ
  (closedSubsetModulePushforward X Z).rightAdjoint

/-- The sections-with-support functor is additive on sheaves of modules. -/
instance closedSubsetModuleSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetModuleSectionsWithSupportFunctor X hZ).Additive := sorry

/-- The cochain-level sections-with-support functor followed by localization to
`D(\mathcal O_X|_Z)`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportToDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ closedSubsetModuleDerived X Z :=
  ((closedSubsetModuleSectionsWithSupportFunctor X hZ).mapHomologicalComplex (up ℤ)) ⋙
    (closedSubsetModuleQ X Z)

-- Proof sketch: choose K-injective resolutions of complexes of `\mathcal O_X`-modules. Since
-- `\mathcal H_Z` is right adjoint to the exact functor `i_*`, it preserves K-injective complexes;
-- thus its total right derived functor is computed by applying `\mathcal H_Z` to a K-injective
-- representative.
/-- The cochain-level sections-with-support functor admits a total right derived functor. -/
theorem closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    Functor.HasRightDerivedFunctor
      (closedSubsetModuleSectionsWithSupportToDerived X hZ)
      (ringedSpaceModuleQis X) := sorry

/-- The canonical right-derived-functor instance for sections with support in the closed subset
`Z`. -/
instance closedSubsetModuleSectionsWithSupportToDerived_instHasRightDerivedFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    Functor.HasRightDerivedFunctor
      (closedSubsetModuleSectionsWithSupportToDerived X hZ)
      (ringedSpaceModuleQis X) :=
  closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor X hZ

/-- The derived pushforward functor `i_* : D(\mathcal O_X|_Z) \to D(\mathcal O_X)`. -/
noncomputable abbrev closedSubsetModulePushforwardDerived
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleDerived X Z ⥤ ringedSpaceModuleDerived X :=
  (closedSubsetModulePushforward X Z).mapDerivedCategory

/-- The derived sections-with-support functor
`R\mathcal H_Z : D(\mathcal O_X) \to D(\mathcal O_X|_Z)`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    ringedSpaceModuleDerived X ⥤ closedSubsetModuleDerived X Z :=
  (closedSubsetModuleSectionsWithSupportToDerived X hZ).totalRightDerived
    (ringedSpaceModuleQ X)
    (ringedSpaceModuleQis X)

/-- The object property on `D(\mathcal O_X)` cutting out objects whose cohomology sheaves are
supported on the subset `Z`. -/
abbrev closedSubsetSupportedDerivedProperty
    (X : RingedSpace.{u}) (Z : Set X) :
    ObjectProperty (ringedSpaceModuleDerived X) :=
  fun K ↦ moduleDerivedCohomologySupportedOn (RingedSpace.ringCatSheaf X) K Z

/-- The full subcategory `D_Z(\mathcal O_X)` of derived `\mathcal O_X`-modules with cohomology
supported on `Z`. -/
abbrev closedSubsetSupportedDerived
    (X : RingedSpace.{u}) (Z : Set X) :=
  (closedSubsetSupportedDerivedProperty X Z).FullSubcategory

/-- The inclusion `D_Z(\mathcal O_X) ↪ D(\mathcal O_X)` of the supported derived subcategory. -/
abbrev closedSubsetSupportedDerivedInclusion
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetSupportedDerived X Z ⥤ ringedSpaceModuleDerived X :=
  (closedSubsetSupportedDerivedProperty X Z).ι

section

variable (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)

-- Proof sketch: identify `R\mathcal H_Z(i_*K)` with `K` by Lemma `20.34.1`; then the cohomology
-- sheaves of `i_*K` are pushforwards from `Z`, so their stalks vanish off `Z`. Equivalently,
-- `i_*K` lies in the full subcategory cut out by cohomology support on `Z`.
/-- Lemma 20.34.2 (1): for `K ∈ D(\mathcal O_X|_Z)`, the derived pushforward `i_* K` has
cohomology supported on `Z`, hence defines an object of `D_Z(\mathcal O_X)`. -/
theorem closedSubsetModulePushforwardDerived_obj_mem_supported
    (K : closedSubsetModuleDerived X Z) :
    closedSubsetSupportedDerivedProperty X Z
      ((closedSubsetModulePushforwardDerived X Z).obj K) := sorry

/-- The derived pushforward `i_*` viewed as a functor into the supported subcategory
`D_Z(\mathcal O_X)`. -/
abbrev closedSubsetModulePushforwardDerivedToSupported
    (X : RingedSpace.{u}) {Z : Set X} :
    closedSubsetModuleDerived X Z ⥤ closedSubsetSupportedDerived X Z :=
  ObjectProperty.lift
    (closedSubsetSupportedDerivedProperty X Z)
    (closedSubsetModulePushforwardDerived X Z)
    (fun K ↦ closedSubsetModulePushforwardDerived_obj_mem_supported X K)

/-- The restriction of the derived sections-with-support functor `R\mathcal H_Z` to the supported
subcategory `D_Z(\mathcal O_X)`. -/
abbrev closedSubsetModuleSectionsWithSupportDerivedFromSupported
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetSupportedDerived X Z ⥤ closedSubsetModuleDerived X Z :=
  closedSubsetSupportedDerivedInclusion X Z ⋙
    (closedSubsetModuleSectionsWithSupportDerived X hZ)

-- Proof sketch: Lemma `20.34.1` gives the adjunction between derived pushforward and derived
-- sections with support. The unit is an isomorphism on `D(\mathcal O_X|_Z)`, and for an object of
-- `D_Z(\mathcal O_X)` the counit is an isomorphism because all cohomology sheaves are already
-- supported on `Z`. Therefore the lifted functor to the supported full subcategory is an
-- equivalence.
/-- The derived pushforward into `D_Z(\mathcal O_X)` is an equivalence. -/
theorem closedSubsetModulePushforwardDerivedToSupported_isEquivalence
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    Functor.IsEquivalence
      (closedSubsetModulePushforwardDerivedToSupported X :
        closedSubsetModuleDerived X Z ⥤ closedSubsetSupportedDerived X Z) := sorry

/-- Lemma 20.34.2 (2): the derived pushforward functor
`i_* : D(\mathcal O_X|_Z) \simeq D_Z(\mathcal O_X)` is the canonical equivalence onto the full
subcategory of objects whose cohomology is supported on `Z`; its inverse is the restriction of
`R\mathcal H_Z`, equivalently of `i^{-1}`, to that supported subcategory. -/
noncomputable abbrev closedSubsetModulePushforwardDerivedSupportedEquivalence
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetModuleDerived X Z ≌ closedSubsetSupportedDerived X Z :=
  letI : Functor.IsEquivalence
      (closedSubsetModulePushforwardDerivedToSupported X :
        closedSubsetModuleDerived X Z ⥤ closedSubsetSupportedDerived X Z) :=
    closedSubsetModulePushforwardDerivedToSupported_isEquivalence X hZ
  (closedSubsetModulePushforwardDerivedToSupported X :
    closedSubsetModuleDerived X Z ⥤ closedSubsetSupportedDerived X Z).asEquivalence

-- Proof sketch: the equivalence is constructed from the functor
-- `closedSubsetModulePushforwardDerivedToSupported X hZ`. The previous equivalence theorem
-- identifies its inverse uniquely up to unique isomorphism, and Lemma `20.34.1` supplies the
-- specific inverse candidate `R\mathcal H_Z` restricted to supported objects.
/-- The inverse of the supported-subcategory equivalence is the restricted derived
sections-with-support functor. -/
theorem closedSubsetModulePushforwardDerivedSupportedEquivalence_inverse_eq
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetModulePushforwardDerivedSupportedEquivalence X hZ).inverse =
      closedSubsetModuleSectionsWithSupportDerivedFromSupported X hZ := sorry

/-- The composite `i_* \circ R\mathcal H_Z` viewed as a functor from `D(\mathcal O_X)` to the
supported subcategory `D_Z(\mathcal O_X)`. -/
abbrev closedSubsetModulePushforwardSectionsWithSupportDerivedToSupported
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    ringedSpaceModuleDerived X ⥤ closedSubsetSupportedDerived X Z :=
  ObjectProperty.lift
    (closedSubsetSupportedDerivedProperty X Z)
    (closedSubsetModuleSectionsWithSupportDerived X hZ ⋙
      closedSubsetModulePushforwardDerived X Z)
    (fun K ↦
      closedSubsetModulePushforwardDerived_obj_mem_supported
        X
        ((closedSubsetModuleSectionsWithSupportDerived X hZ).obj K))

-- Proof sketch: start from the adjunction of Lemma `20.34.1`, then restrict its right adjoint to
-- the supported full subcategory using part (1). Part (2) identifies the supported subcategory
-- with the essential image of `i_*`, so this restricted composite is exactly the right adjoint to
-- the inclusion `D_Z(\mathcal O_X) ↪ D(\mathcal O_X)`.
/-- Lemma 20.34.2 (3): the composite functor
`i_* \circ R\mathcal H_Z : D(\mathcal O_X) \to D_Z(\mathcal O_X)` is right adjoint to the
inclusion `D_Z(\mathcal O_X) \to D(\mathcal O_X)`. -/
theorem closedSubsetSupportedDerivedInclusion_rightAdjoint
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    Nonempty
      (closedSubsetSupportedDerivedInclusion X Z ⊣
        closedSubsetModulePushforwardSectionsWithSupportDerivedToSupported X hZ) := sorry

end

end AlgebraicGeometry.RingedSpace
