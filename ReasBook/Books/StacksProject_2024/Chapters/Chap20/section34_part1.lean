import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_34_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The inclusion of a closed subset into the ambient ringed space. -/
abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The induced map on open sets for a closed-subset inclusion is continuous for the canonical
Grothendieck topologies. -/
private instance closedSubsetInclusion_opensMap_isContinuous
    (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The restricted sheaf of rings `\mathcal O_X|_Z` on the closed subset `Z`. -/
abbrev closedSubsetRestrictedRingCatSheaf
    (X : RingedSpace.{u}) (Z : Set X) : TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X)

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
abbrev closedSubsetModuleCategory (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRestrictedRingCatSheaf X Z)

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on a ringed space. -/
abbrev ringedSpaceModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (SheafOfModules (RingedSpace.ringCatSheaf X))

/-- The unbounded derived category `D(\mathcal O_X|_Z)` of module sheaves on the closed subset
`Z`. -/
abbrev closedSubsetModuleDerived (X : RingedSpace.{u}) (Z : Set X) :=
  DerivedCategory (closedSubsetModuleCategory X Z)

/-- The localization functor from cochain complexes of `\mathcal O_X`-modules to
`D(\mathcal O_X)`. -/
abbrev ringedSpaceModuleQ (X : RingedSpace.{u}) :
    CochainComplex (SheafOfModules (RingedSpace.ringCatSheaf X)) ℤ ⥤ ringedSpaceModuleDerived X :=
  DerivedCategory.Q

/-- The localization functor from cochain complexes of `\mathcal O_X|_Z`-modules to
`D(\mathcal O_X|_Z)`. -/
abbrev closedSubsetModuleQ (X : RingedSpace.{u}) (Z : Set X) :
    CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤ closedSubsetModuleDerived X Z :=
  DerivedCategory.Q

/-- The quasi-isomorphisms in cochain complexes of `\mathcal O_X`-modules. -/
abbrev ringedSpaceModuleQis (X : RingedSpace.{u}) :=
  HomologicalComplex.quasiIso (SheafOfModules (RingedSpace.ringCatSheaf X)) (up ℤ)

/-- The quasi-isomorphisms in cochain complexes of `\mathcal O_X|_Z`-modules. -/
abbrev closedSubsetModuleQis (X : RingedSpace.{u}) (Z : Set X) :=
  HomologicalComplex.quasiIso (closedSubsetModuleCategory X Z) (up ℤ)

/-- Sheaves of modules on a ringed space admit injective resolutions. -/
private instance ringedSpaceModuleCategory_hasInjectiveResolutions
    (X : RingedSpace.{u}) :
    HasInjectiveResolutions (SheafOfModules (RingedSpace.ringCatSheaf X)) := sorry

/-- Pushforward of `\mathcal O_X|_Z`-modules along the closed-subset inclusion `i : Z ↪ X`. -/
noncomputable abbrev closedSubsetModulePushforward
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ SheafOfModules (RingedSpace.ringCatSheaf X) :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} (closedSubsetInclusion X Z)).unit.app
      (RingedSpace.ringCatSheaf X))

-- Proof sketch: the closed-subset support construction on `\mathcal O_X`-modules produces the
-- same Hom-set correspondence as for abelian sheaves, now in the restricted module category over
-- `\mathcal O_X|_Z`. This identifies pushforward from `Z` as a left adjoint.
/-- Pushforward of `\mathcal O_X|_Z`-modules along a closed subset inclusion is a left adjoint. -/
theorem closedSubsetModulePushforward_isLeftAdjoint
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetModulePushforward X Z).IsLeftAdjoint := sorry

/-- The underived sections-with-support functor on `\mathcal O_X`-modules along the closed subset
`Z`, defined as the chosen right adjoint to pushforward from `Z`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    SheafOfModules (RingedSpace.ringCatSheaf X) ⥤ closedSubsetModuleCategory X Z :=
  letI : (closedSubsetModulePushforward X Z).IsLeftAdjoint :=
    closedSubsetModulePushforward_isLeftAdjoint X hZ
  (closedSubsetModulePushforward X Z).rightAdjoint

-- Proof sketch: pushforward along the closed inclusion is exact on the underlying abelian sheaves,
-- so in particular it preserves biproducts and zero morphisms; this yields additivity on module
-- sheaves.
/-- Pushforward from the closed subset is additive on sheaves of modules. -/
instance closedSubsetModulePushforward_additive
    (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModulePushforward X Z).Additive := sorry

-- Proof sketch: a right adjoint between abelian categories preserves finite limits, hence
-- preserves the zero object and biproduct decompositions needed for additivity.
/-- The underived sections-with-support functor is additive. -/
instance closedSubsetModuleSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetModuleSectionsWithSupportFunctor X hZ).Additive := sorry

-- Proof sketch: closed-subset pushforward is exact, so the cochain-level pushforward functor
-- admits an everywhere-defined total left derived functor on the unbounded derived categories.
/-- Closed-subset pushforward has an everywhere-defined total left derived functor. -/
private theorem closedSubsetModulePushforward_hasLeftDerivedFunctor
    (X : RingedSpace.{u}) (Z : Set X) :
    (((closedSubsetModulePushforward X Z).mapHomologicalComplex (up ℤ)) ⋙
        (ringedSpaceModuleQ X)).HasLeftDerivedFunctor
      (closedSubsetModuleQis X Z) := sorry

attribute [local instance] closedSubsetModulePushforward_hasLeftDerivedFunctor

-- Proof sketch: resolve a complex on `X` by a K-injective complex and compute the underived
-- sections-with-support functor on that resolution. This gives an everywhere-defined total right
-- derived functor on the unbounded derived categories.
/-- The sections-with-support functor has an everywhere-defined total right derived functor. -/
private theorem closedSubsetModuleSectionsWithSupport_hasRightDerivedFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (((closedSubsetModuleSectionsWithSupportFunctor X hZ).mapHomologicalComplex (up ℤ)) ⋙
        (closedSubsetModuleQ X Z)).HasRightDerivedFunctor
      (ringedSpaceModuleQis X) := sorry

attribute [local instance] closedSubsetModuleSectionsWithSupport_hasRightDerivedFunctor

/-- The derived pushforward functor `i_* : D(\mathcal O_X|_Z) \to D(\mathcal O_X)` attached to a
closed subset inclusion. -/
noncomputable abbrev closedSubsetModulePushforwardDerived
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleDerived X Z ⥤ ringedSpaceModuleDerived X :=
  ((((closedSubsetModulePushforward X Z).mapHomologicalComplex (up ℤ)) ⋙
      (ringedSpaceModuleQ X))).totalLeftDerived
    (closedSubsetModuleQ X Z)
    (closedSubsetModuleQis X Z)

/-- The derived sections-with-support functor
`R\mathcal H_Z : D(\mathcal O_X) \to D(\mathcal O_X|_Z)`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    ringedSpaceModuleDerived X ⥤ closedSubsetModuleDerived X Z :=
  ((((closedSubsetModuleSectionsWithSupportFunctor X hZ).mapHomologicalComplex (up ℤ)) ⋙
      (closedSubsetModuleQ X Z))).totalRightDerived
    (ringedSpaceModuleQ X)
    (ringedSpaceModuleQis X)

-- Proof sketch: start from the underived adjunction
-- `closedSubsetModulePushforward X Z ⊣ closedSubsetModuleSectionsWithSupportFunctor X hZ`.
-- The previous two helper results identify the derived pushforward and derived
-- sections-with-support functors as the total left and right derived functors of that adjoint
-- pair, so the standard derived-adjunction formalism applies directly.
/-- Lemma 20.34.1: for a ringed space `(X, \mathcal O_X)` and a closed subset `Z \subset X`, the
derived sections-with-support functor
`R\mathcal H_Z : D(\mathcal O_X) \to D(\mathcal O_X|_Z)` is right adjoint to the derived
pushforward functor `i_* : D(\mathcal O_X|_Z) \to D(\mathcal O_X)`. -/
theorem closedSubsetModuleSectionsWithSupportDerived_rightAdjoint_to_pushforwardDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    Nonempty
      ((closedSubsetModulePushforwardDerived X Z) ⊣
        (closedSubsetModuleSectionsWithSupportDerived X hZ)) := sorry

-- Proof sketch: represent `K` by a K-injective complex on `Z`. Exactness of pushforward keeps the
-- pushforward complex suitable for computing the derived functor, and on such a representative
-- the underived sections-with-support functor returns the original complex. Passing to the derived
-- category gives the claimed isomorphism.
/-- Applying derived sections with support to the derived pushforward of an object on `Z`
recovers that object. -/
theorem closedSubsetModuleSectionsWithSupportDerived_obj_pushforwardDerived_iso
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    (K : closedSubsetModuleDerived X Z) :
    Nonempty
      (((closedSubsetModuleSectionsWithSupportDerived X hZ).obj
          ((closedSubsetModulePushforwardDerived X Z).obj K)) ≅ K) := sorry

-- Proof sketch: the previous derived identification shows that an object of the form `i_* 𝒢`,
-- with `𝒢` in degree zero on `Z`, is right-acyclic for the underived sections-with-support
-- functor. Therefore every positive right derived functor vanishes on `i_* 𝒢`.
/-- The higher local cohomology sheaves with support in `Z` vanish on pushforwards from `Z`. -/
theorem isZero_higherRightDerived_closedSubsetModuleSectionsWithSupport_of_pushforward
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    (𝒢 : closedSubsetModuleCategory X Z) (p : ℕ) :
    IsZero
      (((closedSubsetModuleSectionsWithSupportFunctor X hZ).rightDerived (p + 1)).obj
        ((closedSubsetModulePushforward X Z).obj 𝒢)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_34_2 (from Chap20) -/
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

/-! ### Lemma_20_34_3 (from Chap20) -/
open CategoryTheory

/- Domain-style sampling for Lemma 20.34.3:
- primary domain: K-injective cochain complexes under exact additive adjunctions between abelian
  categories;
- inspected owner declarations:
  `CochainComplex.IsKInjective`,
  `Functor.mapHomologicalComplex`,
  `CategoryTheory.exactFunctor`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstraction:
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`.

Source/core/bridge triage:
- `source-facing`: for a closed immersion `i : Z → X`, the sections-with-support functor
  `\mathcal H_Z` sends K-injective complexes of `\mathcal O_X`-modules to K-injective complexes of
  `\mathcal O_X|_Z`-modules;
- `core/canonical`: a right adjoint to an exact additive left adjoint preserves K-injective
  cochain complexes;
- `bridge/view`: this item, because after abstracting away the ringed-space realization, the only
  primitive data are the adjunction `i_* ⊣ \mathcal H_Z` and exactness of `i_*`.

Primitive data are therefore just the exact additive left adjoint and its right adjoint; the
K-injectivity of the mapped complex is derived API from the canonical Chapter 13 owner theorem.
Keeping a second theorem here with the same interface would be a duplicate local wrapper, so the
refined file is a direct recall of the owner declaration.
-/

/- Lemma 20.34.3: the closed-subset statement is exactly the Chapter 13 theorem saying that a
right adjoint to an exact additive left adjoint preserves K-injective cochain complexes. -/
recall right_adjoint_preserves_isKInjective_of_exact_left_adjoint

/-! ### Lemma_20_34_4 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of modules on a ringed space. -/
/-- The category of `\mathcal O_X`-modules on a ringed space is Grothendieck abelian. -/
instance sheafModules_isGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian (Modules X) := sorry

/-- The ring of global sections `Γ(X, \mathcal O_X)` of a ringed space. -/
abbrev globalSectionsRing (X : RingedSpace.{u}) : CommRingCat :=
  X.presheaf.obj (op (⊤ : Opens X.carrier))

/-- The global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSpace.{u}) :
    Modules X ⥤ ModuleCat (globalSectionsRing X) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op (⊤ : Opens X.carrier))

/-- The global-sections functor on module sheaves is additive. -/
instance moduleGlobalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).Additive := sorry

/-- The total right derived global-sections functor on `\mathcal O_X`-modules. -/
abbrev moduleDerivedGlobalSections (X : RingedSpace.{u}) :
    DerivedCategory (Modules X) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (moduleGlobalSectionsFunctor X)

/-- The underived functor of global sections with support in the closed subset `Z`, valued in
`Γ(X, \mathcal O_X)`-modules. It is formalized as global sections on `X` after pushing the
sections-with-support sheaf on `Z` back to `X`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    Modules X ⥤ ModuleCat (globalSectionsRing X) :=
  closedSubsetModuleSectionsWithSupportFunctor X hZ ⋙
    closedSubsetModulePushforward X Z ⋙
      moduleGlobalSectionsFunctor X

/-- The underived global-sections-with-support functor is additive. -/
instance closedSubsetModuleGlobalSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetModuleGlobalSectionsWithSupportFunctor X hZ).Additive := sorry

/-- The total right derived functor computing global sections with support in `Z`, viewed in
`D(Γ(X, \mathcal O_X(X)))`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    DerivedCategory (Modules X) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  CategoryTheory.additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (closedSubsetModuleGlobalSectionsWithSupportFunctor X hZ)

-- Proof sketch: the underived functor of sections with support in `Z` and values in
-- `Γ(X,\mathcal O_X(X))` is the composite
-- `\mathcal H_Z ⋙ i_* ⋙ \Gamma(X,-)`, where `i : Z ↪ X` is the closed-subset inclusion.
-- Choose K-injective resolutions on `X`, use Lemma `20.34.3` to see that `\mathcal H_Z`
-- preserves K-injectives, and use exactness of `i_*` to compare the total right derived functor
-- of the composite with the composite of the derived functors.
/-- Lemma 20.34.4: for a ringed space `(X, \mathcal O_X)` and the inclusion of a closed subset
`i : Z \to X`, the derived global-sections functor on `Z` composed with the derived
sections-with-support functor agrees with the derived global-sections-with-support functor on `X`.
In this file the codomain `D(\mathcal O_X(X))` is modeled by first pushing the supported sheaf on
`Z` forward to `X` and then applying `RΓ(X,-)`. -/
theorem closedSubsetModuleGlobalSectionsWithSupportDerived_iso_comp
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    IsIsomorphic
      (closedSubsetModuleSectionsWithSupportDerived X hZ ⋙
        closedSubsetModulePushforwardDerived X Z ⋙
        moduleDerivedGlobalSections X)
      (closedSubsetModuleGlobalSectionsWithSupportDerived X hZ) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_34_5 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.DerivedCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The inclusion of a closed subset into the ambient ringed space. -/
private abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The induced map on opens for a closed-subset inclusion is continuous for the canonical
Grothendieck topologies. -/
private instance closedSubsetInclusion_opensMap_isContinuous
    (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The restriction of the structure sheaf of `X` to the closed subspace `Z`. -/
private abbrev closedSubsetRingCatSheaf (X : RingedSpace.{u}) (Z : Set X) :
    TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X)

/-- The category of `\mathcal O_X|_Z`-modules on the closed subspace `Z`. -/
private abbrev closedSubsetModuleCategory (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRingCatSheaf X Z)

/-- Pushforward of `\mathcal O_X|_Z`-modules from the closed subspace `Z` to `X`. -/
private abbrev closedSubsetModulePushforward (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
      (closedSubsetInclusion X Z)).unit.app (RingedSpace.ringCatSheaf X))

-- Proof sketch: this is the module-valued closed-immersion adjunction. The pushforward functor
-- from `Z` to `X` is exact, and the usual sections-with-support construction provides its right
-- adjoint.
/-- Pushforward from the closed subspace is a left adjoint. -/
private theorem closedSubsetModulePushforward_isLeftAdjoint
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (closedSubsetModulePushforward X Z).IsLeftAdjoint := sorry

/-- The underived sections-with-support functor along the closed subset `Z`. -/
private abbrev closedSubsetModuleSectionsWithSupportFunctor
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (RingedSpace.Modules X) ⥤ closedSubsetModuleCategory X Z :=
  letI : (closedSubsetModulePushforward X Z).IsLeftAdjoint :=
    closedSubsetModulePushforward_isLeftAdjoint X Z hZ
  (closedSubsetModulePushforward X Z).rightAdjoint

/-- Pushforward from the closed subspace is additive. -/
private instance closedSubsetModulePushforward_additive
    (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetModulePushforward X Z).Additive := sorry

/-- Pushforward from the closed subspace preserves finite limits. -/
private instance closedSubsetModulePushforward_preservesFiniteLimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteLimits (closedSubsetModulePushforward X Z) := sorry

/-- Pushforward from the closed subspace preserves finite colimits. -/
private instance closedSubsetModulePushforward_preservesFiniteColimits
    (X : RingedSpace.{u}) (Z : Set X) :
    PreservesFiniteColimits (closedSubsetModulePushforward X Z) := sorry

/-- The underived sections-with-support functor is additive. -/
private instance closedSubsetModuleSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (closedSubsetModuleSectionsWithSupportFunctor X Z hZ).Additive := sorry

-- Proof sketch: resolve a complex of `\mathcal O_X`-modules by a K-injective complex and apply
-- the sections-with-support functor termwise; this computes the total right derived functor.
/-- The cochain-level sections-with-support functor admits a total right derived functor. -/
private theorem closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (((closedSubsetModuleSectionsWithSupportFunctor X Z hZ).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Q :
          CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤
            DerivedCategory (closedSubsetModuleCategory X Z))).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) := sorry

/-- The canonical right-derived-functor instance for sections with support along `Z`. -/
private instance closedSubsetModuleSectionsWithSupportToDerived_instHasRightDerivedFunctor
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    (((closedSubsetModuleSectionsWithSupportFunctor X Z hZ).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Q :
          CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤
            DerivedCategory (closedSubsetModuleCategory X Z))).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
  closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor X Z hZ

/-- The derived sections-with-support functor `R\mathcal H_Z : D(\mathcal O_X) \to
`D(\mathcal O_X|_Z)`. -/
private abbrev closedSubsetModuleSectionsWithSupportDerived
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (closedSubsetModuleCategory X Z) :=
  (((closedSubsetModuleSectionsWithSupportFunctor X Z hZ).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Q :
        CochainComplex (closedSubsetModuleCategory X Z) ℤ ⥤
          DerivedCategory (closedSubsetModuleCategory X Z))).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ))

/-- Exact closed-subset pushforward viewed on derived categories. -/
private abbrev closedSubsetModulePushforwardExactFunctor
    (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ₑ (RingedSpace.Modules X) :=
  ExactFunctor.of (closedSubsetModulePushforward X Z)

/-- Exact closed-subset pushforward viewed on derived categories. -/
private abbrev closedSubsetModulePushforwardDerived
    (X : RingedSpace.{u}) (Z : Set X) :
    DerivedCategory (closedSubsetModuleCategory X Z) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  let _ : (closedSubsetModulePushforwardExactFunctor X Z).obj.Additive :=
    closedSubsetModulePushforward_additive X Z
  (closedSubsetModulePushforwardExactFunctor X Z).obj.mapDerivedCategory

/-- The derived global-sections-with-support functor `RΓ_Z(X, -)` modeled in
`D(Γ(X, \mathcal O_X))` as derived global sections of the pushed-forward support sheaf. -/
private abbrev derivedGlobalSectionsWithSupport
    (X : RingedSpace.{u}) (Z : Set X) (hZ : IsClosed Z) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  closedSubsetModuleSectionsWithSupportDerived X Z hZ ⋙
    closedSubsetModulePushforwardDerived X Z ⋙
    moduleDerivedGlobalSections X

/-- The open complement `U = X \setminus Z` of the closed subset `Z`. -/
private abbrev openComplement {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z) :
    Opens X.carrier :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The restriction map on section rings from `Γ(X, \mathcal O_X)` to
`Γ(X \setminus Z, \mathcal O_X)`. -/
private abbrev sectionsRestrictionToOpenMap
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    globalSectionsRing X ⟶ sectionsRingOnOpen X (openComplement hZ) :=
  X.presheaf.map
    (homOfLE
      (show openComplement hZ ≤ (⊤ : Opens X.carrier) from
        fun _ _ ↦ trivial)).op

/-- Restriction of scalars from `Γ(X \setminus Z, \mathcal O_X)` to `Γ(X, \mathcal O_X)`. -/
private abbrev moduleSectionsRestrictionToOpenFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    ModuleCat (sectionsRingOnOpen X (openComplement hZ)) ⥤ ModuleCat (globalSectionsRing X) :=
  ModuleCat.restrictScalars (sectionsRestrictionToOpenMap X hZ).hom

/-- Restriction of scalars from the open-complement section ring is additive. -/
private instance moduleSectionsRestrictionToOpenFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (moduleSectionsRestrictionToOpenFunctor X hZ).Additive :=
  inferInstance

/-- Restriction of scalars from the open-complement section ring, viewed on derived categories. -/
private abbrev moduleSectionsRestrictionToOpenExactFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    ModuleCat (sectionsRingOnOpen X (openComplement hZ)) ⥤ₑ ModuleCat (globalSectionsRing X) :=
  ExactFunctor.of (moduleSectionsRestrictionToOpenFunctor X hZ)

/-- Restriction of scalars from the open-complement section ring, viewed on derived categories. -/
private abbrev moduleSectionsRestrictionToOpenDerivedFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X (openComplement hZ))) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  let _ : (moduleSectionsRestrictionToOpenExactFunctor X hZ).obj.Additive :=
    moduleSectionsRestrictionToOpenFunctor_additive X hZ
  (moduleSectionsRestrictionToOpenExactFunctor X hZ).obj.mapDerivedCategory

/-- The derived sections functor on the open complement `X \setminus Z`, viewed in
`D(Γ(X, \mathcal O_X))` by restriction of scalars. -/
private abbrev derivedSectionsAtOpenViaRestriction
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  moduleDerivedSectionsAtOpen X (openComplement hZ) ⋙
    moduleSectionsRestrictionToOpenDerivedFunctor X hZ

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

-- Proof sketch: choose a K-injective complex `I` representing `K`. By Lemma `20.32.1`, the
-- restriction `I|_U` is still K-injective on `U = X \setminus Z`, so `RΓ(U, K)` is computed by
-- `Γ(U, I)`. By Lemma `20.8.1` and the definition of sections with support, the sequence
-- `0 ⟶ Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(U, I) ⟶ 0` is exact. The associated triangle in
-- `D(Γ(X, \mathcal O_X))` is functorial in `K`.
/-- Lemma 20.34.5: for a ringed space `(X, \mathcal O_X)`, a closed subset `Z ⊆ X`, and
`U = X \setminus Z`, there are natural morphisms
`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`
in `D(Γ(X, \mathcal O_X))` whose evaluation at every `K ∈ D(\mathcal O_X)` is a distinguished
triangle. Here `RΓ_Z(X, -)` is formalized by `derivedGlobalSectionsWithSupport`, and `RΓ(U, -)` is
viewed in `D(Γ(X, \mathcal O_X))` by restriction of scalars along
`Γ(X, \mathcal O_X) ⟶ Γ(U, \mathcal O_X)`. -/
theorem derivedGlobalSectionsWithSupport_distinguishedTriangle :
    ∃ α : derivedGlobalSectionsWithSupport X Z hZ ⟶ moduleDerivedGlobalSections X,
      ∃ β :
          moduleDerivedGlobalSections X ⟶ derivedSectionsAtOpenViaRestriction X hZ,
        ∃ δ :
            derivedSectionsAtOpenViaRestriction X hZ ⟶
              derivedGlobalSectionsWithSupport X Z hZ ⋙
                shiftFunctor (DerivedCategory (ModuleCat (globalSectionsRing X))) (1 : ℤ),
          ∀ K : DerivedCategory (RingedSpace.Modules X),
            Triangle.mk (α.app K) (β.app K) (δ.app K) ∈
              distTriang (DerivedCategory (ModuleCat (globalSectionsRing X))) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_34_6 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {Z : Set X}

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf on the underlying
topological space. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : X.carrier.Sheaf RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X.carrier) (forget₂ CommRingCat RingCat.{u})).obj
    X.sheaf

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of modules on a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The inclusion of a closed subset into the underlying topological space of a ringed space. -/
abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X.carrier :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inverse-image map on opens induced by a closed subset inclusion is continuous for the
Grothendieck topologies on opens. -/
instance closedSubsetInclusion_opensMap_isContinuous :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The category of `\mathcal O_X|_Z`-modules on a closed subset `Z \subset X`. -/
abbrev ClosedSubsetSheafModules (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules
    ((TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj
      (ringedSpaceRingCatSheaf X))

/-- The derived category `D(\mathcal O_X|_Z)` on the closed subset `Z`. -/
abbrev ClosedSubsetModuleDerived (X : RingedSpace.{u}) (Z : Set X) :=
  DerivedCategory (ClosedSubsetSheafModules X Z)

/-- The open complement `U = X \setminus Z` of a closed subset `Z` in a ringed space `X`. -/
abbrev closedSubsetOpenComplement (hZ : IsClosed Z) : Opens X.carrier :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

local notation "ModX" => Modules X
local notation "ModZ" => ClosedSubsetSheafModules X Z
local notation "DModX" => ModuleDerived X
local notation "DModZ" => ClosedSubsetModuleDerived X Z
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DModX)
local notation "QZ" => (DerivedCategory.Q : CochainComplex ModZ ℤ ⥤ DModZ)
local notation "QisX" => HomologicalComplex.quasiIso ModX (up ℤ)

/-- The category of `\mathcal O_U`-modules on the open complement `U = X \setminus Z`. -/
abbrev OpenComplementSheafModules (hZ : IsClosed Z) :=
  SheafOfModules
    ((TopCat.Sheaf.pullback RingCat.{u} ((closedSubsetOpenComplement hZ).inclusion')).obj
      (ringedSpaceRingCatSheaf X))

/-- The derived category `D(\mathcal O_U)` on the open complement `U = X \setminus Z`. -/
abbrev OpenComplementModuleDerived (hZ : IsClosed Z) :=
  DerivedCategory (OpenComplementSheafModules hZ)

/-- Restriction of `\mathcal O_X`-modules to the open complement `U = X \setminus Z`. -/
abbrev moduleSheafRestrictionToComplement (hZ : IsClosed Z) :
    ModX ⥤ OpenComplementSheafModules hZ :=
  moduleSheafRestrictionToOpen (closedSubsetOpenComplement hZ) (ringedSpaceRingCatSheaf X)

/-- Restriction to the open complement is additive on sheaves of modules. -/
instance moduleSheafRestrictionToComplement_additive (hZ : IsClosed Z) :
    (moduleSheafRestrictionToComplement hZ).Additive := sorry

/-- Restriction to the open complement preserves finite limits on sheaves of modules. -/
instance moduleSheafRestrictionToComplement_preservesFiniteLimits (hZ : IsClosed Z) :
    PreservesFiniteLimits (moduleSheafRestrictionToComplement hZ) := sorry

/-- Restriction to the open complement preserves finite colimits on sheaves of modules. -/
instance moduleSheafRestrictionToComplement_preservesFiniteColimits (hZ : IsClosed Z) :
    PreservesFiniteColimits (moduleSheafRestrictionToComplement hZ) := sorry

/-- Pushforward of `\mathcal O_U`-modules from the open complement `U = X \setminus Z` back to
the ambient ringed space `X`. -/
noncomputable abbrev modulePushforwardFromComplement (hZ : IsClosed Z) :
    OpenComplementSheafModules hZ ⥤ ModX :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
        ((closedSubsetOpenComplement hZ).inclusion')).unit.app
      (ringedSpaceRingCatSheaf X))

/-- Pushforward from the open complement is additive on sheaves of modules. -/
instance modulePushforwardFromComplement_additive (hZ : IsClosed Z) :
    (modulePushforwardFromComplement hZ).Additive := sorry

/-- Pushforward from the open complement preserves finite limits on sheaves of modules. -/
instance modulePushforwardFromComplement_preservesFiniteLimits (hZ : IsClosed Z) :
    PreservesFiniteLimits (modulePushforwardFromComplement hZ) := sorry

/-- Pushforward from the open complement preserves finite colimits on sheaves of modules. -/
instance modulePushforwardFromComplement_preservesFiniteColimits (hZ : IsClosed Z) :
    PreservesFiniteColimits (modulePushforwardFromComplement hZ) := sorry

/-- The exact derived-category restriction functor to the open complement `U = X \setminus Z`. -/
noncomputable abbrev moduleDerivedRestrictionToComplement (hZ : IsClosed Z) :
    DModX ⥤ OpenComplementModuleDerived hZ :=
  (moduleSheafRestrictionToComplement hZ).mapDerivedCategory

/-- The derived pushforward functor from the open complement back to `D(\mathcal O_X)`. -/
noncomputable abbrev moduleDerivedPushforwardFromComplement (hZ : IsClosed Z) :
    OpenComplementModuleDerived hZ ⥤ DModX :=
  (modulePushforwardFromComplement hZ).mapDerivedCategory

/-- Pushforward of `\mathcal O_X|_Z`-modules along the closed-subset inclusion `i : Z ↪ X`. -/
noncomputable abbrev closedSubsetModulePushforward :
    ModZ ⥤ ModX :=
  SheafOfModules.pushforward
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
        (closedSubsetInclusion X Z)).unit.app
      (ringedSpaceRingCatSheaf X))

-- Proof sketch: pushforward along a closed inclusion has the classical right adjoint given by
-- sections with support in the closed subset, and the same adjunction lifts from abelian sheaves
-- to sheaves of modules over the restricted structure sheaf.
/-- Pushforward along the closed-subset inclusion is a left adjoint on module sheaves. -/
theorem closedSubsetModulePushforward_isLeftAdjoint
    (hZ : IsClosed Z) :
    (@closedSubsetModulePushforward X Z).IsLeftAdjoint := sorry

/-- The sections-with-support functor `\mathcal H_Z` on `\mathcal O_X`-modules, realized as the
chosen right adjoint to pushforward from the closed subset. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportFunctor
    (hZ : IsClosed Z) :
    ModX ⥤ ModZ :=
  letI : (@closedSubsetModulePushforward X Z).IsLeftAdjoint :=
    closedSubsetModulePushforward_isLeftAdjoint hZ
  (@closedSubsetModulePushforward X Z).rightAdjoint

/-- Pushforward from the closed subset is additive on sheaves of modules. -/
instance closedSubsetModulePushforward_additive :
    (@closedSubsetModulePushforward X Z).Additive := sorry

/-- Pushforward from the closed subset preserves finite limits on sheaves of modules. -/
instance closedSubsetModulePushforward_preservesFiniteLimits :
    PreservesFiniteLimits (@closedSubsetModulePushforward X Z) := sorry

/-- Pushforward from the closed subset preserves finite colimits on sheaves of modules. -/
instance closedSubsetModulePushforward_preservesFiniteColimits :
    PreservesFiniteColimits (@closedSubsetModulePushforward X Z) := sorry

/-- The sections-with-support functor is additive on sheaves of modules. -/
instance closedSubsetModuleSectionsWithSupportFunctor_additive
    (hZ : IsClosed Z) :
    (closedSubsetModuleSectionsWithSupportFunctor hZ).Additive := sorry

/-- The cochain-level sections-with-support functor followed by localization to the derived
category on the closed subset `Z`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportToDerived
    (hZ : IsClosed Z) :
    CochainComplex ModX ℤ ⥤ DModZ :=
  ((closedSubsetModuleSectionsWithSupportFunctor hZ).mapHomologicalComplex (up ℤ)) ⋙
    QZ

-- Proof sketch: choose K-injective resolutions of complexes of `\mathcal O_X`-modules. The
-- right adjoint `\mathcal H_Z` preserves K-injective complexes because its left adjoint
-- `i_*` is exact, so the total right derived functor is computed by applying
-- `\mathcal H_Z` degreewise to a K-injective representative.
/-- The cochain-level sections-with-support functor admits a total right derived functor. -/
theorem closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor
    (hZ : IsClosed Z) :
    Functor.HasRightDerivedFunctor (closedSubsetModuleSectionsWithSupportToDerived hZ) QisX :=
  sorry

/-- The canonical right-derived-functor instance for sections with support in the closed subset
`Z`. -/
instance closedSubsetModuleSectionsWithSupportToDerived_instHasRightDerivedFunctor
    (hZ : IsClosed Z) :
    Functor.HasRightDerivedFunctor (closedSubsetModuleSectionsWithSupportToDerived hZ) QisX :=
  closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor hZ

/-- The derived pushforward functor `i_* : D(\mathcal O_X|_Z) \to D(\mathcal O_X)` along the
closed-subset inclusion. Since pushforward is exact, it is represented on derived categories by
the induced functor. -/
noncomputable abbrev closedSubsetModulePushforwardDerived :
    DModZ ⥤ DModX :=
  (@closedSubsetModulePushforward X Z).mapDerivedCategory

/-- The total right derived functor `R\mathcal H_Z : D(\mathcal O_X) \to D(\mathcal O_X|_Z)`. -/
noncomputable abbrev closedSubsetModuleSectionsWithSupportDerived
    (hZ : IsClosed Z) :
    DModX ⥤ DModZ :=
  (closedSubsetModuleSectionsWithSupportToDerived hZ).totalRightDerived QX QisX

/-- The endofunctor `i_* R\mathcal H_Z` on `D(\mathcal O_X)` for a closed subset inclusion
`i : Z \hookrightarrow X`. -/
noncomputable abbrev closedSubsetDerivedLocalCohomologyEndofunctor
    (hZ : IsClosed Z) :
    DModX ⥤ DModX :=
  closedSubsetModuleSectionsWithSupportDerived hZ ⋙
    closedSubsetModulePushforwardDerived

/-- The endofunctor `Rj_*(-|_U)` on `D(\mathcal O_X)` for the open complement
`j : U = X \setminus Z \hookrightarrow X`. -/
noncomputable abbrev openComplementDerivedPushforwardEndofunctor
    (hZ : IsClosed Z) :
    DModX ⥤ DModX :=
  moduleDerivedRestrictionToComplement hZ ⋙
    moduleDerivedPushforwardFromComplement hZ

-- Proof sketch: choose a functorial K-injective resolution of each object of `D(\mathcal O_X)`.
-- Restriction to the open complement preserves K-injective complexes, so `Rj_*` is computed by
-- the underived pushforward of the restricted resolution. The right adjoint `\mathcal H_Z`
-- likewise computes `R\mathcal H_Z` on the same resolution because it preserves K-injectives.
-- Applying the underived short exact sequence
-- `0 → i_* \mathcal H_Z(\mathcal I^\bullet) → \mathcal I^\bullet →
--    j_*(\mathcal I^\bullet|_U) → 0`
-- from Lemma `20.8.1` degreewise produces the desired functorial distinguished triangle.
/-- Lemma 20.34.6: for a ringed space `(X, \mathcal O_X)` and a closed subset `Z \subset X`
with open complement `U = X \setminus Z`, there exist natural morphisms
`i_*R\mathcal H_Z(K) \to K \to Rj_*(K|_U) \to i_*R\mathcal H_Z(K)[1]`
whose evaluation at every `K \in D(\mathcal O_X)` is a distinguished triangle. -/
theorem closedSubsetDerived_localCohomology_triangle_functorial
    (hZ : IsClosed Z) :
    ∃ α :
        closedSubsetDerivedLocalCohomologyEndofunctor hZ ⟶ 𝟭 DModX,
      ∃ β :
          𝟭 DModX ⟶ openComplementDerivedPushforwardEndofunctor hZ,
        ∃ δ :
            openComplementDerivedPushforwardEndofunctor hZ ⟶
              closedSubsetDerivedLocalCohomologyEndofunctor hZ ⋙
                shiftFunctor DModX (1 : ℤ),
          ∀ K : DModX,
            Triangle.mk (α.app K) (β.app K) (δ.app K) ∈ distTriang DModX := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_34_7 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-- The structure sheaf of a ringed space, regarded as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The category of `\mathcal O_U`-modules obtained by pulling the structure sheaf of `X` back to
the open subspace `U`. -/
abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X))

/-- The open complement `X \setminus Z` of a closed subset `Z`. -/
abbrev closedSubsetOpenComplement {X : RingedSpace.{u}} {Z : Set X.carrier}
    (hZ : IsClosed Z) : Opens X.carrier :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The structural ring-sheaf morphism attached to the inclusion of the open subspace `U`. -/
noncomputable abbrev ringedSpaceOpenSubsetStructureSheafHom
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    ringedSpaceRingCatSheaf X ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} U.inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X)) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
    (ringedSpaceRingCatSheaf X)

/-- Pushforward of modules from the open subspace `U` back to the ambient ringed space. -/
noncomputable abbrev modulePushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ ambientModuleCategory X :=
  SheafOfModules.pushforward (ringedSpaceOpenSubsetStructureSheafHom U)

/-- Pushforward from an open subspace is additive on module sheaves. -/
instance modulePushforwardFromOpen_additive
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Additive := sorry

/-- Pushforward from an open subspace preserves finite limits on module sheaves. -/
instance modulePushforwardFromOpen_preservesFiniteLimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteLimits (modulePushforwardFromOpen U) := sorry

/-- Pushforward from an open subspace preserves finite colimits on module sheaves. -/
instance modulePushforwardFromOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (modulePushforwardFromOpen U) := sorry

/-- The derived pushforward functor from the open subspace `U` back to `X`. -/
noncomputable abbrev moduleDerivedPushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    DerivedCategory (openSubspaceModuleCategory X U) ⥤
      DerivedCategory (ambientModuleCategory X) :=
  (modulePushforwardFromOpen U).mapDerivedCategory

/-- The support of an abelian sheaf on a topological space, defined by nonzero stalks. -/
def abelianSheafSupport {Y : TopCat.{u}} (ℱ : Y.Sheaf AddCommGrpCat.{u}) : Set Y :=
  { y | ¬ IsZero (ℱ.presheaf.stalk y) }

/-- The cohomology sheaf of a derived module over a sheaf of rings on a topological space. -/
abbrev moduleDerivedCohomologySheaf
    {Y : TopCat.{u}} (𝒪 : Y.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf 𝒪).obj
    ((DerivedCategory.homologyFunctor (SheafOfModules 𝒪) q).obj K)

/-- A derived module has cohomology supported on `T` when every cohomology sheaf is supported on
`T`. -/
def moduleDerivedCohomologySupportedOn
    {Y : TopCat.{u}} (𝒪 : Y.Sheaf RingCat.{u})
    (K : DerivedCategory (SheafOfModules 𝒪)) (T : Set Y) : Prop :=
  ∀ q : ℤ, abelianSheafSupport (moduleDerivedCohomologySheaf 𝒪 K q) ⊆ T

-- Proof sketch: represent `K` by a K-injective complex on the open subspace `U`. Since
-- pushforward from an open immersion is exact, `Rj_* K` is computed by ordinary pushforward of
-- that representative. Stalks of the pushed-forward complex vanish outside `U`, hence in
-- particular on the closed subset `Z`; therefore every cohomology sheaf is supported in
-- `X \setminus Z`.
/-- Lemma 20.34.7: if `Z` is a closed subset of a ringed space `X` and `j : U \to X` is the
inclusion of an open subset with `U ∩ Z = ∅`, then for every `K ∈ D(\mathcal O_U)` the object
`Rj_* K` has cohomology sheaves supported in the open complement `X \setminus Z`. This is the
support-theoretic form used to express the vanishing of `R\mathcal H_Z(Rj_*K)`. -/
theorem pushforwardFromOpen_cohomologySupportedOn_complement_of_disjoint
    {Z : Set X.carrier} (hZ : IsClosed Z) (U : Opens X.carrier)
    (hUZ : Disjoint (U : Set X.carrier) Z)
    (K : DerivedCategory (openSubspaceModuleCategory X U)) :
    moduleDerivedCohomologySupportedOn
      (ringedSpaceRingCatSheaf X)
      ((moduleDerivedPushforwardFromOpen U).obj K)
      (closedSubsetOpenComplement hZ : Set X.carrier) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_34_8 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The inclusion of a closed subset into the underlying topological space of a ringed space. -/
abbrev closedSubsetInclusion
    (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inverse-image map on opens induced by the closed-subset inclusion is continuous for the
canonical Grothendieck topologies. -/
instance closedSubsetInclusion_opensMap_isContinuous
    (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
abbrev ClosedSubsetSheafModules (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules
    ((TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X))

/-- The abelian category of sheaves on the closed subset `Z` of a ringed space `X`. -/
abbrev ClosedSubsetAbelianSheafCat (X : RingedSpace.{u}) (Z : Set X) :=
  TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)

/-- The underived global-sections functor on abelian sheaves over the underlying space of a
ringed space. -/
abbrev abelianGlobalSectionsFunctor (X : RingedSpace.{u}) :
    AbelianSheafCat X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X.carrier))

/-- Global sections on abelian sheaves are additive. -/
instance abelianGlobalSectionsFunctor_additive (X : RingedSpace.{u}) :
    (abelianGlobalSectionsFunctor X).Additive := sorry

/-- The forgetful functor from `\mathcal O_X|_Z`-modules to their underlying abelian sheaves on
the closed subset `Z`. -/
abbrev closedSubsetUnderlyingAbelianSheafFunctor
    (X : RingedSpace.{u}) (Z : Set X) :
    ClosedSubsetSheafModules X Z ⥤ ClosedSubsetAbelianSheafCat X Z :=
  SheafOfModules.toSheaf
    ((TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj (RingedSpace.ringCatSheaf X))

/-- The derived forgetful functor from `D(\mathcal O_X|_Z)` to the derived category of abelian
sheaves on `Z`. -/
instance closedSubsetUnderlyingAbelianSheafFunctor_additive
    (X : RingedSpace.{u}) (Z : Set X) :
    (closedSubsetUnderlyingAbelianSheafFunctor X Z).Additive := sorry

/-- The derived forgetful functor from `D(\mathcal O_X|_Z)` to the derived category of abelian
sheaves on `Z`. -/
abbrev closedSubsetUnderlyingAbelianSheafDerived
    (X : RingedSpace.{u}) (Z : Set X)
    [IsGrothendieckAbelian.{u} (ClosedSubsetSheafModules X Z)] :
    closedSubsetModuleDerived X Z ⥤
      DerivedCategory (ClosedSubsetAbelianSheafCat X Z) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetUnderlyingAbelianSheafFunctor X Z)

/-- The functor of sections with support in `Z` on underlying abelian sheaves. -/
abbrev closedSubsetAbelianSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    AbelianSheafCat X ⥤ ClosedSubsetAbelianSheafCat X Z :=
  𝓗[hZ]

/-- The sections-with-support functor on abelian sheaves is additive. -/
instance closedSubsetAbelianSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetAbelianSectionsWithSupportFunctor X hZ).Additive := sorry

/-- The derived sections-with-support functor on underlying abelian sheaves. -/
abbrev closedSubsetAbelianSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤
      DerivedCategory (ClosedSubsetAbelianSheafCat X Z) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetAbelianSectionsWithSupportFunctor X hZ)

/-- The underived global-sections-with-support functor on `\mathcal O_X`-modules, viewed in
abelian groups after forgetting the module structure on global sections. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportAsAbelianFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  closedSubsetModuleSectionsWithSupportFunctor X hZ ⋙
    closedSubsetModulePushforward X Z ⋙
      moduleGlobalSectionsAdditiveFunctor X

/-- The total right derived functor computing `RΓ_Z(X, -)` in `D(\operatorname{Ab})`. -/
abbrev closedSubsetModuleGlobalSectionsWithSupportAsAbelianDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetModuleGlobalSectionsWithSupportAsAbelianFunctor X hZ)

/-- The underived global-sections-with-support functor on abelian sheaves over the underlying
space of `X`. -/
abbrev closedSubsetAbelianGlobalSectionsWithSupportFunctor
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    AbelianSheafCat X ⥤ AddCommGrpCat.{u} :=
  closedSubsetAbelianSectionsWithSupportFunctor X hZ ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubsetInclusion X Z) ⋙
      abelianGlobalSectionsFunctor X

/-- The underived abelian global-sections-with-support functor is additive. -/
instance closedSubsetAbelianGlobalSectionsWithSupportFunctor_additive
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z) :
    (closedSubsetAbelianGlobalSectionsWithSupportFunctor X hZ).Additive := sorry

/-- The total right derived functor computing `RΓ_Z(X, -)` on underlying abelian sheaves. -/
abbrev closedSubsetAbelianGlobalSectionsWithSupportDerived
    (X : RingedSpace.{u}) {Z : Set X} (hZ : IsClosed Z)
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (closedSubsetAbelianGlobalSectionsWithSupportFunctor X hZ)

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [IsGrothendieckAbelian.{u} (AbelianSheafCat X)]
variable [IsGrothendieckAbelian.{u} (ClosedSubsetSheafModules X Z)]
variable [IsGrothendieckAbelian.{u} (ClosedSubsetAbelianSheafCat X Z)]

local notation "DModX" => ringedSpaceModuleDerived X
local notation "Kab" => underlyingAbelianSheafDerived X
local notation "KabZ" => closedSubsetUnderlyingAbelianSheafDerived X Z
local notation "RGammaSupportMod" =>
  closedSubsetModuleGlobalSectionsWithSupportAsAbelianDerived X hZ
local notation "RGammaSupportAb" =>
  closedSubsetAbelianGlobalSectionsWithSupportDerived X hZ
local notation "RHSupportMod" =>
  closedSubsetModuleSectionsWithSupportDerived X hZ
local notation "RHSupportAb" =>
  closedSubsetAbelianSectionsWithSupportDerived X hZ

-- Proof sketch: for `RΓ_Z(X,-)`, compare the distinguished triangles of Lemmas `20.34.5` for
-- module sheaves and for underlying abelian sheaves, and use Lemma `20.32.7` on the two ordinary
-- derived-sections terms together with the two-out-of-three principle from Derived Categories,
-- Lemma `13.4.3`. For `R\mathcal H_Z`, repeat the same argument with the distinguished triangles
-- of Lemma `20.34.6`.
/-- Lemma 20.34.8: after forgetting `\mathcal O_X`-module structure to underlying abelian
sheaves, both derived global sections with support and derived sections with support agree with
their abelian local-cohomology counterparts. In other words, for `K_{ab}` the image of
`K ∈ D(\mathcal O_X)` in the derived category of abelian sheaves on `X`, the canonical
comparisons `RΓ_Z(X, K) → RΓ_Z(X, K_{ab})` in `D(\operatorname{Ab})` and
`R\mathcal H_Z(K) → R\mathcal H_Z(K_{ab})` in `D(\underline{\mathbf Z}_Z)` are isomorphisms. -/
theorem localCohomologyWithSupport_underlyingAbelian_isomorphic
    (K : DModX) :
    IsIsomorphic
        ((RGammaSupportMod).obj K)
        ((RGammaSupportAb).obj ((Kab).obj K)) ∧
      IsIsomorphic
        ((KabZ).obj ((RHSupportMod).obj K))
        ((RHSupportAb).obj ((Kab).obj K)) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_34_9 (from Chap20) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

local notation "DModX" => ringedSpaceModuleDerived X
local notation "DModZ" => closedSubsetModuleDerived X Z

variable (restrictionToClosedSubset : DModX ⥤ DModZ)
variable
    (pushforwardSectionsAdj :
      closedSubsetModulePushforwardDerived X Z ⊣
        closedSubsetModuleSectionsWithSupportDerived X hZ)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
variable
    (pushforwardTensorToAmbient :
      ∀ (K : DModX) (L : DModZ),
        (closedSubsetModulePushforwardDerived X Z).obj
            ((derivedTensorZ.obj L).obj (restrictionToClosedSubset.obj K)) ⟶
          ((derivedTensorX.obj ((closedSubsetModulePushforwardDerived X Z).obj L)).obj K))

/-- The pushforward-side morphism whose adjoint transpose gives the closed-subset tensor map. -/
private noncomputable abbrev
    closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_adjoint
    (K M : DModX) :
    (closedSubsetModulePushforwardDerived X Z).obj
        ((derivedTensorZ.obj ((closedSubsetModuleSectionsWithSupportDerived X hZ).obj M)).obj
          (restrictionToClosedSubset.obj K)) ⟶
      ((derivedTensorX.obj M).obj K) :=
  pushforwardTensorToAmbient K
      ((closedSubsetModuleSectionsWithSupportDerived X hZ).obj M) ≫
    ((derivedTensorX.map (pushforwardSectionsAdj.counit.app M)).app K)

/-- Remark 20.34.9: for a ringed space `(X, \mathcal O_X)` and a closed subset `i : Z \hookrightarrow X`,
once `restrictionToClosedSubset` is a chosen model for the restriction functor `K \mapsto K|_Z`,
the adjunction `i_* ⊣ R\mathcal H_Z` and the canonical pushforward-side tensor map determine a
canonical morphism
`K|_Z \otimes_{\mathcal O_X|_Z}^{\mathbf L} R\mathcal H_Z(M) \to
  R\mathcal H_Z(K \otimes_{\mathcal O_X}^{\mathbf L} M)`
in `D(\mathcal O_X|_Z)`. -/
noncomputable def closedSubsetRestrictionTensor_sectionsWithSupportDerived_map
    (K M : DModX) :
    ((derivedTensorZ.obj ((closedSubsetModuleSectionsWithSupportDerived X hZ).obj M)).obj
      (restrictionToClosedSubset.obj K)) ⟶
      (closedSubsetModuleSectionsWithSupportDerived X hZ).obj
        ((derivedTensorX.obj M).obj K) :=
  pushforwardSectionsAdj.homEquiv _ _
    (closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_adjoint
      hZ restrictionToClosedSubset pushforwardSectionsAdj
      derivedTensorX derivedTensorZ pushforwardTensorToAmbient K M)

-- Proof sketch: unfold the definition. The displayed morphism is defined to be the adjoint
-- transpose, under `i_* ⊣ R\mathcal H_Z`, of the pushforward-side map
-- `i_*(K|_Z \otimes^{\mathbf L} R\mathcal H_Z(M)) \to K \otimes^{\mathbf L} M`, obtained by
-- composing the tensor comparison with the adjunction counit `i_* R\mathcal H_Z(M) \to M`.
/-- The canonical closed-subset tensor map is adjoint to the corresponding pushforward-side tensor
comparison followed by the counit map `i_* R\mathcal H_Z(M) \to M`. -/
theorem closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_homEquiv
    (K M : DModX) :
    (pushforwardSectionsAdj.homEquiv _ _).symm
        (closedSubsetRestrictionTensor_sectionsWithSupportDerived_map
          hZ restrictionToClosedSubset pushforwardSectionsAdj
          derivedTensorX derivedTensorZ pushforwardTensorToAmbient K M) =
      closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_adjoint
        hZ restrictionToClosedSubset pushforwardSectionsAdj
        derivedTensorX derivedTensorZ pushforwardTensorToAmbient K M := sorry

end

end AlgebraicGeometry.RingedSpace
