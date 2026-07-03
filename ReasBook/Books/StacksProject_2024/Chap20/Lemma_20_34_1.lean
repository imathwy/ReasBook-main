import Mathlib

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
