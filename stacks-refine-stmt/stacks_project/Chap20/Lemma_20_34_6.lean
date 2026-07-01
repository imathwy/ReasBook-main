import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

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
