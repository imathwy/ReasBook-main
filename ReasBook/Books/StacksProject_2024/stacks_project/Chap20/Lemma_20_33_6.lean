import StacksProject_2024.Chap13.Aux_13_17_1
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap20.Lemma_20_32_8
import StacksProject_2024.Chap20.Open_subspace_module_extension_derived
import StacksProject_2024.Chap20.Open_subspace_module_pushforward_along_derived

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open scoped TopCat

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
attribute [local instance] DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.33.6:
- primary domain: support conditions on cohomology sheaves of derived `𝒪_X`-modules and
  their interaction with restriction, open pushforward, and extension by zero;
- sampled owner declarations:
  `DerivedCategory (RingedSpace.Modules X)`,
  `SheafOfModules.support`,
  `moduleSupport`,
  `moduleSupportedOn`,
  `derivedCategoryCohomologyInProperty`,
  `moduleExtensionByZeroFromOpenDerived`,
  `modulePushforwardFromOpenDerived`;
- best owner abstraction: Chapter 17 already owns the support notion via
  `SheafOfModules.support`, `moduleSupport`, and the support-on-a-subset owner
  `moduleSupportedOn`, while Chapter 13 already owns the degreewise cohomology predicate
  `derivedCategoryCohomologyInProperty`; the ambient derived category `D(𝒪_X)`, the
  owner-file derived lower shriek `moduleExtensionByZeroFromOpenDerived X U`, the derived
  restriction owner `moduleRestrictionToOpenDerived X U`, and the derived open pushforward
  `modulePushforwardFromOpenDerived U` are reused from earlier Chapter 20 files, so this file
  should state the comparison directly through those existing owners rather than introducing local
  wrapper notions for support or open-subspace derived categories;
- primitive data: for part `(1)`, an open subset `U` and a derived module on `X` whose
  cohomology is supported on `U`; for part `(2)`, an open subset `U`, a closed subset `T ⊆ X`
  contained in `U`, and a derived module on that open subspace whose cohomology is supported on
  the induced subset `Subtype.val ⁻¹' T`;
- derived API: the two comparison isomorphism statements.

Source/core/bridge triage:
- `source-facing`: the two comparison statements in Lemma 20.33.6;
- `core/canonical`: `DerivedCategory (RingedSpace.Modules X)`, `SheafOfModules.support`,
  `derivedCategoryCohomologyInProperty`, `moduleSupportedOn`,
  `moduleExtensionByZeroFromOpenDerived`,
  `moduleRestrictionToOpenDerived`, `modulePushforwardFromOpenDerived`;
- `bridge/view`: the textbook term `Rj_*(E|_U)` is presented by the canonical composite owner
  `moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U`.
-/

section

variable {X : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DMod[" U "]" => moduleDerivedOnOpen X U
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation "DExt[" U "]" => moduleExtensionByZeroFromOpenDerived X U
local notation "DPush[" U "]" => modulePushforwardFromOpenDerived U
local notation "RPush[" U "]" => DRes[U] ⋙ DPush[U]

local instance ringedSpaceModules_categoryWithHomology_local :
    CategoryWithHomology (RingedSpace.Modules X) :=
  ringedSpaceModules_categoryWithHomology X

local instance openSubspaceModuleCategory_categoryWithHomology_local
    (U : Opens X.carrier) :
    CategoryWithHomology (openSubspaceModuleCategory X U) :=
  openSubspaceModuleCategory_categoryWithHomology X U

local instance moduleRestrictionToOpen_additive_local (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).Additive :=
  moduleRestrictionToOpen_additive X U

local instance modulePushforwardFromOpen_additive_local (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Additive :=
  modulePushforwardFromOpen_additive U

local instance ringedSpaceModules_Q_isLocalization :
    Functor.IsLocalization
      (DerivedCategory.Q :
        CochainComplex (RingedSpace.Modules X) ℤ ⥤ DModX)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
  DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp

local instance openSubspaceModuleCategory_Q_isLocalization
    (U : Opens X.carrier) :
    Functor.IsLocalization
      (DerivedCategory.Q :
        CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤ DMod[U])
      (HomologicalComplex.quasiIso (openSubspaceModuleCategory X U) (ComplexShape.up ℤ)) :=
  DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp

/-- Companion to Lemma 20.33.6: derived restriction to an open subspace is left adjoint to
derived open pushforward. -/
instance moduleRestrictionToOpenDerived_isLeftAdjoint
    (U : Opens X.carrier) :
    (DRes[U]).IsLeftAdjoint := by
  sorry

/-- Companion to Lemma 20.33.6: derived open pushforward is right adjoint to derived
restriction. -/
instance modulePushforwardFromOpenDerived_isRightAdjoint
    (U : Opens X.carrier) :
    (DPush[U]).IsRightAdjoint := by
  sorry

/-- The right adjoint chosen by `Adjunction.ofIsLeftAdjoint (moduleRestrictionToOpenDerived X U)`
is the canonical derived open pushforward `modulePushforwardFromOpenDerived U`. -/
theorem moduleRestrictionToOpenDerived_rightAdjoint_eq
    (U : Opens X.carrier) :
    (DRes[U]).rightAdjoint = DPush[U] := by
  sorry

/-- The canonical derived adjunction
`moduleRestrictionToOpenDerived X U ⊣ modulePushforwardFromOpenDerived U`. -/
noncomputable def moduleRestrictionToOpenDerivedAdjunction
    (U : Opens X.carrier) :
    DRes[U] ⊣ DPush[U] := by
  simpa [moduleRestrictionToOpenDerived_rightAdjoint_eq] using
    (Adjunction.ofIsLeftAdjoint (DRes[U]))

/-- The canonical unit natural transformation
`𝟭 D(𝒪_X) ⟶ moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U`. -/
noncomputable def moduleRestrictionToOpenDerivedUnitNatTrans
    (U : Opens X.carrier) :
    𝟭 DModX ⟶ RPush[U] :=
  (moduleRestrictionToOpenDerivedAdjunction (X := X) U).unit

-- Proof sketch: let `V = X \ U`. If every cohomology sheaf of `E` is supported on `U`, then
-- each cohomology sheaf restricts to zero on `V`, hence `E|_V = 0`. The restriction of
-- `Rj_* (E|_U)` to `V` is also zero, while its restriction to `U` identifies with `E|_U`.
-- Comparing on the open cover `X = U ∪ V` gives the claimed isomorphism.
/-- Lemma 20.33.6 (1), comparison-map form: if `j : U ↪ X` is an open subspace and every
cohomology sheaf of `E ∈ D(𝒪_X)` is supported on `U`, then the canonical map
`E ⟶ Rj_*(E|_U)` is an isomorphism. -/
@[stacks 08DF]
theorem isIso_restrictionToOpenDerivedToPushforwardFromOpenDerived_of_cohomologySupported
    (U : Opens X.carrier) (E : DModX)
    (hE : derivedCategoryCohomologyInProperty (moduleSupportedOn X U) E) :
    let η : E ⟶ (RPush[U]).obj E :=
      (moduleRestrictionToOpenDerivedUnitNatTrans (X := X) U).app E
    IsIso η := by
  sorry

/-- Lemma 20.33.6 (1): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`E ∈ D(𝒪_X)` is supported on `U`, then `E` is canonically isomorphic to `Rj_*(E|_U)`. Here
`Rj_*(E|_U)` is formalized by `(RPush[U]).obj E`. -/
@[stacks 08DF]
theorem isIsomorphic_restrictionToOpenDerived_pushforwardFromOpenDerived_of_cohomologySupported
    (U : Opens X.carrier)
    (E : DModX)
    (hE : derivedCategoryCohomologyInProperty (moduleSupportedOn X U) E) :
    IsIsomorphic E ((RPush[U]).obj E) := by
  let η : E ⟶ (RPush[U]).obj E :=
    (moduleRestrictionToOpenDerivedUnitNatTrans (X := X) U).app E
  haveI : IsIso η := by
    simpa [η] using
      (isIso_restrictionToOpenDerivedToPushforwardFromOpenDerived_of_cohomologySupported
        U E hE)
  exact ⟨asIso η⟩

-- Proof sketch: the Chapter 20 lower shriek `j_!` is the derived extension-by-zero owner
-- `moduleExtensionByZeroFromOpenDerived X U`. For a closed subset `T ⊆ X` contained in `U`, set
-- `V = X \ T` and `W = U ∩ V`. The support hypothesis on `Subtype.val ⁻¹' T` implies that `F`
-- restricts to zero on `W`, so both `j_! F` and `Rj_* F` vanish on `V`; their restrictions to
-- `U` both identify with `F`. Comparing on the open cover `X = U ∪ V` gives the canonical
-- comparison `j_! F ⟶ Rj_* F` as an isomorphism.
/-- Lemma 20.33.6 (2), comparison-map form: if `j : U ↪ X` is an open subspace and every
cohomology sheaf of `F ∈ D(𝒪_U)` is supported on the induced subset `Subtype.val ⁻¹' T ⊆ U`
of a closed subset `T ⊆ X` contained in `U`, then the canonical map `j_! F ⟶ Rj_* F` is an
isomorphism. -/
@[stacks 08DF]
theorem isIso_extensionByZeroDerivedToPushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {T : Set X}
    (hT_closed : IsClosed T) (hTU : T ⊆ U)
    (F : DMod[U])
    (hF :
      derivedCategoryCohomologyInProperty
        (moduleSupportedOn (X.restrict U.isOpenEmbedding) (Subtype.val ⁻¹' T)) F) :
    let η : F ⟶ (DRes[U]).obj ((DExt[U]).obj F) := by
      simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using
        ((Adjunction.ofIsLeftAdjoint (DExt[U])).unit.app F)
    let f : ((DExt[U]).obj F) ⟶ ((DPush[U]).obj F) := by
      letI : IsIso η :=
        moduleExtensionByZeroFromOpenDerived_restriction_unit_app_isIso U F
      let g : ((DExt[U]).obj F) ⟶ (DRes[U]).rightAdjoint.obj F :=
        ((Adjunction.ofIsLeftAdjoint (DRes[U])).homEquiv
          ((DExt[U]).obj F) F)
            ((asIso η).inv)
      simpa [moduleRestrictionToOpenDerived_rightAdjoint_eq] using g
    IsIso f := by
  sorry

/-- Lemma 20.33.6 (2): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`F ∈ D(𝒪_U)` is supported on the induced subset `Subtype.val ⁻¹' T ⊆ U` of a closed
subset `T ⊆ X` contained in `U`, then `j_! F` is canonically isomorphic to `Rj_* F`. Here
`j_!` is formalized by `(DExt[U]).obj F` and `Rj_*` by `(DPush[U]).obj F`; the support condition
on the open subspace is expressed canonically by `Subtype.val ⁻¹' T`. -/
@[stacks 08DF]
theorem isIsomorphic_extensionByZeroDerived_pushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {T : Set X}
    (hT_closed : IsClosed T) (hTU : T ⊆ U)
    (F : DMod[U])
    (hF :
      derivedCategoryCohomologyInProperty
        (moduleSupportedOn (X.restrict U.isOpenEmbedding) (Subtype.val ⁻¹' T)) F)
    : IsIsomorphic ((DExt[U]).obj F) ((DPush[U]).obj F) := by
  let η : F ⟶ (DRes[U]).obj ((DExt[U]).obj F) := by
    simpa [moduleExtensionByZeroFromOpenDerived_rightAdjoint_eq] using
      ((Adjunction.ofIsLeftAdjoint (DExt[U])).unit.app F)
  let f : ((DExt[U]).obj F) ⟶ ((DPush[U]).obj F) := by
    letI : IsIso η :=
      moduleExtensionByZeroFromOpenDerived_restriction_unit_app_isIso U F
    let g : ((DExt[U]).obj F) ⟶ (DRes[U]).rightAdjoint.obj F :=
      ((Adjunction.ofIsLeftAdjoint (DRes[U])).homEquiv
        ((DExt[U]).obj F) F)
          ((asIso η).inv)
    simpa [moduleRestrictionToOpenDerived_rightAdjoint_eq] using g
  haveI : IsIso f := by
    simpa [η, f] using
      (isIso_extensionByZeroDerivedToPushforwardFromOpen_of_cohomologySupported
        U hT_closed hTU F hF)
  exact ⟨asIso f⟩

end

end AlgebraicGeometry.RingedSpace
