import StacksProject_2024.Chap21.Definition_21_47_1
import StacksProject_2024.Chap21.Lemma_21_20_4

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite.CochainComplex (IsStrictlyPerfect)
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open scoped RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false
set_option linter.unusedSectionVars false

namespace RingedSite.DerivedCategory

section

/- Domain-style sampling for Lemma 21.47.2:
- primary domain: perfect complexes and perfect derived objects of `𝒪_X`-modules on a
  ringed site;
- sampled owner declarations:
  `RingedSite.CochainComplex.IsPerfect`,
  `RingedSite.Hom.ModuleDerived.IsPerfect`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `RingedSite.DerivedCategory.isPerfect_of_exists_cover_on_finalObject`,
  `RingedSite.Hom.ModuleDerived.IsPerfect.of_representation`;
- best owner abstraction:
  `source-facing`: the final-object perfectness criterion in
    `RingedSite.DerivedCategory` together with the representative companion
    `RingedSite.Hom.ModuleDerived.IsPerfect.of_representation`;
  `core/canonical`: `RingedSite.CochainComplex.IsPerfect`,
    `RingedSite.Hom.ModuleDerived.IsPerfect`, and `localizedRestrictionDerived`;
  `bridge/view`: the chosen local comparison isomorphisms on the cover and the representing
    isomorphism `DerivedCategory.Q.obj K ≅ E`.
- primitive data: the derived object `E`, a final object `U : X`, and a cover of `U` carrying
  local strictly perfect models of the localized restrictions of `E`;
- derived API: the final-object cover criterion for perfectness and the representative-invariance
  theorem below.

Source/core/bridge triage:
- `source-facing`: `RingedSite.DerivedCategory.isPerfect_of_exists_cover_on_finalObject` and
  `RingedSite.Hom.ModuleDerived.IsPerfect.of_representation`;
- `core/canonical`: `RingedSite.CochainComplex.IsPerfect`,
  `RingedSite.Hom.ModuleDerived.IsPerfect`, and `localizedRestrictionDerived`;
- `bridge/view`: the internal local-derived-models predicate used to pass between source-facing
  cover data and the complex-level perfectness owner. -/
variable {X : RingedSite.{u, v}}
variable [HasBinaryProducts X.carrier]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]
variable [∀ U : X, HasBinaryProducts (X.localization U).carrier]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{max u v}]
variable [∀ U : X, (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]

local notation "Mod" => ModuleCat X
local notation "ModLoc" U => ModuleCat (X.localization U)
local notation "Cpx" => CochainComplex Mod ℤ
local notation "DMod" => ModuleDerived X

/-- A complex has local derived strictly perfect models if each localized restriction is covered
by a strictly perfect complex in the corresponding localized derived category. -/
private def HasLocalStrictlyPerfectDerivedModels (K : Cpx) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
      IsStrictlyPerfect E' ∧
        ∃ α : DerivedCategory.Q.obj E' ⟶ (j[I.Y]⁻¹).obj (DerivedCategory.Q.obj K),
          IsIso α

/-- A perfect complex already supplies local strictly perfect models in the localized derived
categories. -/
private theorem hasLocalStrictlyPerfectDerivedModels_of_isPerfectComplex
    (K : Cpx) (hK : RingedSite.CochainComplex.IsPerfect K) :
    HasLocalStrictlyPerfectDerivedModels K := by
  intro U
  rcases hK U with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro I
  rcases hT I with ⟨E', α, hE', hα⟩
  let res := localizedRestriction X I.Y
  let eK :
      DerivedCategory.Q.obj ((res.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
        (j[I.Y]⁻¹).obj (DerivedCategory.Q.obj K) :=
    (res.mapDerivedCategoryFactors.app K).symm
  let _ : QuasiIso α := hα
  let _ : IsIso eK.hom := by infer_instance
  have hcomp : IsIso (DerivedCategory.Q.map α ≫ eK.hom) := by infer_instance
  exact ⟨E', hE', DerivedCategory.Q.map α ≫ eK.hom, hcomp⟩

/-- Local derived strictly perfect models transport across a chosen isomorphism between
representatives in the derived category. -/
private theorem hasLocalStrictlyPerfectDerivedModels_transport
    {K F : Cpx} (eKF : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj F)
    (hF : HasLocalStrictlyPerfectDerivedModels F) :
    HasLocalStrictlyPerfectDerivedModels K := by
  intro U
  rcases hF U with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro I
  rcases hT I with ⟨E', hE', α, hα⟩
  let eI := (j[I.Y]⁻¹).mapIso eKF.symm
  let _ : IsIso α := hα
  let _ : IsIso eI.hom := by infer_instance
  have hcomp : IsIso (α ≫ eI.hom) := by infer_instance
  exact ⟨E', hE', α ≫ eI.hom, hcomp⟩

/-- Local derived strictly perfect models can be refined to the quasi-isomorphic chain-level local
models required by `RingedSite.CochainComplex.IsPerfect`. -/
private theorem cochainComplex_isPerfect_of_hasLocalStrictlyPerfectDerivedModels
    (K : Cpx) (hK : HasLocalStrictlyPerfectDerivedModels K) :
    RingedSite.CochainComplex.IsPerfect K := by
  -- TODO: for each localized derived model, use Lemma 21.44.8 to represent the derived
  -- isomorphism by a local chain map after refining the cover, then use Lemma 21.44.4 to keep the
  -- strictly perfect source strictly perfect on the refined cover.
  sorry

/-- A cover of a final object carrying local derived strictly perfect models induces local derived
strictly perfect models on every object of the site. -/
private theorem hasLocalStrictlyPerfectDerivedModels_of_cover_on_finalObject
    (E : DMod) (K : Cpx) (U : X) (hU : IsTerminal U)
    (e : DerivedCategory.Q.obj K ≅ E)
    (hcover :
      ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
          IsStrictlyPerfect E' ∧
            ∃ α : DerivedCategory.Q.obj E' ⟶ (j[I.Y]⁻¹).obj E,
              IsIso α) :
    HasLocalStrictlyPerfectDerivedModels K := by
  rcases hcover with ⟨T, hT⟩
  intro V
  refine ⟨T.pullback (hU.from V), ?_⟩
  intro I
  rcases hT I.base with ⟨E', hE', α, hα⟩
  let eI := (j[I.Y]⁻¹).mapIso e.symm
  let _ : IsIso α := hα
  let _ : IsIso eI.hom := by infer_instance
  have hcomp : IsIso (α ≫ eI.hom) := by infer_instance
  exact ⟨E', hE', α ≫ eI.hom, hcomp⟩

-- Proof sketch: because `U` is final, any object of the site admits a cover obtained by pulling
-- back the chosen cover of `U`. The given strictly perfect local models on that cover then yield
-- the local strictly perfect representatives required by `DerivedCategory.IsPerfect`.
/-- Lemma 21.47.2 (1): if a derived `𝒪_X`-module becomes, on a covering of a final object,
isomorphic in the localized derived categories to strictly perfect complexes, then it is perfect.
-/
@[stacks 08G6]
theorem isPerfect_of_exists_cover_on_finalObject
    (E : DMod) (U : X) (hU : IsTerminal U)
    (hcover :
      ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        ∃ E' : CochainComplex (ModLoc I.Y) ℤ,
          IsStrictlyPerfect E' ∧
            ∃ α : DerivedCategory.Q.obj E' ⟶ (j[I.Y]⁻¹).obj E,
              IsIso α) :
    E.IsPerfect := by
  let K : Cpx := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hModels : HasLocalStrictlyPerfectDerivedModels K := by
    exact hasLocalStrictlyPerfectDerivedModels_of_cover_on_finalObject E K U hU e hcover
  have hK : RingedSite.CochainComplex.IsPerfect K := by
    exact cochainComplex_isPerfect_of_hasLocalStrictlyPerfectDerivedModels K hModels
  exact of_iso_q_obj e.symm hK

namespace _root_.RingedSite.Hom.ModuleDerived

open _root_.RingedSite.DerivedCategory

-- Proof sketch: use `exists_perfect_representative` to choose one perfect representative of `E`.
-- Any other complex representing `E` is isomorphic to that representative in the derived
-- category, so the local strictly perfect models transport across the representing isomorphism.
/-- Lemma 21.47.2 (2): if `E` is perfect, then every complex representing `E` is perfect. -/
@[stacks 08G6]
theorem IsPerfect.of_representation
    {E : DMod} {K : Cpx} (hE : E.IsPerfect)
    (e : DerivedCategory.Q.obj K ≅ E) :
    RingedSite.CochainComplex.IsPerfect K := by
  rcases exists_perfect_representative hE with ⟨F, eF, hF⟩
  let eKF : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj F := e ≪≫ eF
  have hModelsK : HasLocalStrictlyPerfectDerivedModels K := by
    have hLocalF : HasLocalStrictlyPerfectDerivedModels F := by
      exact hasLocalStrictlyPerfectDerivedModels_of_isPerfectComplex F hF
    exact hasLocalStrictlyPerfectDerivedModels_transport eKF hLocalF
  exact cochainComplex_isPerfect_of_hasLocalStrictlyPerfectDerivedModels K hModelsK

end _root_.RingedSite.Hom.ModuleDerived

end

end RingedSite.DerivedCategory
