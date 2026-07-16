import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.«18_44_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Presheaf.SubmonoidPresheaf
open scoped LocalizedPresheaf

noncomputable section

universe u

namespace LocalizedPresheaf

/- Textbook notation for the sheafification of a commutative-ring-valued presheaf on
`Opens.grothendieckTopology X`. -/
set_option quotPrecheck false in
scoped macro:max 𝒪:term noWs "^#[" J:term "]" : term => do
  `((CategoryTheory.presheafToSheaf $J CommRingCat).obj $𝒪)

end LocalizedPresheaf

namespace TopCat.Presheaf
namespace SubmonoidPresheaf

/- Domain-style sampling for Lemma 17.27.1:
- primary domain: localization of commutative-ring-valued presheaves on a topological space and
  the sheafification of that localization;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizationPresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.SectionsMapToUnits`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.existsUnique_localizationPresheafLift`,
  `CategoryTheory.toSheafify`,
  `(presheafToSheaf J CommRingCat.{u}).map`,
  `(presheafToSheaf J CommRingCat.{u}).obj`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- best owner abstraction: the presheaf localization owner is the site-level
  `CategoryTheory.Presheaf.SubmonoidPresheaf`, with `X.Presheaf` as its topological-space
  specialization; the sheafified localization statements are recalled as the direct specialization
  of the site-level owner API from `Chap18.Lemma_18_44_1`; the
  source-side bridge from a presheaf to its sheafification is carried by `toSheafify J 𝒪`;
- primitive data: a presheaf `𝒪 : X.Presheaf CommRingCat` and a multiplicative subpresheaf
  `𝒮 : CategoryTheory.Presheaf.SubmonoidPresheaf 𝒪`;
- derived API: pointwise unit statements for the canonical localization maps, the presheaf and
  sheaf universal properties, and the stalk-localization comparisons.

Source/core/bridge triage:
- `source-facing`: the objectwise localization presheaf `𝒮.localizationPresheaf`, the presheaf
  universal property, and the resulting stalk-localization statements;
- `core/canonical`: the topological presheaf-localization owner above, together with the
  site-level owner `CategoryTheory.Presheaf.SubmonoidPresheaf`, `toSheafify J 𝒪`, and the
  sheafification functor `(presheafToSheaf J CommRingCat).obj`, plus the sheafified localization
  owner declarations from `CategoryTheory.Presheaf.SubmonoidPresheaf`;
- `bridge/view`: the direct bridge condition
  `SectionsMapToUnits 𝒮 (toSheafify J 𝒪 ≫ η.hom)` for maps out of
  `𝒪^#[J]`, and the stalk comparison for the sheafified localization.

This file therefore keeps the topological presheaf-localization owner, recalls the sheafified
universal-property owner from Chapter 18, and only adds the topological presheaf-to-sheafification
bridge needed for the stalk statement. -/

variable {X : TopCat.{u}}

local notation "J" => Opens.grothendieckTopology X

variable {𝒪 : X.Presheaf CommRingCat.{u}} (𝒮 : CategoryTheory.Presheaf.SubmonoidPresheaf 𝒪)

set_option quotPrecheck false in
set_option linter.unusedVariables false in

/-- The multiplicative subset of the stalk consisting of germs of sections belonging to `𝒮`. -/
def stalkSubmonoid (x : X) : Submonoid (𝒪.stalk x) where
  carrier := { z | ∃ (U : Opens X) (hx : x ∈ U) (s : 𝒮.obj (op U)), (𝒪.germ U x hx).hom s.1 = z }
  one_mem' := by
    refine ⟨⊤, by simp, 1, ?_⟩
    simp
  mul_mem' := by
    rintro a b ⟨U, hxU, sU, rfl⟩ ⟨V, hxV, sV, rfl⟩
    let W : Opens X := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    have hsU :
        ((𝒪.map (homOfLE inf_le_left).op).hom sU.1) ∈ 𝒮.obj (op W) :=
      (𝒮.map (homOfLE inf_le_left).op) sU.2
    have hsV :
        ((𝒪.map (homOfLE inf_le_right).op).hom sV.1) ∈ 𝒮.obj (op W) :=
      (𝒮.map (homOfLE inf_le_right).op) sV.2
    refine ⟨W, hxW, ⟨_, (𝒮.obj (op W)).mul_mem hsU hsV⟩, ?_⟩
    change
      (𝒪.germ W x hxW).hom
          (((𝒪.map (homOfLE inf_le_left).op).hom sU.1) *
            ((𝒪.map (homOfLE inf_le_right).op).hom sV.1)) =
        (𝒪.germ U x hxU).hom sU.1 * (𝒪.germ V x hxV).hom sV.1
    rw [map_mul]
    rw [show (𝒪.germ W x hxW).hom ((𝒪.map (homOfLE inf_le_left).op).hom sU.1) =
        (𝒪.germ U x hxU).hom sU.1 by
          simpa [W] using 𝒪.germ_res_apply (homOfLE inf_le_left) x hxW sU.1]
    rw [show (𝒪.germ W x hxW).hom ((𝒪.map (homOfLE inf_le_right).op).hom sV.1) =
        (𝒪.germ V x hxV).hom sV.1 by
          simpa [W] using 𝒪.germ_res_apply (homOfLE inf_le_right) x hxW sV.1]

-- Proof sketch: the canonical localization map sends each `s ∈ 𝒮(U)` to a unit in
-- `Localization (𝒮(U))`.
/-- The localized stalk is naturally an algebra over the original stalk. -/
noncomputable instance localizedStalkAlgebra (x : X) :
    Algebra (𝒪.stalk x)
      ((stalkFunctor CommRingCat x).obj
        (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) :=
  RingHom.toAlgebra (((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom)

/- The canonical localization morphism sends every distinguished section of `𝒮` to a unit. -/
recall toLocalizationPresheaf_sectionsMapToUnits

/- Lemma 17.27.1 recalls the presheaf-level universal property from the site-level owner
`CategoryTheory.Presheaf.SubmonoidPresheaf`. -/
recall existsUnique_localizationPresheafLift

/-- Helper for Lemma 17.27.1: every germ coming from the stalk submonoid maps to a unit in the
localized stalk. -/
lemma stalkSubmonoid_maps_to_units (x : X) (z : stalkSubmonoid 𝒮 x) :
    IsUnit
      ((((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) z.1) := by
  let F : X.Presheaf CommRingCat.{u} :=
    show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf
  rcases z.2 with ⟨U, hxU, sU, hz⟩
  -- Push the chosen germ through the stalk map so that the objectwise localization theorem applies.
  rw [← hz]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU 𝒮.toLocalizationPresheaf sU.1]
  exact IsUnit.map ((F.germ U x hxU).hom)
    (toLocalizationPresheaf_sectionsMapToUnits (𝒮 := 𝒮) sU)

/-- Helper for Lemma 17.27.1: every element of the localized stalk clears one denominator coming
from the stalk submonoid. -/
lemma localized_stalk_clears_denominator (x : X)
    (t :
      ((stalkFunctor CommRingCat x).obj
        (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf))) :
    ∃ a : 𝒪.stalk x, ∃ s : stalkSubmonoid 𝒮 x,
      t * ((((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) s.1) =
        (((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) a := by
  let F : X.Presheaf CommRingCat.{u} :=
    show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf
  obtain ⟨U, hxU, z, rfl⟩ := TopCat.Presheaf.germ_exist 𝒮.localizationPresheaf x t
  obtain ⟨⟨aU, sU⟩, hz⟩ := IsLocalization.surj (𝒮.obj (op U)) z
  refine ⟨(𝒪.germ U x hxU).hom aU, ⟨(𝒪.germ U x hxU).hom sU.1, ⟨U, hxU, sU, rfl⟩⟩, ?_⟩
  -- Realize the stalk identity by mapping the objectwise denominator-clearing equation to the germ.
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU 𝒮.toLocalizationPresheaf sU.1]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU 𝒮.toLocalizationPresheaf aU]
  change
    (F.germ U x hxU).hom z *
        (F.germ U x hxU).hom
          (((𝒮.toLocalizationPresheaf.app (op U)).hom) sU.1) =
      (F.germ U x hxU).hom
        (((𝒮.toLocalizationPresheaf.app (op U)).hom) aU)
  rw [← map_mul]
  exact congrArg (fun y ↦ (F.germ U x hxU).hom y) hz

/-- Helper for Lemma 17.27.1: equality of two stalk images in the localized stalk can be cleared
by one denominator from the stalk submonoid. -/
lemma localized_stalk_map_eq_iff_exists (x : X) (a b : 𝒪.stalk x)
    (h :
      (((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) a =
        (((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) b) :
    ∃ s : stalkSubmonoid 𝒮 x, s.1 * a = s.1 * b := by
  obtain ⟨U, hxU, aU, rfl⟩ := TopCat.Presheaf.germ_exist 𝒪 x a
  obtain ⟨V, hxV, bV, rfl⟩ := TopCat.Presheaf.germ_exist 𝒪 x b
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU 𝒮.toLocalizationPresheaf aU,
    TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV 𝒮.toLocalizationPresheaf bV] at h
  -- Shrink to one neighborhood where the two localized representatives already agree.
  obtain ⟨W, hxW, iWU, iWV, hW⟩ := TopCat.Presheaf.germ_eq 𝒮.localizationPresheaf x hxU hxV
    (((𝒮.toLocalizationPresheaf.app (op U)).hom) aU)
    (((𝒮.toLocalizationPresheaf.app (op V)).hom) bV) h
  have hW' :
      (((𝒮.toLocalizationPresheaf.app (op W)).hom) (((𝒪.map iWU.op).hom) aU)) =
        (((𝒮.toLocalizationPresheaf.app (op W)).hom) (((𝒪.map iWV.op).hom) bV)) := by
    simpa using hW
  change
    (algebraMap (𝒪.obj (op W)) (𝒮.localizationPresheaf.obj (op W)))
        (((𝒪.map iWU.op).hom) aU) =
      (algebraMap (𝒪.obj (op W)) (𝒮.localizationPresheaf.obj (op W)))
        (((𝒪.map iWV.op).hom) bV) at hW'
  rw [IsLocalization.eq_iff_exists (𝒮.obj (op W)) (𝒮.localizationPresheaf.obj (op W))] at hW'
  rcases hW' with ⟨sW, hsW⟩
  refine ⟨⟨(𝒪.germ W x hxW).hom sW.1, ⟨W, hxW, sW, rfl⟩⟩, ?_⟩
  -- Move both stalk elements onto the common neighborhood and then use the cleared objectwise
  -- equality there.
  rw [show (𝒪.germ U x hxU).hom aU =
      (𝒪.germ W x hxW).hom (((𝒪.map iWU.op).hom) aU) by
        simpa using (𝒪.germ_res_apply iWU x hxW aU).symm]
  rw [show (𝒪.germ V x hxV).hom bV =
      (𝒪.germ W x hxW).hom (((𝒪.map iWV.op).hom) bV) by
        simpa using (𝒪.germ_res_apply iWV x hxW bV).symm]
  rw [← map_mul, ← map_mul]
  exact congrArg (fun y ↦ (𝒪.germ W x hxW).hom y) hsW

-- Proof sketch: stalks commute with the filtered colimit defining the stalk, and objectwise
-- localization commutes with this colimit, so the induced stalk map is the localization at the
-- submonoid of germs of sections from `𝒮`.
/-- The canonical map on stalks identifies the stalk of `𝒮⁻¹𝒪` as the localization of `𝒪_x` at the
induced multiplicative subset `𝒮_x`. -/
theorem localizedPresheaf_stalk_isLocalization (x : X) :
    IsLocalization (stalkSubmonoid 𝒮 x)
      ((stalkFunctor CommRingCat x).obj
        (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) := by
  let M := stalkSubmonoid 𝒮 x
  let f :
      Localization M →+*
        ((stalkFunctor CommRingCat x).obj
          (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) :=
    IsLocalization.lift
      (fun z ↦ stalkSubmonoid_maps_to_units (𝒮 := 𝒮) x z)
  have hf_surj : Function.Surjective f := by
    -- Surjectivity is exactly the denominator-clearing statement proved above.
    rw [IsLocalization.lift_surjective_iff]
    intro t
    obtain ⟨a, s, hs⟩ := localized_stalk_clears_denominator (𝒮 := 𝒮) x t
    exact ⟨⟨a, s⟩, hs⟩
  have hf_inj : Function.Injective f := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro hab
      calc
        (((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) a =
            f (algebraMap (𝒪.stalk x) (Localization M) a) := by
              symm
              exact IsLocalization.lift_eq
                (fun z ↦ stalkSubmonoid_maps_to_units (𝒮 := 𝒮) x z) a
        _ = f (algebraMap (𝒪.stalk x) (Localization M) b) := congrArg f hab
        _ = (((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) b := by
              exact IsLocalization.lift_eq
                (fun z ↦ stalkSubmonoid_maps_to_units (𝒮 := 𝒮) x z) b
    · intro hab
      rw [IsLocalization.eq_iff_exists M (Localization M)]
      exact localized_stalk_map_eq_iff_exists (𝒮 := 𝒮) x a b hab
  -- Transport the standard localization owner on `Localization M` across the bijective algebra map.
  let eRing :
      Localization M ≃+*
        ((stalkFunctor CommRingCat x).obj
          (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) :=
    RingEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let e :
      Localization M ≃ₐ[𝒪.stalk x]
        ((stalkFunctor CommRingCat x).obj
          (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) :=
    { toRingEquiv := eRing
      commutes' := by
        intro r
        simpa [eRing] using IsLocalization.lift_eq
          (fun z ↦ stalkSubmonoid_maps_to_units (𝒮 := 𝒮) x z) r }
  exact IsLocalization.isLocalization_of_algEquiv M e

/-- The stalk of the sheafified localization is naturally an algebra over `𝒪_x`. -/
noncomputable instance sheafifiedLocalizationPresheafStalkAlgebra (x : X)
    [HasWeakSheafify J CommRingCat.{u}] :
    Algebra (𝒪.stalk x)
      ↑(TopCat.Presheaf.stalk (((𝒮⁻¹ 𝒪)^#[J]).obj) x) :=
  RingHom.toAlgebra
    (((stalkFunctor CommRingCat x).map
        (CategoryTheory.toSheafify J 𝒪 ≫
          ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom)).hom)

/- Lemma 17.27.1 is the specialization to `Opens.grothendieckTopology X` of the canonical
sheafified-localization owner API from Chapter 18. The only extra topological bridge is the direct
condition
`SectionsMapToUnits 𝒮 (toSheafify J 𝒪 ≫ η.hom)` recording how a map out of `𝒪^#[J]` pulls back
along `𝒪 ⟶ 𝒪^#[J]`. -/

/-- Helper for Lemma 17.27.1: evaluating `toSheafify_naturality` on a distinguished section of
`𝒮` rewrites the composite map into the sheafified localization as the sheafification-unit map on
the localized section itself. -/
lemma toSheafify_localization_eval [HasWeakSheafify J CommRingCat.{u}]
    {U : (Opens X)ᵒᵖ} (a : 𝒪.obj U) :
    (((CategoryTheory.toSheafify J 𝒪 ≫
        ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom).app U).hom) a =
      (((CategoryTheory.toSheafify J 𝒮.localizationPresheaf).app U).hom)
        (((𝒮.toLocalizationPresheaf.app U).hom) a) := by
  -- Rewrite the evaluated section by the sheafification-unit naturality square.
  rw [← CategoryTheory.toSheafify_naturality J 𝒮.toLocalizationPresheaf]
  rfl

/-- Helper for Lemma 17.27.1: evaluating `toSheafify_naturality` on a distinguished section of
`𝒮` rewrites the composite map into the sheafified localization as the sheafification-unit map on
the localized section itself. -/
lemma toSheafify_localization_section_eval [HasWeakSheafify J CommRingCat.{u}]
    {U : (Opens X)ᵒᵖ} (s : 𝒮.obj U) :
    (((CategoryTheory.toSheafify J 𝒪 ≫
        ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom).app U).hom) s.1 =
      (((CategoryTheory.toSheafify J 𝒮.localizationPresheaf).app U).hom)
        (((𝒮.toLocalizationPresheaf.app U).hom) s.1) := by
  -- Evaluate the app-level naturality identity on the chosen section.
  simpa using toSheafify_localization_eval (𝒮 := 𝒮) (U := U) s.1

/-- The canonical sheaf morphism `𝒪^#[J] ⟶ (𝒮⁻¹𝒪)^#[J]` sends every distinguished section of
`𝒮` to a unit after pulling back along `𝒪 ⟶ 𝒪^#[J]`. -/
theorem sheafifiedLocalizationPresheaf_sectionsMapToUnits [HasWeakSheafify J CommRingCat.{u}] :
    SectionsMapToUnits 𝒮
      (CategoryTheory.toSheafify J 𝒪 ≫
        ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom) := by
  intro U s
  -- Route correction: expose the sectionwise naturality rewrite before using the objectwise
  -- localization-unit statement.
  rw [toSheafify_localization_section_eval (𝒮 := 𝒮) s]
  -- The canonical localized section is already a unit before sheafification, so its image stays
  -- a unit in the sheafified ring of sections.
  exact IsUnit.map ((CategoryTheory.toSheafify J 𝒮.localizationPresheaf).app U).hom
    (toLocalizationPresheaf_sectionsMapToUnits (𝒮 := 𝒮) s)

/-- Lemma 17.27.1, sheafified universal property in topological form: any sheaf morphism out of
`𝒪^#[J]` whose pullback along `𝒪 ⟶ 𝒪^#[J]` inverts `𝒮` factors uniquely through
`𝒪^#[J] ⟶ (𝒮⁻¹𝒪)^#[J]`. -/
theorem existsUnique_sheafifiedLocalizationPresheafLift [HasWeakSheafify J CommRingCat.{u}]
    {𝒜 : X.Sheaf CommRingCat.{u}}
    (η : 𝒪^#[J] ⟶ 𝒜)
    (hη : SectionsMapToUnits 𝒮 (CategoryTheory.toSheafify J 𝒪 ≫ η.hom)) :
    ∃! γ : ((𝒮⁻¹ 𝒪)^#[J]) ⟶ 𝒜,
      (presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf ≫ γ = η := by
  obtain ⟨δ, hδ, hδ_unique⟩ :=
    existsUnique_localizationPresheafLift (𝒮 := 𝒮)
      (η := CategoryTheory.toSheafify J 𝒪 ≫ η.hom) hη
  refine ⟨⟨CategoryTheory.sheafifyLift J δ 𝒜.property⟩, ?_, ?_⟩
  · -- The presheaf factorization sheafifies to the desired sheaf factorization.
    ext U x
    have hcomp :
        CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫
            CategoryTheory.sheafifyLift J δ 𝒜.property =
          η.hom := by
      have hsheafify :
          CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫
              CategoryTheory.sheafifyLift J δ 𝒜.property =
            CategoryTheory.sheafifyLift J
              (CategoryTheory.toSheafify J 𝒪 ≫ η.hom) 𝒜.property := by
        apply CategoryTheory.sheafifyLift_unique J
          (CategoryTheory.toSheafify J 𝒪 ≫ η.hom) 𝒜.property
        have hnat :
            𝒮.toLocalizationPresheaf ≫
                CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫
                  CategoryTheory.sheafifyLift J δ 𝒜.property =
              CategoryTheory.toSheafify J 𝒪 ≫
                CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫
                  CategoryTheory.sheafifyLift J δ 𝒜.property := by
          simpa [Category.assoc] using congrArg
            (fun f : 𝒪 ⟶ ((presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf).obj ↦
              f ≫ CategoryTheory.sheafifyLift J δ 𝒜.property)
            (CategoryTheory.toSheafify_naturality J 𝒮.toLocalizationPresheaf)
        calc
          CategoryTheory.toSheafify J 𝒪 ≫
              (CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫
                CategoryTheory.sheafifyLift J δ 𝒜.property) =
            CategoryTheory.toSheafify J 𝒪 ≫
              CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫
                CategoryTheory.sheafifyLift J δ 𝒜.property := by
                  simp
          _ = 𝒮.toLocalizationPresheaf ≫
                CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫
                  CategoryTheory.sheafifyLift J δ 𝒜.property := by
                exact hnat.symm
          _ = 𝒮.toLocalizationPresheaf ≫ δ := by
                rw [CategoryTheory.toSheafify_sheafifyLift]
          _ = CategoryTheory.toSheafify J 𝒪 ≫ η.hom := hδ
      have hη_lift :
          η.hom =
            CategoryTheory.sheafifyLift J
              (CategoryTheory.toSheafify J 𝒪 ≫ η.hom) 𝒜.property := by
        exact CategoryTheory.sheafifyLift_unique J
          (CategoryTheory.toSheafify J 𝒪 ≫ η.hom) 𝒜.property η.hom rfl
      exact hsheafify.trans hη_lift.symm
    simpa [CategoryTheory.sheafifyMap] using congrArg (fun f ↦ ((f.app U).hom) x) hcomp
  · intro γ hγ
    ext U x
    have hγ_hom :
        ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom ≫ γ.hom = η.hom := by
      exact congrArg (fun f ↦ f.1) hγ
    have hδγ :
        CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫ γ.hom = δ := by
      apply hδ_unique
      have hnat :
          𝒮.toLocalizationPresheaf ≫
              CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫ γ.hom =
            CategoryTheory.toSheafify J 𝒪 ≫
              CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫ γ.hom := by
        simpa [Category.assoc] using congrArg
          (fun f : 𝒪 ⟶ ((presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf).obj ↦
            f ≫ γ.hom)
          (CategoryTheory.toSheafify_naturality J 𝒮.toLocalizationPresheaf)
      calc
        𝒮.toLocalizationPresheaf ≫
            CategoryTheory.toSheafify J 𝒮.localizationPresheaf ≫ γ.hom =
          CategoryTheory.toSheafify J 𝒪 ≫
            CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫ γ.hom := hnat
        _ = CategoryTheory.toSheafify J 𝒪 ≫ η.hom := by
              have hγ_hom' :
                  CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫ γ.hom = η.hom := by
                simpa [CategoryTheory.sheafifyMap] using hγ_hom
              calc
                CategoryTheory.toSheafify J 𝒪 ≫
                    CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫ γ.hom =
                  CategoryTheory.toSheafify J 𝒪 ≫
                    (CategoryTheory.sheafifyMap J 𝒮.toLocalizationPresheaf ≫ γ.hom) := by
                      simp
                _ = CategoryTheory.toSheafify J 𝒪 ≫ η.hom := by rw [hγ_hom']
    have hγ_eq : γ.hom = CategoryTheory.sheafifyLift J δ 𝒜.property := by
      exact CategoryTheory.sheafifyLift_unique J δ 𝒜.property γ.hom hδγ
    exact congrArg (fun f ↦ ((f.app U).hom) x) hγ_eq

/-- Helper for Lemma 17.27.1: the stalk of the presheaf localization and the stalk of its
sheafification are canonically isomorphic. -/
noncomputable def sheafified_localization_stalk_iso [HasWeakSheafify J CommRingCat.{u}] (x : X) :
    ((stalkFunctor CommRingCat x).obj
      (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) ≅
      ((stalkFunctor CommRingCat x).obj
        (show X.Presheaf CommRingCat.{u} from (((𝒮⁻¹ 𝒪)^#[J]).obj))) :=
  @asIso _ _ _ _
    ((stalkFunctor CommRingCat x).map
      (CategoryTheory.toSheafify J 𝒮.localizationPresheaf))
    (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat
      𝒮.localizationPresheaf)

/-- Helper for Lemma 17.27.1: the canonical stalk isomorphism intertwines the presheaf-localized
stalk map with the sheafified-localization stalk map from `𝒪_x`. -/
lemma sheafified_localization_stalk_iso_commutes [HasWeakSheafify J CommRingCat.{u}]
    (x : X) (r : 𝒪.stalk x) :
    (sheafified_localization_stalk_iso (𝒮 := 𝒮) x).hom.hom
      ((((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom) r) =
    (((stalkFunctor CommRingCat x).map
      (CategoryTheory.toSheafify J 𝒪 ≫
        ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom)).hom) r := by
  let F : X.Presheaf CommRingCat.{u} :=
    show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf
  obtain ⟨U, hxU, aU, rfl⟩ := TopCat.Presheaf.germ_exist 𝒪 x r
  -- Rewrite both stalk maps on a common germ representative and then use app-level naturality.
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU 𝒮.toLocalizationPresheaf aU]
  change
    (((stalkFunctor CommRingCat x).map
        (CategoryTheory.toSheafify J 𝒮.localizationPresheaf)).hom
      ((F.germ U x hxU).hom
        (((𝒮.toLocalizationPresheaf.app (op U)).hom) aU))) =
      (((stalkFunctor CommRingCat x).map
        (CategoryTheory.toSheafify J 𝒪 ≫
          ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom)).hom)
        ((𝒪.germ U x hxU).hom aU)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    (CategoryTheory.toSheafify J 𝒮.localizationPresheaf)
    (((𝒮.toLocalizationPresheaf.app (op U)).hom) aU)]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    (CategoryTheory.toSheafify J 𝒪 ≫
      ((presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf).hom) aU]
  -- The two section values agree by the sheafification-unit naturality square.
  congr 1
  simpa using (toSheafify_localization_eval (𝒮 := 𝒮) (U := op U) aU).symm

/-- Helper for Lemma 17.27.1: the canonical stalk isomorphism is an algebra equivalence over
`𝒪_x` once the two stalk algebra structures are identified by the naturality rewrite above. -/
noncomputable def sheafified_localization_stalk_algEquiv [HasWeakSheafify J CommRingCat.{u}]
    (x : X) :
    ((stalkFunctor CommRingCat x).obj
      (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) ≃ₐ[𝒪.stalk x]
      ↑(TopCat.Presheaf.stalk (((𝒮⁻¹ 𝒪)^#[J]).obj) x) :=
  { toRingEquiv := (sheafified_localization_stalk_iso (𝒮 := 𝒮) x).commRingCatIsoToRingEquiv
    commutes' := sheafified_localization_stalk_iso_commutes (𝒮 := 𝒮) x }

-- Proof sketch: `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` identifies the stalk of
-- the sheafification of `𝒮⁻¹𝒪` with the stalk of `𝒮⁻¹𝒪`, so the localization description from
-- `localizedPresheaf_stalk_isLocalization` carries over unchanged.
/-- The stalk `((𝒮⁻¹𝒪)^#[J]).obj.stalk x` is again the localization of `𝒪_x` at `𝒮_x`. -/
theorem sheafifiedLocalizationPresheaf_stalk_isLocalization [HasWeakSheafify J CommRingCat.{u}]
    (x : X) :
    IsLocalization (stalkSubmonoid 𝒮 x)
      ↑(TopCat.Presheaf.stalk (((𝒮⁻¹ 𝒪)^#[J]).obj) x) := by
  let M := stalkSubmonoid 𝒮 x
  letI :
      IsLocalization M
        ((stalkFunctor CommRingCat x).obj
          (show X.Presheaf CommRingCat.{u} from 𝒮.localizationPresheaf)) :=
    localizedPresheaf_stalk_isLocalization (𝒮 := 𝒮) x
  -- Route correction: after isolating the stalk-compatibility rewrite, the final step is a
  -- direct transport of the localization owner across the canonical algebra equivalence.
  exact IsLocalization.isLocalization_of_algEquiv M
    (sheafified_localization_stalk_algEquiv (𝒮 := 𝒮) x)

end SubmonoidPresheaf
end TopCat.Presheaf
