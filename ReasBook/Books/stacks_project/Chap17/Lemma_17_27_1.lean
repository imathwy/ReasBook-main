import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Presheaf
namespace SubmonoidPresheaf

/- Domain-style sampling for Lemma 17.27.1:
- primary domain: localization of commutative-ring-valued presheaves on a topological space and
  the sheafification of that localization;
- sampled owner declarations:
  `TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf`,
  `TopCat.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf`,
  `presheafToSheaf`,
  `toSheafify`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- best owner abstraction: the source-facing owner in this file should be the sheafified
  localization morphism `𝒮.toSheafifiedLocalizationPresheaf`, built from the owner pair
  `𝒮.localizationPresheaf` and `𝒮.toLocalizationPresheaf`;
- primitive data: a presheaf `𝒪 : X.Presheaf CommRingCat` and a multiplicative subpresheaf
  `𝒮 : 𝒪.SubmonoidPresheaf`;
- derived API: pointwise unit statements for the canonical localization maps, the presheaf and
  sheaf universal properties, and the stalk-localization comparisons.

Source/core/bridge triage:
- `source-facing`: the sheafified localization owner `𝒮.toSheafifiedLocalizationPresheaf`, its
  universal property among sheaves, and the resulting stalk-localization statement;
- `core/canonical`: `SubmonoidPresheaf.localizationPresheaf`,
  `SubmonoidPresheaf.toLocalizationPresheaf`, `presheafToSheaf`, and `toSheafify`;
- `bridge/view`: the objectwise localization universal property for
  `𝒮.localizationPresheaf` and the induced comparison between the original sections of `𝒮` and
  their images after sheafification.

This file therefore stays on the topological owner `𝒮 : 𝒪.SubmonoidPresheaf`, with the
sheafified localization morphism promoted to the public owner
`𝒮.toSheafifiedLocalizationPresheaf`, together with the derived invertibility predicate
`𝒮.SectionsMapToUnits`. -/

variable {X : TopCat.{u}}

local notation "J" => Opens.grothendieckTopology X

variable {𝒪 : X.Presheaf CommRingCat.{u}} (𝒮 : 𝒪.SubmonoidPresheaf)

namespace LocalizedStructureSheaf

set_option quotPrecheck false in
scoped macro:max 𝒮:term noWs "⁻¹" 𝒪:term : term => do
  let _ := 𝒪
  `(SubmonoidPresheaf.localizationPresheaf $𝒮)

set_option quotPrecheck false in
scoped macro:max 𝒪:term noWs "^#" : term =>
  `((presheafToSheaf J CommRingCat).obj $𝒪)

end LocalizedStructureSheaf

open scoped LocalizedStructureSheaf

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

/-- The localized stalk is naturally an algebra over the original stalk. -/
noncomputable instance localizedStalkAlgebra (x : X) :
    Algebra (𝒪.stalk x) ((𝒮⁻¹ 𝒪).stalk x) :=
  RingHom.toAlgebra (((stalkFunctor CommRingCat x).map 𝒮.toLocalizationPresheaf).hom)

-- Proof sketch: the canonical localization map sends each `s ∈ 𝒮(U)` to a unit in
-- `Localization (𝒮(U))`.
/-- The canonical localization morphism sends every distinguished section of `𝒮` to a unit. -/
theorem toLocalizationPresheaf_sectionsMapToUnits {U : (Opens X)ᵒᵖ} (s : 𝒮.obj U) :
    IsUnit ((𝒮.toLocalizationPresheaf.app U).hom s.1) := by
  change IsUnit ((algebraMap (𝒪.obj U) ((𝒮⁻¹ 𝒪).obj U)) s.1)
  simpa using IsLocalization.map_units ((𝒮⁻¹ 𝒪).obj U) s

-- Proof sketch: objectwise localization is initial among maps that invert `𝒮(U)`, and the
-- componentwise factorization is natural by uniqueness.
/-- Bridge: the objectwise localization presheaf `𝒮⁻¹𝒪` is initial among presheaves of
commutative rings under `𝒪` in which every local section from `𝒮` becomes invertible. -/
theorem localizedPresheaf_is_universal {𝒜 : X.Presheaf CommRingCat.{u}} (η : 𝒪 ⟶ 𝒜)
    (hη : ∀ ⦃U : (Opens X)ᵒᵖ⦄ (s : 𝒮.obj U), IsUnit ((η.app U).hom s.1)) :
    ∃! γ : (𝒮⁻¹ 𝒪) ⟶ 𝒜, 𝒮.toLocalizationPresheaf ≫ γ = η := sorry

-- Proof sketch: stalks commute with the filtered colimit defining the stalk, and objectwise
-- localization commutes with this colimit, so the induced stalk map is the localization at the
-- submonoid of germs of sections from `𝒮`.
/-- The canonical map on stalks identifies the stalk of `𝒮⁻¹𝒪` as the localization of `𝒪_x` at the
induced multiplicative subset `𝒮_x`. -/
theorem localizedPresheaf_stalk_isLocalization (x : X) :
    IsLocalization (𝒮.stalkSubmonoid x) ((𝒮⁻¹ 𝒪).stalk x) := sorry

/-- The canonical morphism from `𝒪^#` to `(𝒮⁻¹𝒪)^#`. -/
noncomputable def toSheafifiedLocalizationPresheaf [HasWeakSheafify J CommRingCat.{u}] :
    𝒪^# ⟶ (𝒮⁻¹ 𝒪)^# :=
  (presheafToSheaf J CommRingCat.{u}).map 𝒮.toLocalizationPresheaf

/-- A morphism out of `𝒪^#` sends the distinguished sections of `𝒮` to units if this holds
objectwise after precomposing with `toSheafify`. -/
def SectionsMapToUnits (𝒮 : 𝒪.SubmonoidPresheaf) [HasWeakSheafify J CommRingCat.{u}]
    {ℱ : X.Sheaf CommRingCat.{u}} (η : 𝒪^# ⟶ ℱ) : Prop :=
  ∀ ⦃U : (Opens X)ᵒᵖ⦄ (s : 𝒮.obj U),
    IsUnit ((η.hom.app U).hom (((CategoryTheory.toSheafify J 𝒪).app U).hom s.1))

/-- The stalk of the sheafified localization is naturally an algebra over `𝒪_x`. -/
noncomputable instance sheafifiedLocalizationStalkAlgebra [HasWeakSheafify J CommRingCat.{u}]
    (x : X) :
    Algebra (𝒪.stalk x)
      ((stalkFunctor CommRingCat x).obj
        ((𝒮⁻¹ 𝒪)^#).obj) :=
  RingHom.toAlgebra (((stalkFunctor CommRingCat x).map
    (CategoryTheory.toSheafify J 𝒪 ≫ 𝒮.toSheafifiedLocalizationPresheaf.hom)).hom)

-- Proof sketch: sheafification produces a sheaf, and its universal property composed with the
-- presheaf-localization universal property gives the claimed initiality among sheaves.
/-- Lemma 17.27.1: the sheafified localization map
`𝒪^# ⟶ (𝒮⁻¹𝒪)^#`
sends the distinguished sections of `𝒮` to units and is initial among sheaves of commutative
rings under the sheafification of `𝒪` with that property. -/
theorem sheafifiedLocalizationPresheaf_is_universal [HasWeakSheafify J CommRingCat.{u}] :
    𝒮.SectionsMapToUnits 𝒮.toSheafifiedLocalizationPresheaf ∧
      ∀ ⦃ℱ : X.Sheaf CommRingCat.{u}⦄
        (η : 𝒪^# ⟶ ℱ),
        (hη : 𝒮.SectionsMapToUnits η) →
          ∃! γ : ((𝒮⁻¹ 𝒪)^#) ⟶ ℱ,
            𝒮.toSheafifiedLocalizationPresheaf ≫ γ = η := sorry

/-- The canonical sheafified localization morphism sends every distinguished section of `𝒮` to a
unit. -/
theorem toSheafifiedLocalizationPresheaf_sectionsMapToUnits
    [HasWeakSheafify J CommRingCat.{u}] :
    𝒮.SectionsMapToUnits 𝒮.toSheafifiedLocalizationPresheaf :=
  𝒮.sheafifiedLocalizationPresheaf_is_universal.1

-- Proof sketch: `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` identifies the stalk of
-- the sheafification of `𝒮⁻¹𝒪` with the stalk of `𝒮⁻¹𝒪`, so the localization description from
-- `localizedPresheaf_stalk_isLocalization` carries over unchanged.
/-- The stalk of the sheafified localization is again the localization of `𝒪_x` at `𝒮_x`. -/
theorem sheafifiedLocalizationPresheaf_stalk_isLocalization [HasWeakSheafify J CommRingCat.{u}]
    (x : X) :
    IsLocalization (𝒮.stalkSubmonoid x)
      ((stalkFunctor CommRingCat x).obj
        ((𝒮⁻¹ 𝒪)^#).obj) := sorry

end SubmonoidPresheaf
end TopCat.Presheaf
