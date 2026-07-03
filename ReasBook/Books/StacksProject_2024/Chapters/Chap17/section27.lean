import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_27_1 (from Chap17) -/
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

/-! ### Lemma_17_27_2 (from Chap17) -/
open CategoryTheory Opposite TopologicalSpace
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace TopCat.Presheaf
namespace SubmonoidPresheaf

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.27.2:
- primary domain: localization of module-valued presheaves over a commutative-ring-valued
  presheaf, together with the sheafification of the resulting tensor description;
- sampled owner declarations:
  `SubmonoidPresheaf.localizationPresheaf`,
  `ringPresheaf`,
  `LocalizedModule.map`,
  `LocalizedModule.equivTensorProduct`,
  `PresheafOfModules.Monoidal.tensorObj`,
  `moduleSheafificationTensorIso`;
- best owner abstraction: the source-facing owner is the localized module presheaf
  `𝒮⁻¹ℱ : PresheafOfModules (ringPresheaf (𝒮.localizationPresheaf))`, whose sections are the
  localized modules `LocalizedModule (𝒮(U)) (ℱ(U))`; the restricted-scalars `𝒪`-linear view and
  the tensor description over `𝒪` are bridge constructions derived from that owner;
- primitive data: a presheaf of commutative rings `𝒪`, a multiplicative subpresheaf
  `𝒮 : 𝒪.SubmonoidPresheaf`, and a presheaf of `𝒪`-modules `ℱ`;
- derived API: the localized ring module presheaf over `𝒪`, the localized module presheaf
  `𝒮⁻¹ℱ`, its `𝒪`-linear bridge `𝒮.localizedModulePresheafOverBase ℱ`, the tensor bridge
  `𝒮.localizedModulePresheafOverBaseIsoTensor ℱ`, the sheafified localized module over the
  sheafification of `𝒮.localizationPresheaf`, and its `𝒪`-linear tensor comparison.

Source/core/bridge triage:
- `source-facing`: the presheaf-level owner `𝒮⁻¹ℱ` over `𝒮.localizationPresheaf` and its
  sheafification over the sheafification of `𝒮.localizationPresheaf`;
- `core/canonical`: the localized ring presheaf owner `𝒮.localizationPresheaf`, the presheaf
  tensor owner `PresheafOfModules.Monoidal.tensorObj`, and the sheafified tensor owner
  `moduleSheafificationTensorIso`;
- `bridge/view`: the `𝒪`-linear restricted-scalars presheaf
  `𝒮.localizedModulePresheafOverBase ℱ`, the presheaf isomorphism
  `𝒮.localizedModulePresheafOverBaseIsoTensor ℱ`, and the corresponding
  `𝒪`-linear sheafified bridge.

This item therefore keeps the Stacks lemma at the presheaf/sheaf level: the localized module
presheaf is owned here by the sectionwise localization construction `𝒮⁻¹ℱ` over the localized
ring presheaf, while the generic tensor presentation over `𝒪` is retained only as the canonical
bridge needed to support the source-facing comparison. -/

variable {𝒪 : X.Presheaf CommRingCat.{u}} (𝒮 : 𝒪.SubmonoidPresheaf)

local notation "J" => Opens.grothendieckTopology X

/-- The localization presheaf `𝒮⁻¹𝒪`, viewed by restriction of scalars as a presheaf of
`\mathcal O_X`-modules. -/
noncomputable abbrev localizedRingModulePresheaf :
    PresheafOfModules (ringPresheaf 𝒪) :=
    (PresheafOfModules.restrictScalars
      (Functor.whiskerRight 𝒮.toLocalizationPresheaf (forget₂ CommRingCat RingCat))).obj
    (PresheafOfModules.unit (ringPresheaf (𝒮.localizationPresheaf)))

private def mapSection
    (𝒮 : 𝒪.SubmonoidPresheaf)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    𝒮.obj U → 𝒮.obj V :=
  fun s ↦ ⟨(𝒪.map i).hom s.1, 𝒮.map i s.2⟩

local instance localizedModuleModule
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (U : (Opens X)ᵒᵖ) :
    Module (𝒮.localizationPresheaf.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) :=
  LocalizedModule.moduleOfIsLocalization

private noncomputable def localizedModuleMapFun
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    LocalizedModule (𝒮.obj U) (ℱ.obj U) →
      ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
        (ModuleCat.of (𝒮.localizationPresheaf.obj V) (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) :=
  fun x ↦
    x.liftOn
      (fun q ↦
        (LocalizedModule.mk (show ℱ.obj V from ℱ.map i q.1) (mapSection 𝒮 i q.2) :
          (ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
            (ModuleCat.of (𝒮.localizationPresheaf.obj V)
              (LocalizedModule (𝒮.obj V) (ℱ.obj V)))))
      (by
        rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨c, hc⟩
        have hmap :
            (show ℱ.obj V from ℱ.map i ((c : 𝒪.obj U) • ((s' : 𝒪.obj U) • m))) =
              (show ℱ.obj V from ℱ.map i ((c : 𝒪.obj U) • ((s : 𝒪.obj U) • m'))) := by
          exact congrArg (fun x ↦ (show ℱ.obj V from ℱ.map i x)) hc
        apply LocalizedModule.mk_eq.mpr
        refine ⟨mapSection 𝒮 i c, ?_⟩
        change (𝒪.map i).hom c.1 • ((𝒪.map i).hom s'.1 • (show ℱ.obj V from ℱ.map i m)) =
            (𝒪.map i).hom c.1 • ((𝒪.map i).hom s.1 • (show ℱ.obj V from ℱ.map i m'))
        calc
          (𝒪.map i).hom c.1 • ((𝒪.map i).hom s'.1 • (show ℱ.obj V from ℱ.map i m)) =
              (𝒪.map i).hom c.1 • (show ℱ.obj V from ℱ.map i ((s' : 𝒪.obj U) • m)) := by
                congr 1
                exact (ℱ.map_smul i (s' : 𝒪.obj U) m).symm
          _ = (show ℱ.obj V from ℱ.map i ((c : 𝒪.obj U) • ((s' : 𝒪.obj U) • m))) := by
                exact (ℱ.map_smul i (c : 𝒪.obj U) ((s' : 𝒪.obj U) • m)).symm
          _ = (show ℱ.obj V from ℱ.map i ((c : 𝒪.obj U) • ((s : 𝒪.obj U) • m'))) := hmap
          _ = (𝒪.map i).hom c.1 • (show ℱ.obj V from ℱ.map i ((s : 𝒪.obj U) • m')) := by
                exact ℱ.map_smul i (c : 𝒪.obj U) ((s : 𝒪.obj U) • m')
          _ = (𝒪.map i).hom c.1 • ((𝒪.map i).hom s.1 • (show ℱ.obj V from ℱ.map i m')) := by
                congr 1
                simpa using (ℱ.map_smul i (s : 𝒪.obj U) m'))

@[simp] private theorem localizedModuleMapFun_mk
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.obj U) (s : 𝒮.obj U) :
    localizedModuleMapFun 𝒮 ℱ i (LocalizedModule.mk m s) =
      (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s) :
        (ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
          (ModuleCat.of (𝒮.localizationPresheaf.obj V)
            (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) := by
  rfl

private theorem localizedModuleMapFun_add
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (x y : LocalizedModule (𝒮.obj U) (ℱ.obj U)) :
    localizedModuleMapFun 𝒮 ℱ i (x + y) =
      localizedModuleMapFun 𝒮 ℱ i x + localizedModuleMapFun 𝒮 ℱ i y := by
  sorry

private theorem localizedModuleMapFun_smul
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (r : 𝒮.localizationPresheaf.obj U) (x : LocalizedModule (𝒮.obj U) (ℱ.obj U)) :
    localizedModuleMapFun 𝒮 ℱ i (r • x) =
      r • localizedModuleMapFun 𝒮 ℱ i x := by
  sorry

private noncomputable def localizedModuleMap
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ModuleCat.of (𝒮.localizationPresheaf.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) ⟶
      ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
        (ModuleCat.of (𝒮.localizationPresheaf.obj V) (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) :=
  let Y :=
    ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
      (ModuleCat.of (𝒮.localizationPresheaf.obj V) (LocalizedModule (𝒮.obj V) (ℱ.obj V))))
  let _ : Module (𝒮.localizationPresheaf.obj U) (LocalizedModule (𝒮.obj V) (ℱ.obj V)) :=
    Y.isModule
  show ModuleCat.of (𝒮.localizationPresheaf.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) ⟶ Y from
    ModuleCat.ofHom <|
      (show LocalizedModule (𝒮.obj U) (ℱ.obj U) →ₗ[𝒮.localizationPresheaf.obj U]
          LocalizedModule (𝒮.obj V) (ℱ.obj V) from
        { toFun := localizedModuleMapFun 𝒮 ℱ i
          map_add' := localizedModuleMapFun_add 𝒮 ℱ i
          map_smul' := localizedModuleMapFun_smul 𝒮 ℱ i })

@[simp] private theorem localizedModuleMap_mk
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.obj U) (s : 𝒮.obj U) :
    localizedModuleMap 𝒮 ℱ i (LocalizedModule.mk m s) =
      (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s) :
        (ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
          (ModuleCat.of (𝒮.localizationPresheaf.obj V)
            (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) := by
  sorry

private theorem localizedModulePresheaf_map_id
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : (Opens X)ᵒᵖ) :
    localizedModuleMap 𝒮 ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (𝒮.localizationPresheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (𝒮.localizationPresheaf.map_id U))).inv.app
        (ModuleCat.of (𝒮.localizationPresheaf.obj U)
          (LocalizedModule (𝒮.obj U) (ℱ.obj U))) := by
  sorry

private theorem localizedModulePresheaf_map_comp
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    localizedModuleMap 𝒮 ℱ (i ≫ j) =
      localizedModuleMap 𝒮 ℱ i ≫
        (ModuleCat.restrictScalars _).map (localizedModuleMap 𝒮 ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (𝒮.localizationPresheaf.map i).hom
            (𝒮.localizationPresheaf.map j).hom
            (𝒮.localizationPresheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| 𝒮.localizationPresheaf.map_comp i j)).inv.app
            (ModuleCat.of (𝒮.localizationPresheaf.obj W)
              (LocalizedModule (𝒮.obj W) (ℱ.obj W))) := by
  sorry

/-- Lemma 17.27.2, presheaf form: the localized module presheaf `𝒮⁻¹ℱ` over the localized ring
presheaf `𝒮⁻¹𝒪`. -/
noncomputable def localizedModulePresheaf
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    PresheafOfModules (ringPresheaf 𝒮.localizationPresheaf) where
  obj U := ModuleCat.of (𝒮.localizationPresheaf.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U))
  map {_ _} i := localizedModuleMap 𝒮 ℱ i
  map_id U := localizedModulePresheaf_map_id 𝒮 ℱ U
  map_comp {_ _ _} i j := localizedModulePresheaf_map_comp 𝒮 ℱ i j

namespace LocalizedModulePresheaf

/- Textbook notation for the localized module presheaf `𝒮⁻¹ℱ`. -/
set_option quotPrecheck false in
scoped macro:max 𝒮:term noWs "⁻¹" ℱ:term : term =>
  `(SubmonoidPresheaf.localizedModulePresheaf $𝒮 $ℱ)

end LocalizedModulePresheaf

open scoped LocalizedModulePresheaf

/-- The `𝒪`-linear bridge obtained from `𝒮⁻¹ℱ` by restricting scalars along
`𝒪 ⟶ 𝒮⁻¹𝒪`. -/
noncomputable abbrev localizedModulePresheafOverBase
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    PresheafOfModules (ringPresheaf 𝒪) :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight 𝒮.toLocalizationPresheaf (forget₂ CommRingCat RingCat))).obj
    (𝒮⁻¹ ℱ)

private theorem localizedModuleTensorObj_eq
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : (Opens X)ᵒᵖ) :
    ModuleCat.of (𝒪.obj U) (Localization (𝒮.obj U) ⊗[𝒪.obj U] ℱ.obj U) =
      (PresheafOfModules.Monoidal.tensorObj 𝒮.localizedRingModulePresheaf ℱ).obj U := by
  sorry

private theorem localizedModulePresheafOverBaseObj_eq
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : (Opens X)ᵒᵖ) :
    (𝒮.localizedModulePresheafOverBase ℱ).obj U =
      ModuleCat.of (𝒪.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) := by
  sorry

private noncomputable abbrev localizedModuleObjIsoTensor
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : (Opens X)ᵒᵖ) :
    (𝒮.localizedModulePresheafOverBase ℱ).obj U ≅
      (PresheafOfModules.Monoidal.tensorObj 𝒮.localizedRingModulePresheaf ℱ).obj U :=
  let e :
      ModuleCat.of (𝒪.obj U) (Localization (𝒮.obj U) ⊗[𝒪.obj U] ℱ.obj U) ≅
        (PresheafOfModules.Monoidal.tensorObj 𝒮.localizedRingModulePresheaf ℱ).obj U :=
    eqToIso (localizedModuleTensorObj_eq 𝒮 ℱ U)
  eqToIso (localizedModulePresheafOverBaseObj_eq 𝒮 ℱ U) ≪≫
    (LinearEquiv.toModuleIso
      ((LocalizedModule.equivTensorProduct (𝒮.obj U) (ℱ.obj U)).restrictScalars (𝒪.obj U))) ≪≫ e

@[simp] private theorem localizedRingModulePresheaf_map_mk
    (𝒮 : 𝒪.SubmonoidPresheaf)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : 𝒮.obj U) :
    𝒮.localizedRingModulePresheaf.map i (Localization.mk 1 s) =
      Localization.mk 1 (mapSection 𝒮 i s) := by
  sorry

/-- The source-facing localized module presheaf is canonically isomorphic to the tensor
presentation `𝒮⁻¹𝒪_X ⊗_{p,\mathcal O_X} ℱ`. -/
private theorem localizedModulePresheafOverBaseIsoTensor_naturality
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (𝒮.localizedModulePresheafOverBase ℱ).map i ≫
        (ModuleCat.restrictScalars ((ringPresheaf 𝒪).map i).hom).map
          (localizedModuleObjIsoTensor 𝒮 ℱ V).hom =
      (localizedModuleObjIsoTensor 𝒮 ℱ U).hom ≫
        (PresheafOfModules.Monoidal.tensorObj 𝒮.localizedRingModulePresheaf ℱ).map i := by
  sorry

/-- The `𝒪`-linear bridge `𝒮⁻¹ℱ`, obtained by restriction of scalars, is canonically isomorphic
to the tensor presentation `𝒮⁻¹𝒪_X ⊗_{\mathcal O_X} ℱ`. -/
noncomputable def localizedModulePresheafOverBaseIsoTensor
    (𝒮 : 𝒪.SubmonoidPresheaf)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    𝒮.localizedModulePresheafOverBase ℱ ≅
      PresheafOfModules.Monoidal.tensorObj 𝒮.localizedRingModulePresheaf ℱ :=
  PresheafOfModules.isoMk
    (fun U ↦ localizedModuleObjIsoTensor 𝒮 ℱ U)
    (fun {_ _} i ↦ localizedModulePresheafOverBaseIsoTensor_naturality 𝒮 ℱ i)

variable (ℱ : PresheafOfModules (ringPresheaf 𝒪))
variable (U : (Opens X)ᵒᵖ)

/- On sections over `U`, the source-facing owner `𝒮⁻¹ℱ` is by definition
the usual localized module `𝒮(U)^{-1}\mathcal F(U)`. Its `\mathcal O_X`-linear bridge is
`𝒮.localizedModulePresheafOverBase ℱ`, and the tensor description is the canonical comparison
coming from `LocalizedModule.equivTensorProduct`. -/
#check
  (𝒮⁻¹ ℱ)

#check
  (𝒮.localizedModulePresheafOverBase ℱ)

#check
  localizedModuleObjIsoTensor 𝒮 ℱ U

section Sheaf

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : X.Sheaf CommRingCat.{u}} (𝒮 : SubmonoidPresheaf 𝒪.obj)

/-- The sheafified localized module `𝒮⁻¹ℱ`, now owned over the sheafification of the localized
ring presheaf `𝒮.localizationPresheaf`. -/
noncomputable abbrev sheafifiedLocalizedModule
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    SheafOfModules
      (ringSheaf J (PresheafOfModules.commRingSheafification J 𝒮.localizationPresheaf)) :=
  (PresheafOfModules.moduleSheafification J 𝒮.localizationPresheaf).obj (𝒮⁻¹ ℱ.val)

/-- The `\mathcal O_X`-linear bridge obtained by sheafifying the restricted-scalars presheaf
`𝒮.localizedModulePresheafOverBase ℱ`. -/
noncomputable abbrev sheafifiedLocalizedModuleOverBase
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    SheafOfModules (ringSheaf J 𝒪) :=
  (moduleSheafification 𝒪).obj (𝒮.localizedModulePresheafOverBase ℱ.val)

/-- Lemma 17.27.2, sheafified tensor comparison for the `\mathcal O_X`-linear bridge obtained by
restricting scalars from the intrinsic localized-module owner. -/
noncomputable abbrev sheafifiedLocalizedModuleOverBaseIsoTensor
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    𝒮.sheafifiedLocalizedModuleOverBase ℱ ≅
      (moduleSheafification 𝒪).obj 𝒮.localizedRingModulePresheaf ⊗
        (moduleSheafification 𝒪).obj ℱ.val :=
  (moduleSheafification 𝒪).mapIso (localizedModulePresheafOverBaseIsoTensor 𝒮 ℱ.val) ≪≫
    (moduleSheafificationTensorIso 𝒪 𝒮.localizedRingModulePresheaf ℱ.val).symm

end Sheaf

end SubmonoidPresheaf
end TopCat.Presheaf
