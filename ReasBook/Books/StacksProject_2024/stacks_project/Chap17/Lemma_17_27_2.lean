import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.Chap18.«18_44_1_1»
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open PresheafOfModules.Monoidal
open SheafOfModules.RingedSite (restrictionAlong ringSheaf ringedSiteModuleCategory unitModule)
open scoped TensorProduct

noncomputable section

universe u v

/-- Helper for Lemma 17.27.2: the underlying `RingCat`-valued presheaf of a presheaf of
commutative rings. -/
abbrev ringPresheaf {C : Type u} [Category.{v} C]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Cᵒᵖ ⥤ RingCat.{max u v} :=
  𝒪 ⋙ forget₂ CommRingCat RingCat

namespace PresheafOfModules

/-- Helper for Lemma 17.27.2: the induced morphism of underlying `RingCat`-valued presheaves
attached to a morphism of presheaves of commutative rings. -/
abbrev presheafStructureMap
    {C : Type u} [Category.{v} C]
    {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    ringPresheaf 𝒪 ⟶ ringPresheaf 𝒪' :=
  CategoryTheory.Functor.whiskerRight α (forget₂ CommRingCat RingCat)

section ModuleSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]

/-- Helper for Lemma 17.27.2: the commutative-ring-valued sheafification of a presheaf of
commutative rings. -/
abbrev commRingSheafification (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Sheaf J CommRingCat.{max u v} :=
  (presheafToSheaf J CommRingCat.{max u v}).obj 𝒪

/-- Helper for Lemma 17.27.2: the bridge from the `RingCat`-valued sheafification of
`ringPresheaf 𝒪` to the underlying `RingCat`-valued sheaf of the commutative-ring sheafification
of `𝒪`. -/
private noncomputable abbrev sheafificationRingBridge
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    (presheafToSheaf J RingCat.{max u v}).obj (ringPresheaf 𝒪) ⟶
      ringSheaf J (commRingSheafification J 𝒪) :=
  (CategoryTheory.sheafComposeNatTrans J (forget₂ CommRingCat RingCat)
    (CategoryTheory.sheafificationAdjunction J CommRingCat.{max u v})
    (CategoryTheory.sheafificationAdjunction J RingCat.{max u v})).app 𝒪

/-- Helper for Lemma 17.27.2: the canonical ring map from a commutative-ring-valued presheaf to
the underlying `RingCat` presheaf of its sheafification. -/
abbrev sheafificationRingMap (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    ringPresheaf 𝒪 ⟶ (ringSheaf J (commRingSheafification J 𝒪)).obj :=
  CategoryTheory.toSheafify J (ringPresheaf 𝒪) ≫
    (sheafToPresheaf J RingCat.{max u v}).map (sheafificationRingBridge (J := J) 𝒪)

omit [J.WEqualsLocallyBijective CommRingCat.{max u v}] in
private theorem sheafificationRingMap_eq_whiskerRight
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    sheafificationRingMap J 𝒪 =
      Functor.whiskerRight
        (show 𝒪 ⟶ (commRingSheafification J 𝒪).obj from CategoryTheory.toSheafify J 𝒪)
        (forget₂ CommRingCat RingCat) := by
  -- Proof comment: the ring-valued sheafification map is the whiskering of the commutative-ring
  -- sheafification unit through the forgetful functor.
  simpa [sheafificationRingMap, sheafificationRingBridge, commRingSheafification, ringPresheaf,
    ringSheaf] using
    (CategoryTheory.sheafComposeNatTrans_fac J (forget₂ CommRingCat RingCat)
      (CategoryTheory.sheafificationAdjunction J CommRingCat.{max u v})
      (CategoryTheory.sheafificationAdjunction J RingCat.{max u v}) 𝒪)

instance sheafificationRingMap_isLocallyInjective
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallyInjective J (sheafificationRingMap J 𝒪) := by
  -- Proof comment: local injectivity is inherited from the sheafification unit before forgetting
  -- from commutative rings to rings.
  let η : 𝒪 ⟶ (commRingSheafification J 𝒪).obj := CategoryTheory.toSheafify J 𝒪
  have hη : Presheaf.IsLocallyInjective J η :=
    (J.W_toSheafify (A := CommRingCat.{max u v}) 𝒪).isLocallyInjective
  have hηForget :
      Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (forget RingCat)) := by
    simpa using ((Presheaf.isLocallyInjective_forget_iff (J := J) (φ := η)).2 hη)
  have hηRing :
      Presheaf.IsLocallyInjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallyInjective_forget_iff
      (J := J) (φ := Functor.whiskerRight η (forget₂ CommRingCat RingCat))).1 hηForget
  simpa [sheafificationRingMap_eq_whiskerRight (J := J) 𝒪, η] using hηRing

instance sheafificationRingMap_isLocallySurjective
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallySurjective J (sheafificationRingMap J 𝒪) := by
  -- Proof comment: local surjectivity is transported along the same forgetful comparison as
  -- local injectivity.
  let η : 𝒪 ⟶ (commRingSheafification J 𝒪).obj := CategoryTheory.toSheafify J 𝒪
  have hη : Presheaf.IsLocallySurjective J η :=
    (J.W_toSheafify (A := CommRingCat.{max u v}) 𝒪).isLocallySurjective
  have hηForget :
      Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (Functor.whiskerRight η (forget₂ CommRingCat RingCat))
          (forget RingCat)) := by
    simpa using ((Presheaf.isLocallySurjective_iff_whisker_forget (J := J) η).1 hη)
  have hηRing :
      Presheaf.IsLocallySurjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget
      (J := J) (Functor.whiskerRight η (forget₂ CommRingCat RingCat))).2 hηForget
  simpa [sheafificationRingMap_eq_whiskerRight (J := J) 𝒪, η] using hηRing

/-- Helper for Lemma 17.27.2: sheafification of presheaves of modules along the canonical map
`\mathcal O \to \mathcal O^\#`. -/
abbrev moduleSheafification
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    PresheafOfModules (ringPresheaf 𝒪) ⥤
      ringedSiteModuleCategory J (commRingSheafification J 𝒪) :=
  PresheafOfModules.sheafification (sheafificationRingMap J 𝒪)

end ModuleSheafification

end PresheafOfModules

section RingedSiteTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 17.27.2: the source-facing tensor product of sheaves of modules on a
commutative ringed site. -/
noncomputable abbrev moduleSheafification (𝒪 : Sheaf J CommRingCat.{max u v}) :
    PresheafOfModules (ringSheaf J 𝒪).obj ⥤ Mod(𝒪) :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)

namespace SheafOfModules.RingedSite

/-- Helper for Lemma 17.27.2: the tensor product of sheaves of modules on a commutative ringed
site, viewed through the ambient monoidal structure. -/
noncomputable abbrev moduleTensor
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (ℱ 𝒢 : Mod(𝒪)) :
    Mod(𝒪) :=
  (MonoidalCategoryStruct.tensorObj ℱ 𝒢 : Mod(𝒪))

scoped infixr:70 " ⊗ " => moduleTensor

end SheafOfModules.RingedSite

end RingedSiteTensor

open scoped SheafOfModules.RingedSite

namespace CategoryTheory
namespace Presheaf
namespace SubmonoidPresheaf

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}} (𝒮 : SubmonoidPresheaf 𝒪)

/- Domain-style sampling for Lemma 17.27.2:
- primary domain: localization of module-valued presheaves over a commutative-ring-valued
  presheaf, together with the tensor presentation of that localization;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizationPresheaf`,
  `ringPresheaf`,
  `PresheafOfModules.presheafStructureMap`,
  `LocalizedModule.map`,
  `LocalizedModule.equivTensorProduct`,
  `PresheafOfModules.Monoidal.tensorObj`;
- best owner abstraction: the presheaf-level owner is the localized module presheaf
  `𝒮⁻¹ℱ : PresheafOfModules (ringPresheaf 𝒮.localizationPresheaf)`, whose sections are
  `LocalizedModule (𝒮.obj U) (ℱ.obj U)`; the `𝒪`-linear view and the tensor description over
  `𝒪` are derived bridge constructions;
- primitive data: a presheaf of commutative rings `𝒪`, a multiplicative subpresheaf
  `𝒮 : SubmonoidPresheaf 𝒪`, and a presheaf of `𝒪`-modules `ℱ`;
- derived API: the localized module presheaf `𝒮⁻¹ℱ`, its restricted-scalars bridge
  `𝒮.localizedModulePresheafOverBase ℱ`, and the canonical tensor comparison
  `𝒮.localizedModulePresheafOverBaseIsoTensor ℱ`, all expressed via the owner ring map
  `PresheafOfModules.presheafStructureMap 𝒮.toLocalizationPresheaf`.

Source/core/bridge triage:
- `source-facing`: the localized module presheaf `𝒮⁻¹ℱ`;
- `core/canonical`: the owner `CategoryTheory.Presheaf.SubmonoidPresheaf` together with
  `𝒮.localizationPresheaf` and `PresheafOfModules.Monoidal.tensorObj`;
- `bridge/view`: the restricted-scalars presheaf
  `𝒮.localizedModulePresheafOverBase ℱ` and the tensor comparison
  `𝒮.localizedModulePresheafOverBaseIsoTensor ℱ`.

This file therefore places the presheaf-level owner at the general categorical layer. Topological
and sheafified specializations should reuse these declarations directly rather than rebuilding a
parallel `TopCat`-level owner. -/

/-- The localized structure presheaf `𝒮⁻¹𝒪`, viewed as an `𝒪`-module by restriction of
scalars along `𝒪 ⟶ 𝒮⁻¹𝒪`. -/
noncomputable abbrev localizedStructureModulePresheafOverBase
    (𝒮 : SubmonoidPresheaf 𝒪) :
    PresheafOfModules (ringPresheaf 𝒪) :=
  (PresheafOfModules.restrictScalars
    (PresheafOfModules.presheafStructureMap 𝒮.toLocalizationPresheaf)).obj
    (PresheafOfModules.unit (ringPresheaf 𝒮.localizationPresheaf))

private def mapSection
    (𝒮 : SubmonoidPresheaf 𝒪)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    𝒮.obj U → 𝒮.obj V :=
  fun s ↦ ⟨(𝒪.map i).hom s.1, 𝒮.map i s.2⟩

/-- Helper for Lemma 17.27.2: `mapSection` forgets to the underlying restricted section. -/
@[simp] private theorem mapSection_val
    (𝒮 : SubmonoidPresheaf 𝒪)
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : 𝒮.obj U) :
    (mapSection 𝒮 i s : 𝒪.obj V) = (𝒪.map i).hom s.1 := by
  rfl

/-- Helper for Lemma 17.27.2: restricting a product of denominators is multiplicative. -/
@[simp] private theorem mapSection_mul
    (𝒮 : SubmonoidPresheaf 𝒪)
    {U V : Cᵒᵖ} (i : U ⟶ V) (s t : 𝒮.obj U) :
    mapSection 𝒮 i (s * t) = mapSection 𝒮 i s * mapSection 𝒮 i t := by
  -- Proof comment: both numerator and submonoid-membership components are preserved by the
  -- ring-presheaf restriction map.
  ext
  simp [mapSection, map_mul]

/-- Helper for Lemma 17.27.2: restricting the trivial denominator keeps it trivial. -/
@[simp] private theorem mapSection_one
    (𝒮 : SubmonoidPresheaf 𝒪)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    mapSection 𝒮 i (1 : 𝒮.obj U) = 1 := by
  -- Proof comment: restriction preserves the multiplicative identity in the ambient ring and in
  -- the submonoid structure.
  ext
  simp [mapSection]

/-- Helper for Lemma 17.27.2: restricting along an identity morphism leaves denominators
unchanged. -/
@[simp] private theorem mapSection_id
    (𝒮 : SubmonoidPresheaf 𝒪)
    (U : Cᵒᵖ) (s : 𝒮.obj U) :
    mapSection 𝒮 (𝟙 U) s = s := by
  -- Proof comment: the identity restriction map acts trivially on both the ring section and its
  -- membership in the multiplicative subpresheaf.
  ext
  simp [mapSection]

/-- Helper for Lemma 17.27.2: denominator restriction is functorial under composition. -/
@[simp] private theorem mapSection_comp
    (𝒮 : SubmonoidPresheaf 𝒪)
    {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (s : 𝒮.obj U) :
    mapSection 𝒮 (i ≫ j) s = mapSection 𝒮 j (mapSection 𝒮 i s) := by
  -- Proof comment: both sides apply the presheaf restriction maps to the denominator in the same
  -- order, so this is just functoriality of `𝒪.map` together with the subpresheaf compatibility.
  ext
  simp [mapSection, Functor.map_comp]

local instance localizedModuleModule
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (U : Cᵒᵖ) :
    Module (𝒮.localizationPresheaf.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) :=
  LocalizedModule.moduleOfIsLocalization

local instance localizedModuleOverBase
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (U : Cᵒᵖ) :
    Module (𝒪.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) :=
  OreLocalization.instModuleOfIsScalarTower

private noncomputable def localizedModuleMapFun
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    LocalizedModule (𝒮.obj U) (ℱ.obj U) →
      ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
        (ModuleCat.of (𝒮.localizationPresheaf.obj V)
          (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) :=
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
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : ℱ.obj U) (s : 𝒮.obj U) :
    localizedModuleMapFun 𝒮 ℱ i (LocalizedModule.mk m s) =
      (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s) :
        (ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
          (ModuleCat.of (𝒮.localizationPresheaf.obj V)
            (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) := by
  rfl

/-- Helper for Lemma 17.27.2: after forgetting the `ModuleCat.restrictScalars` wrapper, the
image of a generator under `localizedModuleMapFun` is still the expected localized generator. -/
@[simp] private theorem localizedModuleMapFun_mk_coe
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : ℱ.obj U) (s : 𝒮.obj U) :
    (localizedModuleMapFun 𝒮 ℱ i (LocalizedModule.mk m s) :
      LocalizedModule (𝒮.obj V) (ℱ.obj V)) =
      LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s) := by
  -- Proof comment: this is the carrier-level version of `localizedModuleMapFun_mk`, so later
  -- scalar computations can work directly in `LocalizedModule` without reopening the owner object.
  simpa using
    (localizedModuleMapFun_mk (𝒮 := 𝒮) (ℱ := ℱ) i m s)

/-- Helper for Lemma 17.27.2: the localization presheaf restriction map sends a standard
fraction to the standard fraction obtained by restricting numerator and denominator. -/
@[simp] private theorem localizationPresheaf_map_mk
    (𝒮 : SubmonoidPresheaf 𝒪)
    {U V : Cᵒᵖ} (i : U ⟶ V) (a : 𝒪.obj U) (s : 𝒮.obj U) :
    ((𝒮.localizationPresheaf.map i).hom) (Localization.mk a s) =
      Localization.mk ((𝒪.map i).hom a) (mapSection 𝒮 i s) := by
  -- Route correction: work directly with the owner map `IsLocalization.map` on fractions instead
  -- of asking `simpa` to unfold the whole presheaf object.
  have hmap := IsLocalization.map_mk' (Q := Localization (𝒮.obj V)) (𝒮.map i) a s
  simpa [mapSection] using hmap

private theorem localizedModuleMapFun_add
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (x y : LocalizedModule (𝒮.obj U) (ℱ.obj U)) :
    localizedModuleMapFun 𝒮 ℱ i (x + y) =
      localizedModuleMapFun 𝒮 ℱ i x + localizedModuleMapFun 𝒮 ℱ i y := by
  -- Proof comment: reduce both localized sections to generators and compare the standard
  -- denominator-clearing formulas on both sides.
  induction x using LocalizedModule.induction_on with
  | h m s =>
      induction y using LocalizedModule.induction_on with
      | h m' s' =>
          rw [LocalizedModule.mk_add_mk]
          rw [localizedModuleMapFun_mk, localizedModuleMapFun_mk, localizedModuleMapFun_mk]
          have hsum :
              (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s) :
                LocalizedModule (𝒮.obj V) (ℱ.obj V)) +
                LocalizedModule.mk (show ℱ.obj V from ℱ.map i m') (mapSection 𝒮 i s') =
              LocalizedModule.mk
                ((mapSection 𝒮 i s' : 𝒪.obj V) • (show ℱ.obj V from ℱ.map i m) +
                  (mapSection 𝒮 i s : 𝒪.obj V) • (show ℱ.obj V from ℱ.map i m'))
                (mapSection 𝒮 i s * mapSection 𝒮 i s') := by
            simpa using
              (LocalizedModule.mk_add_mk
                (m1 := (show ℱ.obj V from ℱ.map i m))
                (m2 := (show ℱ.obj V from ℱ.map i m'))
                (s1 := mapSection 𝒮 i s)
                (s2 := mapSection 𝒮 i s'))
          calc
            LocalizedModule.mk (show ℱ.obj V from ℱ.map i (s' • m + s • m')) (mapSection 𝒮 i (s * s')) =
                LocalizedModule.mk
                  ((mapSection 𝒮 i s' : 𝒪.obj V) • (show ℱ.obj V from ℱ.map i m) +
                    (mapSection 𝒮 i s : 𝒪.obj V) • (show ℱ.obj V from ℱ.map i m'))
                  (mapSection 𝒮 i s * mapSection 𝒮 i s') := by
                    congr
                    · calc
                        (show ℱ.obj V from ℱ.map i (s' • m + s • m')) =
                            (show ℱ.obj V from ℱ.map i (s' • m)) +
                              (show ℱ.obj V from ℱ.map i (s • m')) := by
                                simpa using (ℱ.map i).hom.map_add ((s' : 𝒪.obj U) • m) ((s : 𝒪.obj U) • m')
                        _ = (mapSection 𝒮 i s' : 𝒪.obj V) • (show ℱ.obj V from ℱ.map i m) +
                              (mapSection 𝒮 i s : 𝒪.obj V) • (show ℱ.obj V from ℱ.map i m') := by
                                simpa [mapSection] using
                                  congrArg₂ (fun x y ↦ x + y)
                                    (ℱ.map_smul i (s' : 𝒪.obj U) m)
                                    (ℱ.map_smul i (s : 𝒪.obj U) m')
                    · ext
                      simp [mapSection, map_mul]
            _ = (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s) :
                  LocalizedModule (𝒮.obj V) (ℱ.obj V)) +
                  LocalizedModule.mk (show ℱ.obj V from ℱ.map i m') (mapSection 𝒮 i s') := by
                    exact hsum.symm

/-- Helper for Lemma 17.27.2: scalar multiplication in the restricted-scalars codomain is the
ordinary scalar action after applying the localization ring map. -/
@[simp] private theorem localizedModule_restrictScalars_smul_eq
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (r : 𝒮.localizationPresheaf.obj U)
    (y :
      ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
        (ModuleCat.of (𝒮.localizationPresheaf.obj V)
          (LocalizedModule (𝒮.obj V) (ℱ.obj V))))) :
    ((r • y :
        ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
          (ModuleCat.of (𝒮.localizationPresheaf.obj V)
            (LocalizedModule (𝒮.obj V) (ℱ.obj V))))) :
      LocalizedModule (𝒮.obj V) (ℱ.obj V)) =
      ((𝒮.localizationPresheaf.map i).hom r) •
        (y : LocalizedModule (𝒮.obj V) (ℱ.obj V)) := by
  -- Proof comment: after changing to the underlying carrier, the restricted-scalars action is
  -- definitionally the usual action through the mapped scalar.
  rfl

/-- Helper for Lemma 17.27.2: the source-side scalar action on a generator already has the
expected normal form after applying the restriction map. -/
@[simp] private theorem localizedModuleMapFun_smul_lhs_mk
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (a : 𝒪.obj U) (s t : 𝒮.obj U) (m : ℱ.obj U) :
    localizedModuleMapFun 𝒮 ℱ i ((Localization.mk a s) • LocalizedModule.mk m t) =
      (LocalizedModule.mk (show ℱ.obj V from ℱ.map i (a • m)) (mapSection 𝒮 i (s * t)) :
        (ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
          (ModuleCat.of (𝒮.localizationPresheaf.obj V)
            (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) := by
  -- Proof comment: the source-side localization action is `mk_smul_mk`, after which the
  -- restriction formula is exactly `localizedModuleMapFun_mk`.
  rw [LocalizedModule.mk_smul_mk, localizedModuleMapFun_mk]

/-- Helper for Lemma 17.27.2: after transporting the codomain scalar through
`ModuleCat.restrictScalars`, the target-side scalar action on a generator is the expected
localized numerator/denominator formula. -/
@[simp] private theorem localizedModuleMapFun_smul_rhs_mk
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (a : 𝒪.obj U) (s t : 𝒮.obj U) (m : ℱ.obj U) :
    ((𝒮.localizationPresheaf.map i).hom (Localization.mk a s)) •
        (localizedModuleMapFun 𝒮 ℱ i (LocalizedModule.mk m t) :
          LocalizedModule (𝒮.obj V) (ℱ.obj V)) =
      (LocalizedModule.mk (show ℱ.obj V from ℱ.map i (a • m)) (mapSection 𝒮 i (s * t)) :
        LocalizedModule (𝒮.obj V) (ℱ.obj V)) := by
  -- Proof comment: rewrite both the scalar and the localized section on generators, then use the
  -- standard `LocalizedModule.mk_smul_mk` formula.
  have hmk :
      (Localization.mk ((𝒪.map i).hom a) (mapSection 𝒮 i s) :
          Localization (𝒮.obj V)) •
        (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i t) :
          LocalizedModule (𝒮.obj V) (ℱ.obj V)) =
      (LocalizedModule.mk
        (((𝒪.map i).hom a) • (show ℱ.obj V from ℱ.map i m))
        (mapSection 𝒮 i s * mapSection 𝒮 i t) :
          LocalizedModule (𝒮.obj V) (ℱ.obj V)) := by
    simpa using
      (LocalizedModule.mk_smul_mk
        (R := 𝒪.obj V)
        (S := 𝒮.obj V)
        (r := (show 𝒪.obj V from (𝒪.map i).hom a))
        (m := (show ℱ.obj V from ℱ.map i m))
        (s := mapSection 𝒮 i s)
        (t := mapSection 𝒮 i t))
  calc
    ((𝒮.localizationPresheaf.map i).hom (Localization.mk a s)) •
        (localizedModuleMapFun 𝒮 ℱ i (LocalizedModule.mk m t) :
          LocalizedModule (𝒮.obj V) (ℱ.obj V)) =
      (LocalizedModule.mk
        (((𝒪.map i).hom a) • (show ℱ.obj V from ℱ.map i m))
        (mapSection 𝒮 i s * mapSection 𝒮 i t) :
          LocalizedModule (𝒮.obj V) (ℱ.obj V)) := by
            rw [localizationPresheaf_map_mk, localizedModuleMapFun_mk_coe]
            exact hmk
    _ =
      (LocalizedModule.mk (show ℱ.obj V from ℱ.map i (a • m)) (mapSection 𝒮 i (s * t)) :
        LocalizedModule (𝒮.obj V) (ℱ.obj V)) := by
            congr
            · simpa [mapSection] using (ℱ.map_smul i a m).symm
            · exact (mapSection_mul 𝒮 i s t).symm

private theorem localizedModuleMapFun_smul
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (r : 𝒮.localizationPresheaf.obj U) (x : LocalizedModule (𝒮.obj U) (ℱ.obj U)) :
    localizedModuleMapFun 𝒮 ℱ i (r • x) =
      r • localizedModuleMapFun 𝒮 ℱ i x := by
  -- Proof comment: reduce the scalar and the localized section to generators and compare the
  -- two normal forms obtained from the source and target scalar actions.
  induction r using Localization.induction_on with
  | _ q =>
      rcases q with ⟨a, s⟩
      induction x using LocalizedModule.induction_on with
      | _ m t =>
          rw [localizedModuleMapFun_smul_lhs_mk]
          change
            ((LocalizedModule.mk (show ℱ.obj V from ℱ.map i (a • m)) (mapSection 𝒮 i (s * t)) :
                ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
                  (ModuleCat.of (𝒮.localizationPresheaf.obj V)
                    (LocalizedModule (𝒮.obj V) (ℱ.obj V))))) :
              LocalizedModule (𝒮.obj V) (ℱ.obj V)) =
              (((Localization.mk a s) •
                  localizedModuleMapFun 𝒮 ℱ i (LocalizedModule.mk m t) :
                    ((ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
                      (ModuleCat.of (𝒮.localizationPresheaf.obj V)
                        (LocalizedModule (𝒮.obj V) (ℱ.obj V))))) :
                LocalizedModule (𝒮.obj V) (ℱ.obj V))
          rw [localizedModule_restrictScalars_smul_eq]
          change
            (LocalizedModule.mk (show ℱ.obj V from ℱ.map i (a • m)) (mapSection 𝒮 i (s * t)) :
              LocalizedModule (𝒮.obj V) (ℱ.obj V)) =
              ((𝒮.localizationPresheaf.map i).hom (Localization.mk a s)) •
                (localizedModuleMapFun 𝒮 ℱ i (LocalizedModule.mk m t) :
                  LocalizedModule (𝒮.obj V) (ℱ.obj V))
          rw [localizedModuleMapFun_smul_rhs_mk]

private noncomputable def localizedModuleMap
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
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
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : ℱ.obj U) (s : 𝒮.obj U) :
    localizedModuleMap 𝒮 ℱ i (LocalizedModule.mk m s) =
      (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s) :
        (ModuleCat.restrictScalars (𝒮.localizationPresheaf.map i).hom).obj
          (ModuleCat.of (𝒮.localizationPresheaf.obj V)
            (LocalizedModule (𝒮.obj V) (ℱ.obj V)))) := by
  -- Proof comment: `localizedModuleMap` is the linear map built from `localizedModuleMapFun`.
  rfl

private theorem localizedModulePresheaf_map_id
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ) :
    localizedModuleMap 𝒮 ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (𝒮.localizationPresheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (𝒮.localizationPresheaf.map_id U))).inv.app
        (ModuleCat.of (𝒮.localizationPresheaf.obj U)
          (LocalizedModule (𝒮.obj U) (ℱ.obj U))) := by
  -- Proof comment: compare the two maps on a standard localized generator and use the presheaf
  -- identity axiom for the numerator together with `mapSection_id` for the denominator.
  apply ModuleCat.hom_ext
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s =>
      have hmap' :
          (ModuleCat.Hom.hom (ℱ.map (𝟙 U))) m =
            (ModuleCat.Hom.hom
              ((ModuleCat.restrictScalarsId' (((ringPresheaf 𝒪).map (𝟙 U)).hom)
                (congrArg RingCat.Hom.hom (((ringPresheaf 𝒪).map_id U)))).inv.app
                (ℱ.obj U))) m := by
        exact congrArg (fun h ↦ (ModuleCat.Hom.hom h) m) (ℱ.map_id U)
      have hmap :
          (show ℱ.obj U from ℱ.map (𝟙 U) m) = m := by
        calc
          (ModuleCat.Hom.hom (ℱ.map (𝟙 U))) m =
              (ModuleCat.Hom.hom
                ((ModuleCat.restrictScalarsId' (((ringPresheaf 𝒪).map (𝟙 U)).hom)
                  (congrArg RingCat.Hom.hom (((ringPresheaf 𝒪).map_id U)))).inv.app
                  (ℱ.obj U))) m := hmap'
          _ = m := by
            exact ModuleCat.restrictScalarsId'App_inv_apply
              (((ringPresheaf 𝒪).map (𝟙 U)).hom)
              (congrArg RingCat.Hom.hom (((ringPresheaf 𝒪).map_id U)))
              (ℱ.obj U)
              m
      rw [localizedModuleMap_mk]
      rw [hmap, mapSection_id]
      symm
      exact ModuleCat.restrictScalarsId'App_inv_apply
        ((𝒮.localizationPresheaf.map (𝟙 U)).hom)
        (congrArg CommRingCat.Hom.hom (𝒮.localizationPresheaf.map_id U))
        (ModuleCat.of (𝒮.localizationPresheaf.obj U)
          (LocalizedModule (𝒮.obj U) (ℱ.obj U)))
        (LocalizedModule.mk m s)

private theorem localizedModulePresheaf_map_comp
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    localizedModuleMap 𝒮 ℱ (i ≫ j) =
      localizedModuleMap 𝒮 ℱ i ≫
        (ModuleCat.restrictScalars _).map (localizedModuleMap 𝒮 ℱ j) ≫
        (ModuleCat.restrictScalarsComp' (𝒮.localizationPresheaf.map i).hom
          (𝒮.localizationPresheaf.map j).hom
          (𝒮.localizationPresheaf.map (i ≫ j)).hom
          (congrArg CommRingCat.Hom.hom <| 𝒮.localizationPresheaf.map_comp i j)).inv.app
        (ModuleCat.of (𝒮.localizationPresheaf.obj W)
          (LocalizedModule (𝒮.obj W) (ℱ.obj W))) := by
  -- Proof comment: compare the direct and iterated restriction maps on a standard localized
  -- generator, and use the explicit composition bridge only at the final carrier level.
  apply ModuleCat.hom_ext
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s =>
      change
        (LocalizedModule.mk (show ℱ.obj W from ℱ.map (i ≫ j) m) (mapSection 𝒮 (i ≫ j) s) :
          LocalizedModule (𝒮.obj W) (ℱ.obj W)) =
          ((ModuleCat.restrictScalarsComp' (𝒮.localizationPresheaf.map i).hom
              (𝒮.localizationPresheaf.map j).hom
              (𝒮.localizationPresheaf.map (i ≫ j)).hom
              (congrArg CommRingCat.Hom.hom <| 𝒮.localizationPresheaf.map_comp i j)).inv.app
              (ModuleCat.of (𝒮.localizationPresheaf.obj W)
                (LocalizedModule (𝒮.obj W) (ℱ.obj W))))
            (LocalizedModule.mk
              (show ℱ.obj W from ℱ.map j (show ℱ.obj V from ℱ.map i m))
              (mapSection 𝒮 j (mapSection 𝒮 i s)))
      have hmap :
          (show ℱ.obj W from ℱ.map (i ≫ j) m) =
            (show ℱ.obj W from ℱ.map j (show ℱ.obj V from ℱ.map i m)) := by
        simpa using (congrArg (fun f => f m) (ℱ.map_comp i j)).symm
      have hsection :
          mapSection 𝒮 (i ≫ j) s = mapSection 𝒮 j (mapSection 𝒮 i s) := by
        exact mapSection_comp 𝒮 i j s
      simpa [ModuleCat.restrictScalarsComp'App_inv_apply] using
        congrArg₂
          (fun m' s' ↦
            (LocalizedModule.mk m' s' : LocalizedModule (𝒮.obj W) (ℱ.obj W)))
          hmap hsection

/-- Lemma 17.27.2, presheaf form: the localized module presheaf `𝒮⁻¹ℱ` over the localized ring
presheaf `𝒮⁻¹𝒪`. -/
noncomputable def localizedModulePresheaf
    (𝒮 : SubmonoidPresheaf 𝒪)
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
  `(($(𝒮)).localizedModulePresheaf $ℱ)

end LocalizedModulePresheaf

open scoped LocalizedModulePresheaf

/-- The `𝒪`-linear bridge obtained from `𝒮⁻¹ℱ` by restricting scalars along
`𝒪 ⟶ 𝒮⁻¹𝒪`. -/
noncomputable abbrev localizedModulePresheafOverBase
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    PresheafOfModules (ringPresheaf 𝒪) :=
  (PresheafOfModules.restrictScalars
    (PresheafOfModules.presheafStructureMap 𝒮.toLocalizationPresheaf)).obj
    (𝒮⁻¹ ℱ)

/-- Helper for Lemma 17.27.2: the objectwise tensor presentation of the localized structure
module has the same carrier as the explicit tensor product. -/
private noncomputable def localizedModuleTensorObjIso
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat.of (𝒪.obj U) (Localization (𝒮.obj U) ⊗[𝒪.obj U] ℱ.obj U) ≅
      (tensorObj 𝒮.localizedStructureModulePresheafOverBase ℱ).obj U := by
  let _ : Module (𝒪.obj U) (Localization (𝒮.obj U) ⊗[𝒪.obj U] ℱ.obj U) := inferInstance
  let _ :
      Module (𝒪.obj U)
        (↑(𝒮.localizedStructureModulePresheafOverBase.obj U) ⊗[𝒪.obj U] ℱ.obj U) := inferInstance
  refine
    { hom := ModuleCat.ofHom ?_
      inv := ModuleCat.ofHom ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · exact
      { toFun := fun x ↦ x
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro r x
          rfl }
  · exact
      { toFun := fun x ↦ x
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro r x
          rfl }
  · ext x
    rfl
  · ext x
    rfl

/-- Helper for Lemma 17.27.2: applying the identity ring hom to a scalar does not change its
action on a module. -/
@[simp] private theorem ring_hom_id_smul
    {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (r : R) (x : M) :
    (RingHom.id R) r • x = r • x := by
  rfl

/-- Helper for Lemma 17.27.2: the restricted-scalars presentation of the localized module object
is canonically the same `𝒪(U)`-module as the explicit localized module carrier. -/
private noncomputable def localizedModulePresheafOverBaseObjIso
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ) :
    (𝒮.localizedModulePresheafOverBase ℱ).obj U ≅
      ModuleCat.of (𝒪.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) := by
  -- Proof comment: restriction of scalars does not change the underlying localized-module
  -- carrier, so the bridge is the identity on sections.
  let _ : Module (𝒪.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U)) := inferInstance
  let _ : Module (ringPresheaf 𝒪).obj U ((𝒮.localizedModulePresheaf ℱ).obj U) := inferInstance
  refine
    { hom := ModuleCat.ofHom ?_
      inv := ModuleCat.ofHom ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · exact
      { toFun := fun x ↦ x
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro r x
          rfl }
  · exact
      { toFun := fun x ↦ x
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro r x
          rfl }
  · ext x
    rfl
  · ext x
    rfl

/-- Helper for Lemma 17.27.2: the objectwise localized-module-over-base bridge is the identity on
sections. -/
@[simp] private theorem localizedModulePresheafOverBaseObjIso_hom_apply
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ)
    (x : (𝒮.localizedModulePresheafOverBase ℱ).obj U) :
    (localizedModulePresheafOverBaseObjIso 𝒮 ℱ U).hom x = x := by
  -- Proof comment: the bridge comes from an equality of objects whose carrier map is literally
  -- the identity.
  simp [localizedModulePresheafOverBaseObjIso]

/-- Helper for Lemma 17.27.2: the inverse objectwise localized-module-over-base bridge is also
the identity on sections. -/
@[simp] private theorem localizedModulePresheafOverBaseObjIso_inv_apply
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ)
    (x : ModuleCat.of (𝒪.obj U) (LocalizedModule (𝒮.obj U) (ℱ.obj U))) :
    (localizedModulePresheafOverBaseObjIso 𝒮 ℱ U).inv x = x := by
  -- Proof comment: this is the inverse carrier-level identity coming from the same equality.
  simp [localizedModulePresheafOverBaseObjIso]

private noncomputable def localizedGeneratorApp
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ) :
    ℱ.obj U ⟶ (𝒮.localizedModulePresheafOverBase ℱ).obj U := by
  refine ?_ ≫ (localizedModulePresheafOverBaseObjIso 𝒮 ℱ U).inv
  change ModuleCat.of (𝒪.obj U) ↑(ℱ.obj U) ⟶
      ModuleCat.of (𝒪.obj U) (LocalizedModule (𝒮.obj U) ↑(ℱ.obj U))
  exact ModuleCat.ofHom (LocalizedModule.mkLinearMap (𝒮.obj U) (ℱ.obj U))

/-- Helper for Lemma 17.27.2: the localization unit over `U` sends a section to the corresponding
denominator-one localized generator. -/
@[simp] private theorem localizedGeneratorApp_apply
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ) (m : ℱ.obj U) :
    localizedGeneratorApp 𝒮 ℱ U m =
      (LocalizedModule.mk m (1 : 𝒮.obj U) :
        (𝒮.localizedModulePresheafOverBase ℱ).obj U) := by
  -- Proof comment: the localization unit is the sectionwise `LocalizedModule.mkLinearMap`, and
  -- the transport back across the objectwise bridge is the identity on the carrier.
  simp [localizedGeneratorApp]

private theorem localizedModulePresheafOverBase_naturality
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    ℱ.map i ≫
        (ModuleCat.restrictScalars ((ringPresheaf 𝒪).map i).hom).map
          (localizedGeneratorApp 𝒮 ℱ V) =
      localizedGeneratorApp 𝒮 ℱ U ≫ (𝒮.localizedModulePresheafOverBase ℱ).map i := by
  -- Proof comment: both sides send a section `m` to the denominator-one localized generator
  -- obtained after restricting `m` along `i`.
  apply ModuleCat.hom_ext
  ext m
  simp [localizedGeneratorApp, localizedModuleMap_mk]

/-- The presheaf-level localization morphism `\mathcal F \to \mathcal S^{-1}\mathcal F`, viewed
by restriction of scalars along `\mathcal O ⟶ \mathcal S^{-1}\mathcal O`. -/
noncomputable def toLocalizedModulePresheafOverBase
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    ℱ ⟶ 𝒮.localizedModulePresheafOverBase ℱ where
  app U := localizedGeneratorApp 𝒮 ℱ U
  naturality {U V} i := by
    simpa using localizedModulePresheafOverBase_naturality 𝒮 ℱ i

private noncomputable abbrev localizedModuleObjIsoTensor
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ) :
    (𝒮.localizedModulePresheafOverBase ℱ).obj U ≅
      (tensorObj 𝒮.localizedStructureModulePresheafOverBase ℱ).obj U :=
  localizedModulePresheafOverBaseObjIso 𝒮 ℱ U ≪≫
    (LinearEquiv.toModuleIso
      ((LocalizedModule.equivTensorProduct (𝒮.obj U) (ℱ.obj U)).restrictScalars (𝒪.obj U))) ≪≫
    localizedModuleTensorObjIso 𝒮 ℱ U

/-- Helper for Lemma 17.27.2: the localized-module/tensor comparison sends a standard generator
to the corresponding pure tensor `1/s ⊗ m`. -/
@[simp] private theorem localizedModuleObjIsoTensor_hom_mk
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) (U : Cᵒᵖ)
    (m : ℱ.obj U) (s : 𝒮.obj U) :
    (localizedModuleObjIsoTensor 𝒮 ℱ U).hom (LocalizedModule.mk m s) =
      ((Localization.mk 1 s) ⊗ₜ[𝒪.obj U] m :
        (tensorObj 𝒮.localizedStructureModulePresheafOverBase ℱ).obj U) := by
  -- Proof comment: the two transport isomorphisms in `localizedModuleObjIsoTensor` are identity
  -- maps on carriers, so the computation reduces to the standard localization/tensor equivalence.
  simp [localizedModuleObjIsoTensor]

@[simp] private theorem localizedStructureModulePresheafOverBase_map_mk
    (𝒮 : SubmonoidPresheaf 𝒪)
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : 𝒮.obj U) :
    𝒮.localizedStructureModulePresheafOverBase.map i (Localization.mk 1 s) =
      Localization.mk 1 (mapSection 𝒮 i s) := by
  -- Proof comment: after unfolding the restricted unit-module map, this is exactly the fraction
  -- formula for the localization presheaf restriction map at numerator `1`.
  change ((𝒮.localizationPresheaf.map i).hom) (Localization.mk 1 s) =
      Localization.mk 1 (mapSection 𝒮 i s)
  simpa using localizationPresheaf_map_mk (𝒮 := 𝒮) i (1 : 𝒪.obj U) s

/-- Helper for Lemma 17.27.2: the tensor-presheaf restriction map sends a pure tensor to the
tensor of the two restricted factors. -/
private theorem tensorObjMap_tmul
    (𝒜 ℬ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (a : 𝒜.obj U) (b : ℬ.obj U) :
    (((tensorObj 𝒜 ℬ).map i).hom (a ⊗ₜ[𝒪.obj U] b) :
      𝒜.obj V ⊗[𝒪.obj V] ℬ.obj V) =
      ((show 𝒜.obj V from (𝒜.map i).hom a) ⊗ₜ[𝒪.obj V]
        (show ℬ.obj V from (ℬ.map i).hom b)) := by
  -- Proof comment: this is exactly the owner computation rule for the tensor-product presheaf.
  simpa using PresheafOfModules.Monoidal.tensorObj_map_tmul (M₁ := 𝒜) (M₂ := ℬ) i a b

/-- The source-facing localized module presheaf is canonically isomorphic to the tensor
presentation `𝒮⁻¹𝒪 ⊗_{\mathcal O} ℱ`. -/
private theorem localizedModulePresheafOverBaseIsoTensor_naturality
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (𝒮.localizedModulePresheafOverBase ℱ).map i ≫
        (ModuleCat.restrictScalars ((ringPresheaf 𝒪).map i).hom).map
          (localizedModuleObjIsoTensor 𝒮 ℱ V).hom =
      (localizedModuleObjIsoTensor 𝒮 ℱ U).hom ≫
        (tensorObj 𝒮.localizedStructureModulePresheafOverBase ℱ).map i := by
  -- Proof comment: both sides are determined by their effect on a standard localized generator,
  -- where the localized-module/tensor comparison and both presheaf restriction maps have explicit
  -- generator formulas.
  apply ModuleCat.hom_ext
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s =>
      simp [localizedModuleMap_mk]
      change
        (localizedModuleObjIsoTensor 𝒮 ℱ V).hom
            (LocalizedModule.mk (show ℱ.obj V from ℱ.map i m) (mapSection 𝒮 i s)) =
          ((tensorObj 𝒮.localizedStructureModulePresheafOverBase ℱ).map i).hom
            ((localizedModuleObjIsoTensor 𝒮 ℱ U).hom (LocalizedModule.mk m s))
      rw [localizedModuleObjIsoTensor_hom_mk, localizedModuleObjIsoTensor_hom_mk,
        tensorObjMap_tmul, localizedStructureModulePresheafOverBase_map_mk]

/-- The `𝒪`-linear bridge `𝒮⁻¹ℱ`, obtained by restriction of scalars, is canonically isomorphic
to the tensor presentation `𝒮⁻¹𝒪 ⊗_{\mathcal O} ℱ`. -/
noncomputable def localizedModulePresheafOverBaseIsoTensor
    (𝒮 : SubmonoidPresheaf 𝒪)
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    𝒮.localizedModulePresheafOverBase ℱ ≅
      tensorObj 𝒮.localizedStructureModulePresheafOverBase ℱ :=
  PresheafOfModules.isoMk
    (fun U ↦ localizedModuleObjIsoTensor 𝒮 ℱ U)
    (fun {_ _} i ↦ localizedModulePresheafOverBaseIsoTensor_naturality 𝒮 ℱ i)

variable (ℱ : PresheafOfModules (ringPresheaf 𝒪))
variable (U : Cᵒᵖ)

/- On sections over `U`, the owner `𝒮⁻¹ℱ` is by definition the localized module
`𝒮(U)^{-1}\mathcal F(U)`. Its `\mathcal O`-linear bridge is
`𝒮.localizedModulePresheafOverBase ℱ`, while the localized structure presheaf over `𝒪` is
`𝒮.localizedStructureModulePresheafOverBase`. The tensor description is the canonical comparison
coming from `LocalizedModule.equivTensorProduct`. -/
set_option linter.hashCommand false in
#check
  (𝒮⁻¹ ℱ)

set_option linter.hashCommand false in
#check
  (𝒮.localizedModulePresheafOverBase ℱ)

set_option linter.hashCommand false in
#check
  𝒮.localizedStructureModulePresheafOverBase

set_option linter.hashCommand false in
#check
  localizedModuleObjIsoTensor 𝒮 ℱ U

section Sheaf

variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}} (𝒮 : SubmonoidPresheaf O.obj)

local notation "Mod(" O ")" => ringedSiteModuleCategory J O

/-- Helper for Lemma 17.27.2: the canonical morphism from `O` to the sheafification of the
localized structure presheaf `𝒮⁻¹O`. -/
noncomputable def toSheafifiedLocalizationPresheaf :
    O ⟶ (presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf :=
  (sheafificationIso O).hom ≫
    (presheafToSheaf J CommRingCat).map 𝒮.toLocalizationPresheaf

/- Domain-style sampling for the sheafified half of Lemma 17.27.2:
- primary domain: sheafification of the localized module presheaf on a commutative ringed site;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizedModulePresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.toSheafifiedLocalizationPresheaf`,
  `PresheafOfModules.moduleSheafification`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.moduleTensor`,
  `PresheafOfModules.sheafificationAdjunction`;
- best owner abstraction: the source-facing sheaf owner is the sheafification of the existing
  localized module presheaf, over the sheafified localized structure sheaf `(𝒮⁻¹O)^#[J]`;
- primitive data: a sheaf of commutative rings `O`, a multiplicative subpresheaf
  `𝒮 : SubmonoidPresheaf O.obj`, and an `O`-module sheaf `ℱ`;
- derived API: the source-facing sheafified localization `(𝒮⁻¹ℱ)^#[J]` itself, together with
  the final `O`-linear tensor comparison landing in the intrinsic sheaf tensor owner `⊗`;
  intermediate sheafification-of-presheaf-tensor presentations are internal bridge/view data.

Source/core/bridge triage:
- `source-facing`: the sheafified localized module `(𝒮⁻¹ℱ)^#[J]`;
- `core/canonical`: `localizedModulePresheaf`, `PresheafOfModules.moduleSheafification`, and the
  sheafified localization ring map `𝒮.toSheafifiedLocalizationPresheaf`, together with the
  sheaf tensor owner `moduleTensor`;
- `bridge/view`: the restricted-scalars identification and the internal sheafification-unit tensor
  comparison used only to reach the canonical tensor endpoint. -/

/-- The source-facing sheafified localized module `(𝒮⁻¹ℱ)^#[J]` over the sheafified localized
structure sheaf `(𝒮⁻¹O)^#[J]`. -/
noncomputable abbrev sheafifiedLocalizedModule
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (𝒮 : SubmonoidPresheaf O.obj) (ℱ : ringedSiteModuleCategory J O) :
    ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf) :=
  (PresheafOfModules.moduleSheafification J 𝒮.localizationPresheaf).obj
    (𝒮.localizedModulePresheaf ℱ.val)

/-- The localized structure sheaf `(𝒮⁻¹O)^#[J]`, viewed as an `O`-module by restriction of
scalars along `O ⟶ (𝒮⁻¹O)^#[J]`, implemented by sheafifying the presheaf-level bridge
`𝒮.localizedStructureModulePresheafOverBase`. -/
noncomputable abbrev sheafifiedLocalizedStructureModuleOverBase
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (𝒮 : SubmonoidPresheaf O.obj) :
    ringedSiteModuleCategory J O :=
  (moduleSheafification O).obj 𝒮.localizedStructureModulePresheafOverBase

/- Textbook notation for the sheafified localized module `(𝒮⁻¹ℱ)^#[J]`. Since the site is not
inferable from the localized module presheaf alone, we keep it explicit in `[J]` and attach it
directly to the canonical owner
`CategoryTheory.Presheaf.SubmonoidPresheaf.sheafifiedLocalizedModule`. The module slot is a
general term so internal bridge arguments can still use `(𝒮⁻¹(unitModule J O))^#[J]`. -/
namespace SheafifiedLocalizedModule

scoped syntax:lead "(" ident noWs "⁻¹" term ")^#[" term "]" : term

scoped macro_rules
  | `(($𝒮⁻¹ $ℱ)^#[$J]) => `(sheafifiedLocalizedModule $J $𝒮 $ℱ)

end SheafifiedLocalizedModule

open scoped SheafifiedLocalizedModule

private theorem sheafifiedLocalizedModuleOverBase_eq_restriction
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (𝒮 : SubmonoidPresheaf O.obj) (ℱ : ringedSiteModuleCategory J O) :
    (moduleSheafification O).obj (𝒮.localizedModulePresheafOverBase ℱ.val) =
      (restrictionAlong 𝒮.toSheafifiedLocalizationPresheaf).obj
        ((𝒮⁻¹ℱ)^#[J]) := by
  -- Proof comment: both sides are the same sheafification of the underlying abelian presheaf,
  -- equipped with the same `O`-module structure after restricting along
  -- `O ⟶ (𝒮⁻¹O)^#[J]`.
  simp [sheafifiedLocalizedModule, SheafOfModules.RingedSite.restrictionAlong,
    SheafOfModules.RingedSite.ringSheafMap, toSheafifiedLocalizationPresheaf]

noncomputable abbrev sheafifiedLocalizedModuleRestrictionIso
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (𝒮 : SubmonoidPresheaf O.obj) (ℱ : ringedSiteModuleCategory J O) :
    (restrictionAlong 𝒮.toSheafifiedLocalizationPresheaf).obj
        ((𝒮⁻¹ℱ)^#[J]) ≅
      (moduleSheafification O).obj (𝒮.localizedModulePresheafOverBase ℱ.val) :=
  (eqToIso (sheafifiedLocalizedModuleOverBase_eq_restriction J 𝒮 ℱ)).symm

private noncomputable def restrictScalarsIdIso
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (ℱ : PresheafOfModules (ringSheaf J O).obj) :
    (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj ℱ ≅ ℱ :=
  PresheafOfModules.isoMk
    (fun U ↦ by
      simpa using
        (ModuleCat.restrictScalarsId'App
          (((𝟙 (ringSheaf J O).obj : (ringSheaf J O).obj ⟶ (ringSheaf J O).obj).app U).hom)
          rfl
          (ℱ.obj U)))
    (fun {U V} i ↦ by
      ext x
      rfl)

private noncomputable abbrev sheafificationUnitToVal
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (ℱ : PresheafOfModules (ringSheaf J O).obj) :
    ℱ ⟶ ((moduleSheafification O).obj ℱ).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).unit.app ℱ ≫
    (restrictScalarsIdIso J ((moduleSheafification O).obj ℱ).val).hom

private noncomputable abbrev sheafificationCounitIso
    {J : GrothendieckTopology C} {O : Sheaf J CommRingCat.{max u v}}
    (ℱ : ringedSiteModuleCategory J O) :
    (moduleSheafification O).obj ℱ.val ≅ ℱ :=
  let e := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).counit
  e.app ℱ

/-- Helper for Lemma 17.27.2: the canonical oplax-monoidal comparison from sheafification of a
presheaf tensor product to the tensor product of the two sheafifications. -/
private noncomputable abbrev moduleSheafificationTensorComparison
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory J O)]
    (𝒜 : PresheafOfModules (ringSheaf J O).obj) (ℱ : ringedSiteModuleCategory J O) :
    (moduleSheafification O).obj (PresheafOfModules.Monoidal.tensorObj 𝒜 ℱ.val) ⟶
      ((moduleSheafification O).obj 𝒜) ⊗ ((moduleSheafification O).obj ℱ.val) :=
  -- Proof comment: use the canonical monoidal comparison of the sheafification functor directly,
  -- rather than rebuilding the oplax comparison through an auxiliary tensor map.
  (moduleSheafification O).map
    (PresheafOfModules.Monoidal.tensorHom
      (sheafificationUnitToVal J 𝒜)
      (sheafificationUnitToVal J ℱ.val))

/-- Helper for Lemma 17.27.2: the oplax-monoidal sheafification comparison is invertible. -/
private instance moduleSheafificationTensorComparison_isIso
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory J O)]
    (𝒜 : PresheafOfModules (ringSheaf J O).obj) (ℱ : ringedSiteModuleCategory J O) :
    IsIso (moduleSheafificationTensorComparison J 𝒜 ℱ) := by
  -- Proof comment: the comparison is the `hom` of a canonical isomorphism.
  change IsIso
    (Functor.OplaxMonoidal.δ (_root_.moduleSheafification (J := J) O) 𝒜 ℱ.val)
  infer_instance

private noncomputable abbrev moduleSheafificationTensorIso
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory J O)]
    (𝒜 : PresheafOfModules (ringSheaf J O).obj) (ℱ : ringedSiteModuleCategory J O) :
    (moduleSheafification O).obj (PresheafOfModules.Monoidal.tensorObj 𝒜 ℱ.val) ≅
      ((moduleSheafification O).obj 𝒜) ⊗ ((moduleSheafification O).obj ℱ.val) :=
  -- Proof comment: keep the final tensor comparison in the canonical `μIso` spelling used in the
  -- sibling Chapter 17 files.
  asIso (moduleSheafificationTensorComparison J 𝒜 ℱ)

/-- Internal bridge: the source-facing localized module `(𝒮⁻¹ℱ)^#[J]`, viewed over `O` by
restriction of scalars, identifies with the sheafification of the presheaf tensor presentation. -/
private noncomputable abbrev sheafifiedLocalizedModuleIsoSheafifiedTensor
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (𝒮 : SubmonoidPresheaf O.obj) [MonoidalCategory (ringedSiteModuleCategory J O)]
    (ℱ : ringedSiteModuleCategory J O) :
    (restrictionAlong 𝒮.toSheafifiedLocalizationPresheaf).obj
        ((𝒮⁻¹ℱ)^#[J]) ≅
      (moduleSheafification O).obj
        (tensorObj 𝒮.localizedStructureModulePresheafOverBase ℱ.val) :=
  sheafifiedLocalizedModuleRestrictionIso J 𝒮 ℱ ≪≫
    (moduleSheafification O).mapIso (𝒮.localizedModulePresheafOverBaseIsoTensor ℱ.val)

/-- Lemma 17.27.2, sheafified form: after restricting scalars along
`O ⟶ (𝒮⁻¹O)^#[J]`, the source-facing localized module `(𝒮⁻¹ℱ)^#[J]` is canonically isomorphic to
the intrinsic sheaf-module tensor
`((𝒮⁻¹O)^#[J])|_O ⊗_{\mathcal O} \mathcal F`. -/
noncomputable abbrev sheafifiedLocalizedModuleIsoTensor
    (J : GrothendieckTopology C) {O : Sheaf J CommRingCat.{max u v}}
    (𝒮 : SubmonoidPresheaf O.obj) [MonoidalCategory (ringedSiteModuleCategory J O)]
    (ℱ : ringedSiteModuleCategory J O) :
    (restrictionAlong 𝒮.toSheafifiedLocalizationPresheaf).obj
        ((𝒮⁻¹ℱ)^#[J]) ≅
      𝒮.sheafifiedLocalizedStructureModuleOverBase J ⊗ ℱ :=
  sheafifiedLocalizedModuleIsoSheafifiedTensor J 𝒮 ℱ ≪≫
    moduleSheafificationTensorIso J 𝒮.localizedStructureModulePresheafOverBase ℱ ≪≫
    MonoidalCategory.tensorIso (Iso.refl _) (sheafificationCounitIso ℱ)

end Sheaf

end SubmonoidPresheaf
end Presheaf
end CategoryTheory

open scoped LocalizedPresheaf CategoryTheory.Presheaf.SubmonoidPresheaf.SheafifiedLocalizedModule

section SheafifiedLocalizedModuleNotation

open CategoryTheory.Presheaf.SubmonoidPresheaf

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J O)]
variable (𝒮 : CategoryTheory.Presheaf.SubmonoidPresheaf O.obj)
variable (ℱ : ringedSiteModuleCategory J O)

/- The source-facing owner is used on the theorem surface in the textbook notation
`(𝒮⁻¹ℱ)^#[J]`. -/
set_option linter.hashCommand false in
#check
  (𝒮⁻¹ℱ)^#[J]

/- The sheafified tensor comparison is stated on the theorem surface using the source-facing owner,
viewed over `O` by restriction of scalars. -/
set_option linter.hashCommand false in
#check
  𝒮.sheafifiedLocalizedStructureModuleOverBase J

set_option linter.hashCommand false in
#check
  𝒮.sheafifiedLocalizedModuleIsoTensor J ℱ

end SheafifiedLocalizedModuleNotation

namespace TopCat.Presheaf
namespace SubmonoidPresheaf

variable {X : TopCat.{u}}

local notation "J" => Opens.grothendieckTopology X

open CategoryTheory.Presheaf.SubmonoidPresheaf

section Sheaf

variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective CommRingCat.{u}]
variable {𝒪 : X.Sheaf CommRingCat.{u}} (𝒮 : CategoryTheory.Presheaf.SubmonoidPresheaf 𝒪.obj)
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable (ℱ : ringedSiteModuleCategory J 𝒪)

local notation "ModX" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for the topological-space specialization of Lemma 17.27.2:
- primary domain: sheafification of the localized module presheaf on a ringed topological space;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizedModulePresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.sheafifiedLocalizedModule`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizedModulePresheafOverBaseIsoTensor`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.toSheafifiedLocalizationPresheaf`,
  `moduleSheafification`,
  `moduleTensor`,
  `PresheafOfModules.sheafificationAdjunction`;
- best owner abstraction: the presheaf owner and tensor bridge remain the general site-level
  declarations on `𝒮`; the source-facing sheaf owner is
  `(𝒮⁻¹ℱ)^#[J]`, owned by
  `CategoryTheory.Presheaf.SubmonoidPresheaf.sheafifiedLocalizedModule`; the `TopCat` layer should
  only record its `\mathcal O_X`-linear bridge and tensor comparison;
- primitive data: a sheaf of commutative rings `𝒪`, a multiplicative subpresheaf
  `𝒮 : SubmonoidPresheaf 𝒪.obj`, and a sheaf of `𝒪`-modules `ℱ`;
- derived API: the source-facing sheafified localized module `(𝒮⁻¹ℱ)^#[J]` and the `𝒪`-linear
  tensor comparison obtained by restricting scalars and sheafifying the presheaf-level
  comparison.

Source/core/bridge triage:
- `source-facing`: the sheafified localized module `(𝒮⁻¹ℱ)^#[J]`;
- `core/canonical`: the general site-level owners
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizedModulePresheaf` and
  `CategoryTheory.Presheaf.SubmonoidPresheaf.sheafifiedLocalizedModule`;
- `bridge/view`: the restricted-scalars identification used internally to form the general
  sheafified tensor comparison, specialized here to `J = Opens.grothendieckTopology X`.

This section is therefore only a specialization layer. The presheaf localization owner and its
sheafified owner live at the general site-level namespace and are reused here directly on `𝒮`. -/

end Sheaf

end SubmonoidPresheaf
end TopCat.Presheaf
