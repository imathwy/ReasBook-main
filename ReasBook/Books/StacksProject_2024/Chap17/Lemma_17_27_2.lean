import Mathlib
import StacksProject_2024.Chap17.Lemma_17_27_1
import StacksProject_2024.Chap18.Lemma_18_26_1

-- Declarations for this item will be appended below by the statement pipeline.

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
