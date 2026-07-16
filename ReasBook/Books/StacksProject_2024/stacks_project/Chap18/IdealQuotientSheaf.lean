import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_90_1
import StacksProject_2024.stacks_project.Chap18.IdealSectionIdeal
import StacksProject_2024.stacks_project.Chap18.Lemma_18_34_5
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory

open CategoryTheory Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for the ringed-site quotient-by-ideal owner:
- primary domain: quotient sheaves of rings on a fixed site and the induced quotient map under
  same-site change of rings;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `unitModule`,
  `ringSheaf`,
  `ringSheafMap`,
  `quotientMapModIdeal`;
- best owner abstraction: the source-facing object is the quotient ring sheaf
  `quotientRingSheaf I`, with the target-side quotient `targetQuotientRingSheaf α I` and the
  canonical map `quotientRingSheafMap α I`; the sectionwise ideals are derived from the ideal
  sheaf inclusion `I.arrow`;
- primitive data: a site `(\mathcal C, J)`, a structure sheaf `\mathcal O`, an ideal sheaf
  `I : \operatorname{Sub}(\mathcal O)`, and optionally a same-site ring map
  `α : \mathcal O \to \mathcal O'`;
- derived API: the sectionwise ideals `idealSectionIdeal I U`, the quotient sheaf
  `quotientRingSheaf I`, the target quotient `targetQuotientRingSheaf α I`, the quotient map
  `quotientRingSheafMap α I`, and the nilpotence predicate
  `IsAnnihilatedByIdealPower I ℱ`.

Source/core/bridge triage:
- `source-facing`: the quotient sheaf `\mathcal O / \mathcal I` and the source-side nilpotence
  condition that some power of `\mathcal I` annihilates `\mathcal F`;
- `core/canonical`: `Subobject (unitModule J 𝒪)`, `Subobject.arrow`, `ringSheaf`, and
  `quotientMapModIdeal`;
- `bridge/view`: the sectionwise ideal family cut out by `I` and the target-side quotient by the
  extended ideal along `α`.
-/

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- Restriction maps preserve the ideals of sections cut out by an ideal sheaf. -/
private theorem idealSectionIdeal_le_comap
    (I : Subobject (unitModule J 𝒪)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    idealSectionIdeal I U ≤
      (idealSectionIdeal I V).comap (𝒪.obj.map f).hom := by
  sorry

/-- The quotient presheaf of commutative rings `\mathcal O / \mathcal I`. -/
private noncomputable def quotientCommRingPresheaf
    (I : Subobject (unitModule J 𝒪)) :
    Cᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (𝒪.obj.obj U ⧸ idealSectionIdeal I U)
  map {U V} f := CommRingCat.ofHom <|
    Ideal.quotientMap (idealSectionIdeal I V) (𝒪.obj.map f).hom
      (idealSectionIdeal_le_comap I f)
  map_id U := by
    sorry
  map_comp f g := by
    sorry

/-- The quotient sheaf of commutative rings `\mathcal O / \mathcal I`. -/
noncomputable def quotientCommRingSheaf
    (I : Subobject (unitModule J 𝒪)) :
    Sheaf J CommRingCat.{u} :=
  ⟨quotientCommRingPresheaf I, by sorry⟩

/-- The canonical quotient projection `\mathcal O \to \mathcal O / \mathcal I` as a morphism of
sheaves of commutative rings. -/
noncomputable def quotientCommRingSheafProjection
    (I : Subobject (unitModule J 𝒪)) :
    𝒪 ⟶ quotientCommRingSheaf I where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom (Ideal.Quotient.mk _)
      naturality := by
        intro U V f
        ext x
        rfl }

/-- The quotient ring sheaf `\mathcal O / \mathcal I`. -/
abbrev quotientRingSheaf
    (I : Subobject (unitModule J 𝒪)) :
    Sheaf J RingCat.{u} :=
  ringSheaf J (quotientCommRingSheaf I)

/-- The canonical quotient projection `\mathcal O \to \mathcal O / \mathcal I` in its
`RingCat`-valued form. -/
abbrev quotientRingSheafProjection
    (I : Subobject (unitModule J 𝒪)) :
    ringSheaf J 𝒪 ⟶ quotientRingSheaf I :=
  ringSheafMap (quotientCommRingSheafProjection I)

/-- Restriction maps preserve the sectionwise powers `\mathcal I(U)^n`. -/
private theorem idealPowerSectionIdeal_le_comap
    (I : Subobject (unitModule J 𝒪)) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    idealSectionIdeal I U ^ n ≤
      (idealSectionIdeal I V ^ n).comap (𝒪.obj.map f).hom := by
  exact
    (Ideal.pow_right_mono (idealSectionIdeal_le_comap I f) n).trans
      (Ideal.le_comap_pow (f := (𝒪.obj.map f).hom) (K := idealSectionIdeal I V) n)

section IdealPowerQuotient

variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]

/-- The quotient presheaf of commutative rings `\mathcal O / \mathcal I^n`. -/
noncomputable def idealPowerQuotientCommRingPresheaf
    (I : Subobject (unitModule J 𝒪)) (n : ℕ) :
    Cᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (𝒪.obj.obj U ⧸ idealSectionIdeal I U ^ n)
  map {U V} f := CommRingCat.ofHom <|
    Ideal.quotientMap (idealSectionIdeal I V ^ n) (𝒪.obj.map f).hom
      (idealPowerSectionIdeal_le_comap I f n)
  map_id U := by
    ext r
    simp [Ideal.quotientMap_mk]
  map_comp f g := by
    ext r
    simp [Ideal.quotientMap_mk, RingHom.comp_apply, Functor.map_comp]

/-- The quotient sheaf of commutative rings `\mathcal O / \mathcal I^n`. -/
noncomputable def idealPowerQuotientCommRingSheaf
    (I : Subobject (unitModule J 𝒪)) (n : ℕ) :
    Sheaf J CommRingCat.{u} :=
  PresheafOfModules.commRingSheafification J (idealPowerQuotientCommRingPresheaf I n)

/-- The presheaf-level quotient projection `\mathcal O \to \mathcal O / \mathcal I^n`. -/
private noncomputable def idealPowerQuotientCommRingPresheafProjection
    (I : Subobject (unitModule J 𝒪)) (n : ℕ) :
    𝒪.obj ⟶ idealPowerQuotientCommRingPresheaf I n where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk _)
  naturality := by
    intro U V f
    ext x
    rfl

/-- The canonical quotient projection `\mathcal O \to \mathcal O / \mathcal I^n`. -/
noncomputable def idealPowerQuotientCommRingSheafProjection
    (I : Subobject (unitModule J 𝒪)) (n : ℕ) :
    𝒪 ⟶ idealPowerQuotientCommRingSheaf I n :=
  { hom :=
      idealPowerQuotientCommRingPresheafProjection I n ≫
        (show idealPowerQuotientCommRingPresheaf I n ⟶
            (idealPowerQuotientCommRingSheaf I n).obj from
          CategoryTheory.toSheafify J (idealPowerQuotientCommRingPresheaf I n)) }

/-- The quotient ring sheaf `\mathcal O / \mathcal I^n`. -/
abbrev idealPowerQuotientRingSheaf
    (I : Subobject (unitModule J 𝒪)) (n : ℕ) :
    Sheaf J RingCat.{u} :=
  ringSheaf J (idealPowerQuotientCommRingSheaf I n)

/-- The canonical quotient projection `\mathcal O \to \mathcal O / \mathcal I^n` in its
`RingCat`-valued form. -/
abbrev idealPowerQuotientRingSheafProjection
    (I : Subobject (unitModule J 𝒪)) (n : ℕ) :
    ringSheaf J 𝒪 ⟶ idealPowerQuotientRingSheaf I n :=
  ringSheafMap (idealPowerQuotientCommRingSheafProjection I n)

end IdealPowerQuotient

/-- The sectionwise extended ideal on `\mathcal O'` cut out by the image of `\mathcal I` under
`\alpha : \mathcal O \to \mathcal O'`. -/
private noncomputable def targetIdealSectionIdeal
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪))
    (U : Cᵒᵖ) : Ideal (𝒪'.obj.obj U) :=
  Ideal.map ((α.hom.app U).hom) (idealSectionIdeal I U)

/-- Restriction maps preserve the sectionwise extended ideals on the target sheaf. -/
private theorem targetIdealSectionIdeal_le_comap
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    targetIdealSectionIdeal α I U ≤
      (targetIdealSectionIdeal α I V).comap (𝒪'.obj.map f).hom := by
  sorry

/-- The quotient presheaf of commutative rings `\mathcal O' / \mathcal I \mathcal O'`
attached to `\alpha : \mathcal O \to \mathcal O'`. -/
private noncomputable def targetQuotientCommRingPresheaf
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪)) :
    Cᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (𝒪'.obj.obj U ⧸ targetIdealSectionIdeal α I U)
  map {U V} f := CommRingCat.ofHom <|
    Ideal.quotientMap (targetIdealSectionIdeal α I V) (𝒪'.obj.map f).hom
      (targetIdealSectionIdeal_le_comap α I f)
  map_id U := by
    sorry
  map_comp f g := by
    sorry

/-- The quotient sheaf of commutative rings `\mathcal O' / \mathcal I \mathcal O'` attached to
`\alpha : \mathcal O \to \mathcal O'`. -/
private noncomputable def targetQuotientCommRingSheaf
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪)) :
    Sheaf J CommRingCat.{u} :=
  ⟨targetQuotientCommRingPresheaf α I, by sorry⟩

/-- The target quotient ring sheaf `\mathcal O' / \mathcal I \mathcal O'` attached to
`\alpha : \mathcal O \to \mathcal O'`. -/
abbrev targetQuotientRingSheaf
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪)) :
    Sheaf J RingCat.{u} :=
  ringSheaf J (targetQuotientCommRingSheaf α I)

/-- The canonical quotient map `\mathcal O / \mathcal I \to \mathcal O' / \mathcal I
\mathcal O'` induced by `\alpha : \mathcal O \to \mathcal O'`, in its commutative-ring-valued
form. -/
private noncomputable def quotientCommRingSheafMap
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪)) :
    quotientCommRingSheaf I ⟶ targetQuotientCommRingSheaf α I where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom <|
        quotientMapModIdeal ((α.hom.app U).hom) (idealSectionIdeal I U)
      naturality := by
        intro U V f
        sorry }

/-- The canonical quotient map `\mathcal O / \mathcal I \to \mathcal O' / \mathcal I
\mathcal O'` induced by `\alpha : \mathcal O \to \mathcal O'`. -/
abbrev quotientRingSheafMap
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪)) :
    quotientRingSheaf I ⟶ targetQuotientRingSheaf α I :=
  ringSheafMap (quotientCommRingSheafMap α I)

/-- Some power of the ideal sheaf `\mathcal I` annihilates the sheaf `\mathcal F`. -/
def IsAnnihilatedByIdealPower
    (I : Subobject (unitModule J 𝒪))
    (ℱ : Mod(𝒪)) : Prop :=
  ∃ n : ℕ, ∀ U : Cᵒᵖ,
    idealSectionIdeal I U ^ n ≤
      Module.annihilator (𝒪.obj.obj U) (ℱ.val.obj U)

end SheafOfModules.RingedSite
