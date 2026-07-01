import Mathlib
import stacks_project.Chap15.Lemma_15_90_1
import stacks_project.Chap18.Lemma_18_28_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SheafOfModules

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.28.16:
- primary domain: same-site change of rings for sheaves of modules, with flatness owned by
  `SheafOfModules.RingedSite.IsFlatHom` and the canonical base-change morphism owned by the
  pullback/pushforward adjunction for `ringedSiteStructureMap α`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlatHom`,
  `ringedSiteStructureMap`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `Ideal.quotientMap`,
  `CategoryTheory.Subobject.arrow`;
- best owner abstraction: the ideal-sheaf side should be organized around the intrinsic owner
  `I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪))`, with its sectionwise ideals derived from
  `I.arrow`, while the conclusion should remain the sheaf-level `IsIso` statement for the
  adjunction unit at `ℱ`;
- primitive data: a morphism `α : 𝒪 ⟶ 𝒪'`, an ideal sheaf
  `I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪))`, and an `\mathcal O`-module `ℱ`;
- derived API: the ideal of sections cut out by `I` on each object, the sectionwise quotient-map
  hypothesis, and the sectionwise annihilation-by-a-power predicate.

Source/core/bridge triage:
- `source-facing`: the textbook base-change map
  `id ⊗ 1 : \mathcal F \to \mathcal F \otimes_{\mathcal O} \mathcal O'`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlatHom α`,
  `SheafOfModules.pullbackPushforwardAdjunction (ringedSiteStructureMap α)`, and the structure
  sheaf owner `SheafOfModules.unit (ringSheaf J 𝒪)` together with its subobjects;
- `bridge/view`: the sectionwise ideal `idealSectionIdeal I U`, derived from the subobject owner
  `I`, together with the induced quotient maps modulo that ideal.
-/

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}}

/-- The ideal of sections over `U` cut out by an ideal sheaf
`I : \operatorname{Sub}(\mathcal O)`. -/
def idealSectionIdeal
    (I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪)))
    (U : Cᵒᵖ) : Ideal ((ringSheaf J 𝒪).obj.obj U) :=
  { carrier := Set.range fun s : (I : SheafOfModules (ringSheaf J 𝒪)).val.obj U ↦
      (Hom.val I.arrow).app U s
    zero_mem' := ⟨0, by simpa using ((Hom.val I.arrow).app U).hom.map_zero⟩
    add_mem' := by
      rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      exact ⟨x + y, by simpa using ((Hom.val I.arrow).app U).hom.map_add x y⟩
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      exact ⟨r • x, by simpa using ((Hom.val I.arrow).app U).hom.map_smul r x⟩ }

/-- An `\mathcal O`-module is annihilated by `\mathcal I^n` when, on every object of the site,
the `n`th power of the ideal of sections cut out by `I` acts trivially on the corresponding
module of sections. -/
abbrev IsAnnihilatedByIdealSheafPower
    (I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪)))
    (n : ℕ) (ℱ : SheafOfModules (ringSheaf J 𝒪)) : Prop :=
  ∀ U : Cᵒᵖ, idealSectionIdeal I U ^ n ≤
    Module.annihilator ((ringSheaf J 𝒪).obj.obj U) (ℱ.val.obj U)

-- Proof sketch: evaluate the sheaf-level base-change unit at each object `U`. The flatness
-- hypothesis is expressed by the chapter owner `IsFlatHom α`; the quotient and annihilation
-- assumptions are stated objectwise using the derived section ideals from `I`. Apply the module
-- statement from Lemma `15.90.2` to each section ring map `(α.hom.app U).hom`, then reassemble
-- these objectwise isomorphisms into the sheaf-level adjunction unit.
/-- Lemma 18.28.16: let `\mathcal C` be a site, let `\mathcal O \to \mathcal O'` be a flat
homomorphism of sheaves of rings, and let `\mathcal I \subset \mathcal O` be an ideal sheaf,
formalized by a subobject `I : \operatorname{Sub}(\mathcal O)`, such that
`\mathcal O/\mathcal I \to \mathcal O'/\mathcal I \mathcal O'` is an isomorphism. If an
`\mathcal O`-module `\mathcal F` is annihilated by `\mathcal I^n` for some `n ≥ 0`, then the
canonical base-change morphism
`id ⊗ 1 : \mathcal F \to \mathcal F \otimes_{\mathcal O} \mathcal O'`, formalized here as the
unit of the pullback/pushforward adjunction for `ringedSiteStructureMap α`, is an isomorphism. -/
theorem tensorBaseChangeUnit_isIso_of_isFlatHom_of_quotientMap_bijective_of_annihilated
    (α : 𝒪 ⟶ 𝒪')
    (hflat : IsFlatHom α)
    (I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪)))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (hquot : ∀ U : Cᵒᵖ,
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map ((α.hom.app U).hom) (idealSectionIdeal I U))
          ((α.hom.app U).hom)
          Ideal.le_comap_map))
    (hpow : ∃ n : ℕ, IsAnnihilatedByIdealSheafPower I n ℱ) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction (ringedSiteStructureMap α)).unit.app ℱ) :=
  sorry

end SheafOfModules.RingedSite
