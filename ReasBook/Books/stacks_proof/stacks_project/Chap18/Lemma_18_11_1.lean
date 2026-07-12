import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open PresheafOfModules

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J RingCat.{u}]
variable [J.WEqualsLocallyBijective RingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.11.1:
- primary domain: sheafification of presheaves of modules on a Grothendieck site;
- sampled owner API:
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`,
  `PresheafOfModules.sheafificationCompToSheaf`,
  `CategoryTheory.sheafificationAdjunction`.

Source/core/bridge triage:
- `source-facing`: the Stacks-style unique factorization through `ℱ ⟶ ℱ^#`;
- `core/canonical`: the module-sheafification adjunction along `toSheafify J 𝒪`;
- `bridge/view`: the `∃!` reformulation of the adjunction Hom-equivalence.

The additive compatibility in part (1) is already an exact upstream owner theorem, so the local
duplicate should be removed in favor of direct recall. Part (2) remains as the thin source-facing
bridge.
-/

/- Lemma 18.11.1 (1): the compatibility of the sheafified `𝒪^#`-module with the sheafification of
the underlying additive presheaf is exactly the canonical unit-compatibility theorem for the
module-sheafification adjunction. -/
recall PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app

section

variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (ℱ : PresheafOfModules 𝒪)

-- Proof sketch: apply the adjunction
-- `PresheafOfModules.sheafification ⊣ SheafOfModules.forget ⋙ restrictScalars` along
-- `toSheafify J 𝒪`; the hom-set equivalence turns a presheaf morphism `ℱ ⟶ 𝒢` into the unique
-- `𝒪^#`-linear morphism `ℱ^# ⟶ 𝒢` whose composite with the unit is the original map.
/-- Lemma 18.11.1 (2): for a sheaf of `𝒪^#`-modules `𝒢`, every morphism of presheaves of
`𝒪`-modules from `ℱ` to the restriction of `𝒢` factors uniquely through the canonical map
`ℱ ⟶ ℱ^#` by a morphism of `𝒪^#`-modules. -/
@[stacks 03CY]
theorem modulePresheafSheafification_factorsUniquely
    (𝒢 : SheafOfModules ((presheafToSheaf J RingCat.{u}).obj 𝒪))
    (η : ℱ ⟶
      (SheafOfModules.forget ((presheafToSheaf J RingCat.{u}).obj 𝒪) ⋙
        restrictScalars (toSheafify J 𝒪)).obj 𝒢) :
    ∃! γ : (sheafification (toSheafify J 𝒪)).obj ℱ ⟶ 𝒢,
      (sheafificationAdjunction (toSheafify J 𝒪)).unit.app ℱ ≫
          (SheafOfModules.forget ((presheafToSheaf J RingCat.{u}).obj 𝒪) ⋙
            restrictScalars (toSheafify J 𝒪)).map γ =
        η := by
  let e : ((sheafification (toSheafify J 𝒪)).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶
        (SheafOfModules.forget ((presheafToSheaf J RingCat.{u}).obj 𝒪) ⋙
          restrictScalars (toSheafify J 𝒪)).obj 𝒢) :=
    (sheafificationAdjunction (toSheafify J 𝒪)).homEquiv ℱ 𝒢
  refine ⟨e.symm η, ?_, ?_⟩
  · change e (e.symm η) = η
    exact Equiv.apply_symm_apply e η
  · intro γ hγ
    exact ((Equiv.symm_apply_eq e).2 hγ.symm).symm

end

end
