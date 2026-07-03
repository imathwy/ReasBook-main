import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_11_1 (from Chap18) -/
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

/-! ### Lemma_18_11_2 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J RingCat.{u}]
variable [J.WEqualsLocallyBijective RingCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{u})

/- Lemma 18.11.2: for a presheaf of rings `𝒪` on a site `(C, J)`, the sheafification functor
`PMod(𝒪) ⥤ Mod(𝒪^\#)` is exact. The canonical owner-level form is the bundled exact functor
`ExactFunctor.of (PresheafOfModules.sheafification (toSheafify J 𝒪))`. -/
#check
  (ExactFunctor.of (PresheafOfModules.sheafification (toSheafify J 𝒪)) :
    PresheafOfModules 𝒪 ⥤ₑ
      SheafOfModules ((presheafToSheaf J RingCat.{u}).obj 𝒪))

end

/-! ### Lemma_18_11_3 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪₁ 𝒪₂ : Sheaf J RingCat.{u}}
variable (α : 𝒪₁ ⟶ 𝒪₂) (𝒢 : SheafOfModules 𝒪₁) (ℱ : SheafOfModules 𝒪₂)

private abbrev ringSheafHomOverId :
    𝒪₁ ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{u} J J).obj 𝒪₂ :=
  α

/- Domain-style sampling for Lemma 18.11.3:
- primary domain: change of rings for sheaves of modules on one ringed site;
- sampled owner declarations:
  `SheafOfModules.restrictScalars`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: `SheafOfModules.pullbackPushforwardAdjunction α`;
- primitive data: the ring-sheaf morphism `α : 𝒪₁ ⟶ 𝒪₂`;
- same-site bridge: the canonical identity-site transport `ringSheafHomOverId α`;
- derived API: the specialized Hom-set equivalence, where the same-site functor
  `SheafOfModules.pushforward (ringSheafHomOverId α)` is restriction of scalars.

Source/core/bridge triage:
- `source-facing`: the Hom-bijection for change of rings on one site;
- `core/canonical`: the adjunction
  `SheafOfModules.pullback (ringSheafHomOverId α) ⊣
    SheafOfModules.pushforward (ringSheafHomOverId α)`;
- `bridge/view`: the specialization of `.homEquiv` to `𝒢` and `ℱ`.

This file is therefore a bridge/view item, so the owner adjunction should be recalled directly and
the displayed Hom-bijection should stay a thin specialization. -/

/- Lemma 18.11.3, owner form: for sheaves of modules on a ringed site, extension of scalars along
`α : 𝒪₁ ⟶ 𝒪₂` is left adjoint to the same-site pushforward functor, i.e. to restriction of
scalars along `α`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.11.3: the adjunction for change of rings along `α : 𝒪₁ ⟶ 𝒪₂` induces the canonical
same-site Hom-set equivalence
`Hom_{𝒪₁}(𝒢, \mathrm{res}_α(ℱ)) ≃ Hom_{𝒪₂}(α^* 𝒢, ℱ)`,
where `α^*` is `SheafOfModules.pullback α` and the same-site `pushforward α` is restriction of
scalars. -/
#check
  ((SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId α)).homEquiv 𝒢 ℱ).symm

/-! ### Lemma_18_11_4 (from Chap18) -/
open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 𝒪' : Sheaf J RingCat.{u}}

/- Domain-style sampling for Lemma 18.11.4:
- primary domain: change of rings for sheaves of modules on a ringed site;
- sampled owner declarations:
  `Sheaf.isLocallySurjective_iff_epi'`,
  `SheafOfModules.restrictScalars`,
  `PresheafOfModules.restrictHomEquivOfIsLocallySurjective`,
  `SheafOfModules.fullyFaithfulForget`,
  `Functor.FullyFaithful.map_bijective`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that restriction of scalars along an epimorphism of sheaves of
  rings is fully faithful;
- `core/canonical`: the functor `SheafOfModules.restrictScalars α`, together with local
  surjectivity of the ring-sheaf map;
- `bridge/view`: the induced bijectivity on each Hom-set.

Primitive vs derived API:
- primitive data: the ring-sheaf epimorphism `α : 𝒪 ⟶ 𝒪'`;
- owner statement: `(SheafOfModules.restrictScalars α).FullyFaithful`;
- derived companion: bijectivity of the induced map on each Hom-set, obtained from the existing
  locally-surjective change-of-rings Hom-equivalence.

The canonical owner route is: pass from `Epi α` to local surjectivity of `α.hom` via
`Sheaf.isLocallySurjective_iff_epi'`, then use the existing
change-of-rings Hom-equivalence and the fully faithful forget functor. -/

private theorem isLocallySurjective_hom_of_epi (α : 𝒪 ⟶ 𝒪') [Epi α] :
    Presheaf.IsLocallySurjective J α.hom := by
  sorry

/-- Lemma 18.11.4: if `𝒪 ⟶ 𝒪'` is an epimorphism of sheaves of rings on a site, then the
restriction functor `Mod(𝒪') ⥤ Mod(𝒪)` is fully faithful. Equivalently, for `𝒪'`-modules
`𝒢₁` and `𝒢₂`, morphisms `𝒢₁ ⟶ 𝒢₂` over `𝒪'` are exactly the morphisms between the same
underlying sheaves viewed as `𝒪`-modules. -/
-- Proof sketch: use `Sheaf.isLocallySurjective_iff_epi'` to obtain local surjectivity of `α`,
-- then apply the existing presheaf-level
-- change-of-rings equivalence
-- `PresheafOfModules.restrictHomEquivOfIsLocallySurjective` and lift back to sheaves via the
-- fully faithful forget functor `SheafOfModules.fullyFaithfulForget`.
noncomputable def sheaf_of_modules_restrict_scalars_fullyFaithful
    (α : 𝒪 ⟶ 𝒪') [Epi α] :
    (SheafOfModules.restrictScalars α).FullyFaithful where
  preimage {M₁ M₂} g := by
    letI : Presheaf.IsLocallySurjective J α.hom := isLocallySurjective_hom_of_epi α
    exact (SheafOfModules.fullyFaithfulForget 𝒪').preimage <|
      (PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom
        M₂.isSheaf).symm g.val
  map_preimage := by
    intro M₁ M₂ g
    letI : Presheaf.IsLocallySurjective J α.hom := isLocallySurjective_hom_of_epi α
    apply (SheafOfModules.fullyFaithfulForget 𝒪).map_injective
    rfl
  preimage_map := by
    intro M₁ M₂ g
    letI : Presheaf.IsLocallySurjective J α.hom := isLocallySurjective_hom_of_epi α
    apply (SheafOfModules.fullyFaithfulForget 𝒪').map_injective
    rfl

/-- Restriction of scalars along an epimorphism of sheaves of rings induces a bijection on
morphisms between sheaves of `𝒪'`-modules. -/
theorem sheaf_of_modules_restrict_scalars_map_bijective
    (α : 𝒪 ⟶ 𝒪') [Epi α] (𝒢₁ 𝒢₂ : SheafOfModules 𝒪') :
    Function.Bijective
      (((SheafOfModules.restrictScalars α).map :
        (𝒢₁ ⟶ 𝒢₂) →
          ((SheafOfModules.restrictScalars α).obj 𝒢₁ ⟶
            (SheafOfModules.restrictScalars α).obj 𝒢₂))) := by
  simpa using
    (sheaf_of_modules_restrict_scalars_fullyFaithful α).map_bijective 𝒢₁ 𝒢₂
