import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
