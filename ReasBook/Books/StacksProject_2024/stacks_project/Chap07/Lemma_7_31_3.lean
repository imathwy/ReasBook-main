import Mathlib
import StacksProject_2024.Chap07.Definition_7_15_1_Topoi
import StacksProject_2024.Chap07.Lemma_7_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.31.3:
- primary domain: slice-topos inverse-image functors built from a localized geometric morphism and
  a canonical pullback functor in `CategoryTheory.Over`, bundled at the strongest owner level
  available here;
- sampled owner declarations:
  `LeftExactAdjunction.localization`,
  `LeftExactAdjunction.localization_inverseImage_obj`,
  `Over.pullback`,
  `Over.pullbackComp`,
  `Over.pullbackCongr`;
- best owner abstraction:
  the chapter owner for the localized slice morphism is already
  `LeftExactAdjunction.localization`, while the additional map
  `s : ℱ ⟶ (f⁻¹).obj 𝒢` contributes only the canonical slice pullback owner `Over.pullback s`.
  The correct public surface is therefore the direct composite
  `((f.localization 𝒢).inverseImage ⋙ Over.pullback s)`, while the left exactness packaging is the
  derived canonical wrapper `LeftExactFunctor.of` and should not be given a second owner name;
- primitive data vs derived API:
  primitive data are the morphism of topoi `f`, the sheaves `𝒢`, `ℱ`, and the comparison map `s`;
  the source-facing inverse-image functor is the direct composite above, while its left-exact
  packaging, objectwise pullback formula, and base-change comparison are derived API from the
  owners above;
- source/core/bridge triage:
  `source-facing`: the localized inverse-image functor
    `((f.localization 𝒢).inverseImage ⋙ Over.pullback s) : Over 𝒢 ⥤ Over ℱ`;
  `core/canonical`: `LeftExactAdjunction.localization`, `LeftExactFunctor.of`, and `Over.pullback`;
  `bridge/view`: the underlying composite functor and its base-change comparison.

This file therefore works directly with the canonical composite
`((f.localization 𝒢).inverseImage ⋙ Over.pullback s)`, and leaves the left-exact wrapper as the
owner-level packaging supplied by `LeftExactFunctor.of` when needed.
-/

/-
Lemma 7.31.3: for a morphism of topoi `f : Sh(𝒞) ⟶ Sh(𝒟)` and a sheaf morphism
`s : ℱ ⟶ f^{-1} 𝒢`, the inverse-image functor of the induced localized morphism
`Sh(𝒞)/ℱ ⟶ Sh(𝒟)/𝒢` is the canonical composite of the localized inverse image from
Lemma 7.31.1 with the relocalization pullback from Lemma 7.30.6. Its left-exact packaging is
obtained directly by `LeftExactFunctor.of`, so no separate owner alias is introduced here.
-/
#check
  (fun
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    (s : ℱ ⟶ (f⁻¹).obj 𝒢) ↦
      show Over 𝒢 ⥤ₗ Over ℱ from
        LeftExactFunctor.of ((f.localization 𝒢).inverseImage ⋙ Over.pullback s))

-- Proof sketch: use that the localized inverse image from Lemma 7.31.1 is
-- `(f.localization 𝒢).inverseImage`, and then apply the objectwise description of
-- `Over.pullback s`.
/-- The localized inverse-image composite sends `(ℋ ⟶ 𝒢)` to the pullback
`(f^{-1} ℋ ×_{f^{-1} 𝒢} ℱ ⟶ ℱ)`. -/
@[simp] theorem localization_inverseImage_pullback_obj
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (ℋ : Over 𝒢) :
    ((f.localization 𝒢).inverseImage ⋙ Over.pullback s).obj ℋ =
      Over.mk (pullback.snd ((f⁻¹).map ℋ.hom) s) := by
  change (Over.pullback s).obj ((f.localization 𝒢).inverseImage.obj ℋ) =
      Over.mk (pullback.snd ((f⁻¹).map ℋ.hom) s)
  rw [LeftExactAdjunction.localization_inverseImage_obj]
  rfl

-- Proof sketch: this is the naturality step for the pullback-preservation comparison of `f⁻¹`
-- used in `localization_inverseImage_pullback_iso`.
private noncomputable def localization_inverseImage_pullback_iso_app
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    (A : Over 𝒢) :
    ((Over.pullback b ⋙ Over.post (f⁻¹)).obj A) ≅
      ((Over.post (f⁻¹) ⋙ Over.pullback ((f⁻¹).map b)).obj A) := by
  refine Over.isoMk (PreservesPullback.iso f.inverseImage A.hom b) ?_
  exact PreservesPullback.iso_hom_snd f.inverseImage A.hom b

-- Proof sketch: this is the naturality step for the objectwise pullback-preservation comparison
-- of `f⁻¹` used in `localization_inverseImage_pullback_iso`.
private theorem localization_inverseImage_pullback_iso_naturality
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    {A B : Over 𝒢}
    (g : A ⟶ B) :
    ((Over.pullback b ⋙ Over.post (f⁻¹)).map g ≫
        (localization_inverseImage_pullback_iso_app f b B).hom).left =
      (((localization_inverseImage_pullback_iso_app f b A).hom ≫
        (Over.post (f⁻¹) ⋙ Over.pullback ((f⁻¹).map b)).map g)).left := by
  sorry

-- Proof sketch: the equality `s' ≫ (f⁻¹).map b = a ≫ s` identifies the two pullback functors on
-- the nose; the dependent instance bookkeeping is discharged in this private theorem.
private theorem pullbackCongr_of_localization_square
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    {ℱ' : Sheaf JC (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ (f⁻¹).obj 𝒢')
    (hs : s' ≫ (f⁻¹).map b = a ≫ s) :
    Over.pullback (s' ≫ (f⁻¹).map b) = Over.pullback (a ≫ s) := by
  sorry

-- Proof sketch: this is the pullback-preservation comparison for `f⁻¹` rewritten as a natural
-- isomorphism between slice pullback functors and localized inverse images.
private noncomputable def localization_inverseImage_pullback_iso
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    (b : 𝒢' ⟶ 𝒢) :
    Over.pullback b ⋙ (f.localization 𝒢').inverseImage ≅
      (f.localization 𝒢).inverseImage ⋙ Over.pullback ((f⁻¹).map b) := by
  change Over.pullback b ⋙ Over.post (f⁻¹) ≅ Over.post (f⁻¹) ⋙ Over.pullback ((f⁻¹).map b)
  refine NatIso.ofComponents (fun A ↦ ?_) ?_
  · exact localization_inverseImage_pullback_iso_app f b A
  · intro A B g
    apply Over.OverMorphism.ext
    exact localization_inverseImage_pullback_iso_naturality f b g

-- Proof sketch: first commute `Over.pullback b` past the localized inverse image using the
-- pullback-preservation comparison for `f⁻¹`, viewed through the objectwise formula from
-- Lemma `7.31.1`. Then compare the remaining iterated pullbacks by
-- `Over.pullbackComp`, and use `Over.pullbackCongr hs` for the equality
-- `s' ≫ (f⁻¹).map b = a ≫ s`.
/-- Base change for the localized inverse-image functor: a commutative square
`s' ≫ f^{-1}(b) = a ≫ s` induces the canonical comparison isomorphism on the corresponding slice
inverse-image functors. -/
noncomputable def localization_inverseImage_pullback_base_change_iso
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    {ℱ' : Sheaf JC (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ (f⁻¹).obj 𝒢')
    (hs : s' ≫ (f⁻¹).map b = a ≫ s) :
    Over.pullback b ⋙ (f.localization 𝒢').inverseImage ⋙ Over.pullback s' ≅
      (f.localization 𝒢).inverseImage ⋙ Over.pullback s ⋙ Over.pullback a := by
  exact
    (Functor.associator (Over.pullback b) (f.localization 𝒢').inverseImage (Over.pullback s')).symm ≪≫
      (Functor.isoWhiskerRight (localization_inverseImage_pullback_iso f b) (Over.pullback s')) ≪≫
      Functor.associator (f.localization 𝒢).inverseImage (Over.pullback ((f⁻¹).map b))
        (Over.pullback s') ≪≫
      (Functor.isoWhiskerLeft (f.localization 𝒢).inverseImage
        ((Over.pullbackComp s' ((f⁻¹).map b)).symm ≪≫
          eqToIso (pullbackCongr_of_localization_square f b a s s' hs) ≪≫
            Over.pullbackComp a s)) ≪≫
      Functor.associator (f.localization 𝒢).inverseImage (Over.pullback s) (Over.pullback a)

-- Proof sketch: this is the proposition-level companion obtained from the canonical functor
-- isomorphism above.
/-- Companion proposition-level base-change form for the localized inverse-image functor. -/
theorem localization_inverseImage_pullback_base_change
    (f : MorphismOfTopoiIn JD JC)
    {𝒢 𝒢' : Sheaf JD (Type w)}
    {ℱ : Sheaf JC (Type w)}
    {ℱ' : Sheaf JC (Type w)}
    (b : 𝒢' ⟶ 𝒢)
    (a : ℱ' ⟶ ℱ)
    (s : ℱ ⟶ (f⁻¹).obj 𝒢)
    (s' : ℱ' ⟶ (f⁻¹).obj 𝒢')
    (hs : s' ≫ (f⁻¹).map b = a ≫ s) :
    IsIsomorphic
      (Over.pullback b ⋙ (f.localization 𝒢').inverseImage ⋙ Over.pullback s')
      ((f.localization 𝒢).inverseImage ⋙ Over.pullback s ⋙ Over.pullback a) := by
  exact ⟨localization_inverseImage_pullback_base_change_iso f b a s s' hs⟩

end CategoryTheory
