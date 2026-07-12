import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe v u

namespace CategoryTheory.MonoidalClosed

/-- The source-order internal-Hom equivalence in a braided monoidal closed category, obtained from
the owner equivalence `internalHomAdjunction₂.homEquiv` by transporting across the braiding. -/
def braidedHomEquiv {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
    [MonoidalClosed A] (ℱ 𝒢 ℋ : A) :
    (ℱ ⊗ 𝒢 ⟶ ℋ) ≃ (ℱ ⟶ (ihom 𝒢).obj ℋ) :=
  ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
    (internalHomAdjunction₂.homEquiv :
      (𝒢 ⊗ ℱ ⟶ ℋ) ≃ (ℱ ⟶ (ihom 𝒢).obj ℋ))

/-- The inverse of `braidedHomEquiv` is the braiding followed by the canonical `uncurry` map. -/
theorem braidedHomEquiv_symm_apply
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    {K L M : A} (f : K ⟶ (ihom L).obj M) :
    (braidedHomEquiv K L M).symm f = (β_ K L).hom ≫ uncurry f := by
  change (β_ K L).hom ≫ uncurry f ≫ (Iso.refl M).hom = (β_ K L).hom ≫ uncurry f
  simp

private abbrev tensorLeftTensorIso {A : Type u} [Category.{v} A] [MonoidalCategory A]
    [BraidedCategory A] (K L : A) :
    tensorLeft (K ⊗ L) ≅ tensorLeft K ⋙ tensorLeft L :=
  ((tensoringLeft A).mapIso (β_ K L)) ≪≫ tensorLeftTensor L K

/-- The source-order currying isomorphism in a braided monoidal closed category. This is the
objectwise right-adjoint-uniqueness comparison between the iterated internal Hom and the internal
Hom out of the tensor product. -/
noncomputable def internalHomTensorIso {A : Type u} [Category.{v} A] [MonoidalCategory A]
    [BraidedCategory A] [MonoidalClosed A] (K L M : A) :
    (ihom K).obj ((ihom L).obj M) ≅ (ihom (K ⊗ L)).obj M :=
  let adjTensor : tensorLeft (K ⊗ L) ⊣ ihom (K ⊗ L) :=
    ihom.adjunction (K ⊗ L)
  let adjComp : tensorLeft (K ⊗ L) ⊣ ihom L ⋙ ihom K :=
    (((ihom.adjunction K).comp (ihom.adjunction L)).ofNatIsoLeft
      (tensorLeftTensorIso K L).symm)
  (Adjunction.rightAdjointUniq adjTensor adjComp).symm.app M

/-- The canonical source-order tensor/internal-Hom unit in a braided monoidal closed category,
obtained by currying the braiding `L ⊗ K ⟶ K ⊗ L`. -/
noncomputable def tensorInternalHomUnit {A : Type u} [Category.{v} A] [MonoidalCategory A]
    [BraidedCategory A] [MonoidalClosed A] (K L : A) :
    K ⟶ (ihom L).obj (K ⊗ L) :=
  curry (β_ L K).hom

/-- The canonical tensor/internal-Hom unit is the coevaluation map followed by the braiding on the
tensor factor. -/
theorem tensorInternalHomUnit_spec
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (K L : A) :
    tensorInternalHomUnit K L =
      (ihom.coev L).app K ≫ (ihom L).map (β_ L K).hom := by
  simp [tensorInternalHomUnit, MonoidalClosed.curry_eq]

/-- The canonical tensor/internal-Hom unit is natural in the left tensor factor. -/
theorem tensorInternalHomUnit_natural_left
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    {K₁ K₂ L : A} (f : K₁ ⟶ K₂) :
    CommSq f (tensorInternalHomUnit K₁ L) (tensorInternalHomUnit K₂ L)
      ((ihom L).map (f ▷ L)) := by
  refine CommSq.mk ?_
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  simp [tensorInternalHomUnit]

/-- The canonical tensor/internal-Hom unit is natural in the internal-Hom variable. -/
theorem tensorInternalHomUnit_natural_right
    {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]
    (K : A) {L₁ L₂ : A} (g : L₁ ⟶ L₂) :
    CommSq
      (tensorInternalHomUnit K L₂)
      (tensorInternalHomUnit K L₁)
      ((pre g).app (K ⊗ L₂))
      ((ihom L₁).map (K ◁ g)) := by
  refine CommSq.mk ?_
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_right]
  simp [tensorInternalHomUnit]

end CategoryTheory.MonoidalClosed

/- Domain-style sampling for Lemma 18.27.6:
- primary domain: tensor-internal-Hom adjunctions in braided monoidal closed categories;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry`,
  `MonoidalClosed.internalHomAdjunction₂.homEquiv`,
  `Adjunction.rightAdjointUniq`;
- best owner abstraction:
  the chapter owner is `CategoryTheory.MonoidalClosed.braidedHomEquiv`, whose source
  orientation `Hom(ℱ ⊗ 𝒢, ℋ) ≃ Hom(ℱ, Hom(𝒢, ℋ))` is obtained from
  `internalHomAdjunction₂.homEquiv` by transport across the braiding;
- primitive data:
  objects `ℱ 𝒢 ℋ` in a braided monoidal closed category;
- derived API:
  the source-oriented Hom-set equivalence `braidedHomEquiv` and the companion objectwise
  currying isomorphism `internalHomTensorIso`.

Source/core/bridge triage:
- `source-facing`: the source-oriented equivalence
  `(ℱ ⊗ 𝒢 ⟶ ℋ) ≃ (ℱ ⟶ (𝒢 ⟹ ℋ))`;
- `core/canonical`: `MonoidalClosed.internalHomAdjunction₂.homEquiv`, equivalently
  `MonoidalClosed.curry` / `MonoidalClosed.uncurry`;
- `bridge/view`: transport across the braiding isomorphism
  `β_ ℱ 𝒢 : ℱ ⊗ 𝒢 ≅ 𝒢 ⊗ ℱ`.
-/
