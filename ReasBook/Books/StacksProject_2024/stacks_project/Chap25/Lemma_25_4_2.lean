import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_5_1
import StacksProject_2024.stacks_project.Chap25.Definition_25_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open AlgebraicTopology
open scoped CategoryTheory.FreeAbelianSheaf

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable {ℱ 𝒢 : Cᵒᵖ ⥤ Type (max w v)}
variable {K : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))}

-- Semantic search tool unavailable in this runner; the statement uses the canonical local-surjective
-- presheaf hypothesis together with the Čech nerve owner `Arrow.mk φ`.

/-- The canonical degree-`0` identification of the homology of the constant simplicial presheaf on
`𝒢` with the free abelian sheaf on `𝒢`. -/
noncomputable def simplicialPresheafConstHomologyZeroIso
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) :
    simplicialPresheafHomology J
        ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) 0 ≅
      ((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{max w v}) :=
  (HomologicalComplex.homologyFunctor
      (Sheaf J AddCommGrpCat.{max w v}) (ComplexShape.down ℕ) 0).mapIso
    ((AlgebraicTopology.alternatingFaceMapComplex
        (Sheaf J AddCommGrpCat.{max w v})).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ 𝒢
        (simplicialPresheafFreeAbelianSheafFunctor J))) ≪≫
    (HomologicalComplex.homologyFunctor
      (Sheaf J AddCommGrpCat.{max w v}) (ComplexShape.down ℕ) 0).mapIso
      (AlgebraicTopology.alternatingFaceMapComplexConst.app
        (((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{max w v}))) ≪≫
    ChainComplex.alternatingConstHomologyZero
      (((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{max w v}))

/-- The canonical degree-`0` comparison map from `H₀(K)` to the free abelian sheaf
`(ℤ_ 𝒢)^#[J]`, induced by the augmentation of `K`. -/
  noncomputable abbrev simplicialPresheafHomology_zeroToFreeAbelianSheaf
      (augmentation :
        K ⟶ (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
      simplicialPresheafHomology J K 0 ⟶ ((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{max w v}) :=
    simplicialPresheafHomologyMap J augmentation 0 ≫
    (simplicialPresheafConstHomologyZeroIso J 𝒢).hom

@[simp]
  theorem simplicialPresheafHomology_zeroToFreeAbelianSheaf_def
      (augmentation :
        K ⟶ (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :
    simplicialPresheafHomology_zeroToFreeAbelianSheaf J augmentation =
      simplicialPresheafHomologyMap J augmentation 0 ≫
        (simplicialPresheafConstHomologyZeroIso J 𝒢).hom := rfl

/-- Lemma 25.4.2 (1): if `φ : ℱ ⟶ 𝒢` is surjective after sheafification, then the positive-degree
homology sheaves of the simplicial presheaf whose `n`-simplices are the `(n + 1)`-fold fibre
products of `ℱ` over `𝒢` vanish. -/
theorem cechNerve_simplicialPresheafHomology_succ_isZero
    (φ : ℱ ⟶ 𝒢) [Presheaf.IsLocallySurjective J φ] (n : ℕ) :
    IsZero (simplicialPresheafHomology J (Arrow.mk φ).cechNerve (n + 1)) := sorry

/-- Lemma 25.4.2 (2): if `φ : ℱ ⟶ 𝒢` is surjective after sheafification, then the canonical
degree-`0` comparison map from the homology sheaf of the Čech nerve of `φ` to the free abelian
sheaf on `𝒢` is an isomorphism. -/
theorem cechNerve_simplicialPresheafHomology_zeroToFreeAbelianSheaf_isIso
    (φ : ℱ ⟶ 𝒢) [Presheaf.IsLocallySurjective J φ] :
    IsIso (simplicialPresheafHomology_zeroToFreeAbelianSheaf J
      (Arrow.mk φ).augmentedCechNerve.hom) := sorry

end

end CategoryTheory
