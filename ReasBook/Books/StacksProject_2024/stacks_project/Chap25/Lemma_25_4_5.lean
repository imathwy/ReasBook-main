import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_4_4
import StacksProject_2024.stacks_project.Chap25.Lemma_25_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C]
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable {X : C}

-- Semantic search note: `lean_leansearch` recalled the generic simplicial homology and
-- acyclicity API. The source-facing statement below keeps the local Chapter 25 fixed-target
-- `Hypercovering` owner and applies the presheaf functor `F : SR(C, X) ⥤ PSh(C) / h_X`.

/-- The simplicial presheaf `F(K)` attached to a hypercovering `K` of `X`. -/
abbrev hypercoveringSimplicialPresheaf (K : @Hypercovering C _ J X) :
    SimplicialObject (Cᵒᵖ ⥤ Type (max u v)) :=
  K.toSimplicialObject ⋙
    (SemiRepresentableFamily.Over.forget ⋙ SemiRepresentableFamily.toPresheaf)

/-- Helper: the fixed-target augmentations are natural in the simplicial direction of a
hypercovering. -/
private theorem hypercoveringAugmentation_naturality
    (K : @Hypercovering C _ J X) {Δ Γ : SimplexCategoryᵒᵖ} (f : Δ ⟶ Γ) :
    (hypercoveringSimplicialPresheaf K).map f ≫
        SemiRepresentableFamily.Over.augmentation (K.toSimplicialObject.obj Γ) =
      SemiRepresentableFamily.Over.augmentation (K.toSimplicialObject.obj Δ) ≫
        ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max u v))).obj
          (uliftYoneda.{u}.obj X)).map f := sorry

/-- The canonical augmentation `F(K) ⟶ h_X` of the simplicial presheaf attached to a
hypercovering of `X`. -/
noncomputable def hypercoveringAugmentation (K : @Hypercovering C _ J X) :
    hypercoveringSimplicialPresheaf K ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max u v))).obj (uliftYoneda.{u}.obj X) :=
  { app := fun Δ ↦ SemiRepresentableFamily.Over.augmentation (K.toSimplicialObject.obj Δ)
    naturality := fun {_ _} f ↦ hypercoveringAugmentation_naturality K f }

/-- Lemma 25.4.5 (1): for a hypercovering `K` of `X`, the homology of the simplicial presheaf
`F(K)` vanishes in all positive degrees. -/
@[stacks 01GF]
theorem hypercoveringSimplicialPresheafHomology_succ_isZero
    (K : @Hypercovering C _ J X) (n : ℕ) :
    IsZero (simplicialPresheafHomology J (hypercoveringSimplicialPresheaf K) (n + 1)) := sorry

/-- Lemma 25.4.5 (2): for a hypercovering `K` of `X`, the canonical degree-`0` comparison map
identifies the homology of `F(K)` with the free abelian sheaf `\mathbf{Z}_X^\#`. -/
@[stacks 01GF]
theorem hypercoveringSimplicialPresheafHomology_zeroToFreeAbelianSheaf_isIso
    (K : @Hypercovering C _ J X) :
    IsIso (simplicialPresheafHomology_zeroToFreeAbelianSheaf J
      (hypercoveringAugmentation K)) := sorry

end

end CategoryTheory
