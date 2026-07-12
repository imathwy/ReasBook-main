import Mathlib
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` only surfaced the scheme-flatness owner
-- `AlgebraicGeometry.Flat`; the blowup owner was then verified from `Definition_31_34_1`, and the
-- local Chapter 31 pattern uses `Scheme.IdealSheafData.comap` together with the canonical
-- categorical pullback square.

section

variable {X₁ X₂ X₂' : Scheme.{u}}
variable (f : X₁ ⟶ X₂) [Flat f]
variable (I₂ : X₂.IdealSheafData) (b₂ : X₂' ⟶ X₂) [IsBlowup b₂ I₂]

/-- Lemma 31.32.3: if `f : X₁ ⟶ X₂` is flat and `b₂ : X₂' ⟶ X₂` is the blowup of `X₂` in the
closed subscheme defined by `I₂`, then the pullback projection `X₁ ×_{X₂} X₂' ⟶ X₁` is the blowup
of `X₁` in the inverse-image closed subscheme `I₂.comap f`. -/
theorem pullback_fst_isBlowup_of_flat :
    IsBlowup (pullback.fst f b₂) (I₂.comap f) := sorry

/-- The canonical pullback square of a flat base change of a blowup is again a blowup square. -/
theorem pullbackSquare_fst_isBlowup_of_flat :
    IsBlowup (pullback.fst f b₂) (I₂.comap f) ∧
      IsPullback (pullback.snd f b₂) (pullback.fst f b₂) b₂ f := by
  exact ⟨pullback_fst_isBlowup_of_flat (f := f) (I₂ := I₂) (b₂ := b₂), IsPullback.of_hasPullback f b₂⟩

/-- Source-facing cartesian reformulation of `pullback_fst_isBlowup_of_flat`. -/
theorem exists_cartesian_blowup_square_of_flat :
    ∃ (X₁' : Scheme.{u}) (b₁ : X₁' ⟶ X₁) (g' : X₁' ⟶ X₂'),
      IsBlowup b₁ (I₂.comap f) ∧ IsPullback g' b₁ b₂ f := by
  refine ⟨pullback f b₂, pullback.fst f b₂, pullback.snd f b₂, ?_⟩
  exact pullbackSquare_fst_isBlowup_of_flat (f := f) (I₂ := I₂) (b₂ := b₂)

end

end AlgebraicGeometry
