import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import StacksProject_2024.stacks_project.Chap26.Definition_26_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Scheme.IdealSheafData

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the source-facing owner stays on an ideal-sheaf-defined closed subscheme
-- `Z : X.IdealSheafData`, with factorization expressed by existence of a morphism to
-- `Z.subscheme`. For part (2), the canonical reduced subscheme owner is `X.nilradical.subscheme`.

variable {X Y : Scheme.{u}} [IsReduced Y]

/-- Lemma 26.12.7 (1): let `X` be a scheme, let `Z ⊆ X` be a closed subscheme, and let `Y` be a
reduced scheme. A morphism `f : Y ⟶ X` factors through `Z`, expressed as the existence of
`g : Y ⟶ Z.subscheme` with `g ≫ Z.subschemeι = f`, if and only if the set-theoretic image of `f`
is contained in the underlying closed subset `Z.support`. -/
@[stacks 0356]
theorem exists_factorization_subschemeι_iff_range_subset
    (f : Y ⟶ X) (Z : X.IdealSheafData) :
    (∃ g : Y ⟶ Z.subscheme, g ≫ Z.subschemeι = f) ↔
      Set.range f.base ≤ (Z.support : Set X) := sorry

/-- Lemma 26.12.7 (1), companion uniqueness: since `Z.subschemeι` is a preimmersion, any
factorization through `Z.subscheme` is unique. Thus the source criterion can be promoted from
existence to unique existence for downstream use. -/
theorem existsUnique_factorization_subschemeι_iff_range_subset
    (f : Y ⟶ X) (Z : X.IdealSheafData) :
    (∃! g : Y ⟶ Z.subscheme, g ≫ Z.subschemeι = f) ↔
      Set.range f.base ≤ (Z.support : Set X) := by
  sorry

/-- Lemma 26.12.7 (2): any morphism from a reduced scheme `Y` to a scheme `X` factors through the
reduced subscheme `X_red`, formalized by the Chapter 26 owner `reduction X` and its canonical
inclusion `X.nilradical.subschemeι`; this is the previous theorem specialized to the nilradical
closed subscheme, using that its support is all of `X`. -/
@[stacks 0356]
theorem exists_factorization_reducedSubschemeι
    (f : Y ⟶ X) :
    ∃ g : Y ⟶ reduction X, g ≫ X.nilradical.subschemeι = f := sorry

/-- Lemma 26.12.7 (2), companion uniqueness: the factorization through the reduced subscheme is
unique. -/
theorem existsUnique_factorization_reducedSubschemeι
    (f : Y ⟶ X) :
    ∃! g : Y ⟶ reduction X, g ≫ X.nilradical.subschemeι = f := by
  sorry

end AlgebraicGeometry.Scheme
