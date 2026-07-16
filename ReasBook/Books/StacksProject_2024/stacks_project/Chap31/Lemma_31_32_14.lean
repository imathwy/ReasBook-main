import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the morphism-level finite-presentation and
-- closed-immersion owners, while local Chapter 31 precedent records blowups through `IsBlowup`
-- and closed subschemes through `Scheme.IdealSheafData.support` and `subschemeι`.

/-- Lemma 31.32.14: if `X` is quasi-compact and quasi-separated, `Z ⊆ X` is a finitely
presented closed subscheme, `b : X' ⟶ X` is the blowup in `Z`, `Z' ⊆ X'` is a finitely
presented closed subscheme, and `b' : X'' ⟶ X'` is the blowup in `Z'`, then there is a
finitely presented closed subscheme `Y ⊆ X` whose underlying set is `Z ∪ b(Z')` and such that
the composite `X'' ⟶ X` is the blowup of `X` in `Y`. -/
@[stacks 080B]
theorem exists_finitePresentation_closedSubscheme_support_eq_union_image_and_isBlowup_comp
    {X X' X'' : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (Z : X.IdealSheafData) (hZfp : LocallyOfFinitePresentation Z.subschemeι)
    (b : X' ⟶ X) [IsBlowup b Z]
    (Z' : X'.IdealSheafData) (hZ'fp : LocallyOfFinitePresentation Z'.subschemeι)
    (b' : X'' ⟶ X') [IsBlowup b' Z'] :
    ∃ Y : {Y : X.IdealSheafData // LocallyOfFinitePresentation Y.subschemeι},
      ((Y : X.IdealSheafData).support : Set X) =
          (Z.support : Set X) ∪ b.base '' (Z'.support : Set X') ∧
        IsBlowup (b' ≫ b) (Y : X.IdealSheafData) := sorry

end AlgebraicGeometry
