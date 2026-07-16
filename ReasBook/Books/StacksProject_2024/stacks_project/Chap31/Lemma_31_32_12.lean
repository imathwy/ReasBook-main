import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.comap` and
-- `Scheme.IdealSheafData.comap_comp`; local Chapter 31 precedent records blowups through
-- `IsBlowup` and ideal-sheaf products by the affine-open formula
-- `Scheme.IdealSheafData.ofIdeals (fun U ↦ I.ideal U * J.ideal U)`.

/-- The product of two ideal sheaves, expressed on affine opens by the product of section ideals. -/
def idealSheafProduct {X : Scheme.{u}} (I J : X.IdealSheafData) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦ I.ideal U * J.ideal U

/-- Lemma 31.32.12: let `b : X' -> X` be the blowup of `X` in the quasi-coherent ideal sheaf
`I`, and let `b' : X'' -> X'` be the blowup of `X'` in `J.comap b`
(`b^{-1} J O_{X'}`). Then the composite `X'' -> X` is the blowup of `X` in the product
ideal sheaf `I J`; this is the project-level form of the canonical isomorphism with the blowup
of `X` in `I J`. -/
@[stacks 080A]
theorem iteratedBlowup_isBlowup_idealSheafProduct
    {X X' X'' : Scheme.{u}} (I J : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I]
    (b' : X'' ⟶ X') [IsBlowup b' (J.comap b)] :
    IsBlowup (b' ≫ b) (idealSheafProduct I J) := sorry

end AlgebraicGeometry
