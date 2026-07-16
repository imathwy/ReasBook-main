import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `IsReduced.of_openCover` and
-- `isReduced_of_isAffine_isReduced` as the ambient reducedness owners, while local Chapter 31
-- precedent confirms that the blowup hypothesis is recorded by `IsBlowup`.

section

variable {X X' : Scheme.{u}} {I : X.IdealSheafData} {b : X' ⟶ X}

/-- Lemma 31.32.8: let `X` be a scheme and let `I ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. If
`X` is reduced, then the blowup `b : X' ⟶ X` of `X` in `I` is reduced. -/
@[stacks 0808]
theorem isReduced_of_isBlowup [IsReduced X] [IsBlowup b I] :
    IsReduced X' := sorry

end

end AlgebraicGeometry
