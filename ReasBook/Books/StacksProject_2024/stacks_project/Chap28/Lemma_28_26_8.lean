import Mathlib
import StacksProject_2024.Chap28.Lemma_28_26_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [CategoryTheory.MonoidalCategory X.Modules]

/- Semantic recall: `lean_leansearch` surfaced the canonical separated-scheme owner
`Scheme.IsSeparated`. The local Chapter 28 API represents an ample invertible sheaf by an
`Invertible` instance together with `IsAmple`, and Lemma 28.26.7 is the prior affine
nonvanishing-neighborhood criterion. -/

/-- Lemma 28.26.8: if a scheme `X` admits an ample invertible `\mathcal O_X`-module, then
`X` is separated. -/
@[stacks 09MP]
theorem isSeparated_of_exists_isAmple
    (h : ∃ (L : X.Modules) (hL : Invertible L), @IsAmple X inferInstance L hL) :
    X.IsSeparated := sorry

end AlgebraicGeometry.Scheme.Modules
