import Mathlib
import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules} [hL : Invertible L]

/- Semantic recall: `lean_leansearch` surfaced the canonical separated-scheme owner
`Scheme.IsSeparated` and affine-open/quasi-separated cover criteria, while local Chapter 28
precedes this item with the source-facing `Invertible` interface and its nonvanishing opens. -/

/-- Lemma 28.26.7: if every point of a scheme `X` lies in an affine nonvanishing open `X_s`
for some global section `s` of a positive tensor power of an invertible `\mathcal O_X`-module
`L`, then `X` is separated. -/
@[stacks 01PY]
theorem isSeparated_of_forall_exists_positive_tensorPow_section_affine_nonvanishing
    (h : ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(hL n, ⊤),
      AffineOpenNeighborhood x (hL.nonvanishingOpen s)) :
    X.IsSeparated := sorry

end AlgebraicGeometry.Scheme.Modules
