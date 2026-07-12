import Mathlib
import StacksProject_2024.Chap31.Lemma_31_13_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the Krull-dimension owner
-- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`, and local Chapter 31 precedent packages an
-- effective Cartier divisor as `D : S.IdealSheafData` with closed subscheme `D.subscheme`. The
-- source point `s ∈ D` is represented here by `x : D.subscheme`.

variable {S : Scheme.{u}}

/-- The structure sheaf presheaf on the closed subscheme cut out by `D`. -/
private noncomputable abbrev subschemePresheaf (D : S.IdealSheafData) :=
  D.subscheme.presheaf

/-- The local ring of the closed subscheme cut out by `D` at the point `x`. -/
private noncomputable abbrev subschemeStalk (D : S.IdealSheafData) (x : D.subscheme) :=
  (subschemePresheaf D).stalk x

/-- Lemma 31.13.5: if `D ⊆ S` is an effective Cartier divisor and `s ∈ D`, then finite local
dimension at `s` on `S` forces the local dimension on `D` at `s` to be strictly smaller. Here
the source point `s ∈ D` is represented by `x : D.subscheme`, whose image in `S` is
`D.subschemeι x`. -/
theorem ringKrullDim_stalk_subscheme_lt_stalk_of_isEffectiveCartierDivisor
    (D : S.IdealSheafData) [IsEffectiveCartierDivisor D] (x : D.subscheme)
    (hfin : ringKrullDim (S.presheaf.stalk (D.subschemeι x)) < ⊤) :
    ringKrullDim (subschemeStalk D x) <
      ringKrullDim (S.presheaf.stalk (D.subschemeι x)) := sorry

end AlgebraicGeometry.Scheme
