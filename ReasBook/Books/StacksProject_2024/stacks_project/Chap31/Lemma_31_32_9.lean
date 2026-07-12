import Mathlib
import StacksProject_2024.Chap31.Definition_31_32_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme predicate `IsIntegral`, and
-- local Chapter 31 search verified that this workspace records blowups both by the universal
-- property class `IsBlowup` and by the packaged owner `Blowup`. The dependencies
-- `Lemma 31.32.2` and `Lemma 10.70.10` indicate the intended affine-chart route, so the main
-- statement is placed on `IsBlowup` with a thin companion for `Blowup`.

/-- Lemma 31.32.9: if `X` is an integral scheme and `b : X' ⟶ X` is the blowup of `X` in a
nonzero quasi-coherent ideal sheaf `I`, then `X'` is integral. -/
@[stacks 02ND]
theorem isIntegral_of_isBlowup_of_ne_zero
    {X X' : Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData)
    [IsBlowup b I] [IsIntegral X] (hI : I ≠ 0) :
    IsIntegral X' := sorry

namespace Blowup

/-- A blowup of an integral scheme in a nonzero quasi-coherent ideal sheaf is integral. -/
theorem isIntegral_scheme
    {X : Scheme.{u}} {I : X.IdealSheafData} (π : Blowup X I)
    [IsIntegral X] (hI : I ≠ 0) :
    IsIntegral π.scheme := sorry

end Blowup

end AlgebraicGeometry
