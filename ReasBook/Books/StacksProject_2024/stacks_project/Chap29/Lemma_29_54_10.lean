import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_13_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` recalled the canonical normalization and finiteness owners
-- `Scheme.normalizationTo` and `AlgebraicGeometry.IsFinite`, while mathlib also supplies
-- `irreducibleSpace_of_isIntegral`. The source-faithful statement is therefore the finiteness of
-- the normalization morphism under the integral-local `IsJapanese` hypothesis from Definition
-- `28.13.1`.

/-- An integral scheme has finitely many irreducible components on each quasi-compact open,
providing the ambient finiteness hypothesis needed to form `X.normalizationTo`. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensOfIsIntegral (X : Scheme.{u})
    [IsIntegral X] : HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

/-- Lemma 29.54.10: if `X` is an integral Japanese scheme, then the normalization
`ν : X^ν ⟶ X`, formalized as `X.normalizationTo`, is a finite morphism. -/
@[stacks 035R]
theorem isFinite_normalizationTo_of_isJapanese (X : Scheme.{u}) [IsIntegral X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    (hX : IsJapanese X) :
    IsFinite X.normalizationTo := sorry

end AlgebraicGeometry.Scheme
