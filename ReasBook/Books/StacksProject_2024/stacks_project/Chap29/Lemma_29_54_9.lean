import Mathlib
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced mathlib's relative-normalization morphism
-- `Scheme.Hom.fromNormalization`; local Chapter 29 packages the source-facing normalization
-- morphism as `Scheme.normalizationTo`, and Chapter 28 packages normal schemes as
-- `Scheme.isNormal`.

/-- Lemma 29.54.9: let `X` be a scheme with locally finitely many irreducible components. The
normalization morphism `ν : X^ν ⟶ X`, formalized as `X.normalizationTo`, is an isomorphism if
and only if `X` is normal. -/
@[stacks 0H7D]
theorem isIso_normalizationTo_iff_isNormal
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    IsIso X.normalizationTo ↔ X.isNormal := sorry

end AlgebraicGeometry.Scheme
