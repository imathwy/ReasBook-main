import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_13_8
import StacksProject_2024.stacks_project.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` confirmed the canonical finiteness owner `AlgebraicGeometry.IsFinite`, while
-- Chapter 29 already packages the scheme normalization morphism as `Scheme.normalizationTo`.
-- The source-faithful statement is therefore the Nagata specialization `IsFinite X.normalizationTo`.

/-- A Nagata scheme has finitely many irreducible components on quasi-compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensOfNagata (X : Scheme.{u}) [Nagata X] :
    HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

/-- Lemma 29.54.11: if `X` is a Nagata scheme, then the normalization
`ν : X^ν ⟶ X`, formalized as `X.normalizationTo`, is a finite morphism. -/
@[stacks 035S]
theorem isFinite_normalizationTo_of_nagata (X : Scheme.{u}) [Nagata X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    IsFinite X.normalizationTo := sorry

end AlgebraicGeometry.Scheme
