import Mathlib
import StacksProject_2024.Chap29.Lemma_29_54_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical relative-normalization morphism
-- `Scheme.Hom.fromNormalization`; local Chapter 29 precedent packages the source-facing
-- normalization morphism as `Scheme.normalizationTo` and birationality as `IsBirational`.

/-- A scheme with finitely many irreducible components satisfies the chapter finiteness
hypothesis on irreducible components of quasi-compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensOfFiniteIrreducibleComponents
    (X : Scheme.{u}) [Finite (irreducibleComponents X)] :
    HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

/-- The normalization of a scheme with finitely many irreducible components again has finitely
many irreducible components. -/
instance instFiniteIrreducibleComponentsNormalizationOfFiniteIrreducibleComponents
    (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    Finite (irreducibleComponents X.normalization) := sorry

/-- Lemma 29.54.7: let `X` be a reduced scheme with finitely many irreducible components. Then
the normalization morphism `ν : X^ν ⟶ X`, formalized as `X.normalizationTo`, is birational. -/
@[stacks 0BXC]
theorem isBirational_normalizationTo_of_isReduced_finiteIrreducibleComponents
    (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    IsBirational X.normalizationTo := sorry

end AlgebraicGeometry.Scheme
