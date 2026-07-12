import Mathlib
import StacksProject_2024.Chap28.Lemma_28_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsIntegral.component_integral`
-- for the domain part of section rings on integral schemes, and Chapter 28 already packages
-- normality by `X.isNormal` and `_root_.IsNormalRing (Γ(X, U))`.

/-- Lemma 28.7.9: if `X` is an integral normal scheme, then its ring of global sections
`Γ(X, ⊤)` is a normal domain; in the project owner style, this is expressed by
`_root_.IsNormalRing (Γ(X, ⊤))`. -/
theorem isNormalRing_globalSections (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal) :
    _root_.IsNormalRing (Γ(X, ⊤)) := sorry

end AlgebraicGeometry.Scheme
