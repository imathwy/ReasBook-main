import Mathlib
import StacksProject_2024.Chap29.Lemma_29_6_7
import StacksProject_2024.Chap29.Lemma_29_7_7

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical reducedness owner `IsReduced`.
-- Local Chapter 29 inspection confirmed `schemeTheoreticClosure` and
-- `schemeTheoreticallyDense` as the project owners; the item tag `056E` agrees with the source URL.

variable {X : Scheme.{u}} (U : X.Opens)

/-- Lemma 29.7.9 (1): if `U ⊆ X` is a reduced open subscheme, then the scheme theoretic closure
of `U` in `X` is all of `X` if and only if `U` is scheme theoretically dense in `X`. -/
@[stacks 056E]
theorem schemeTheoreticClosure_eq_self_iff_schemeTheoreticallyDense_of_isReduced
    [IsReduced U.toScheme] :
    schemeTheoreticClosure U = X ↔ schemeTheoreticallyDense U := sorry

/-- Lemma 29.7.9 (2): if `U ⊆ X` is a reduced open subscheme whose scheme theoretic closure is
all of `X`, then `X` is reduced. -/
@[stacks 056E]
theorem isReduced_of_schemeTheoreticClosure_eq_self_of_isReduced
    [IsReduced U.toScheme] (hclosure : schemeTheoreticClosure U = X) :
    IsReduced X := sorry

end AlgebraicGeometry
