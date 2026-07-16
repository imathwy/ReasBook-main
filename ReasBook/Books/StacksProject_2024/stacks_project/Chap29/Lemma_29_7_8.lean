import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced mathlib's `Dense` predicate and
-- `Scheme.Opens`; local Chapter 29 inspection confirmed `schemeTheoreticClosure` and
-- `schemeTheoreticallyDense` as the project owners from `Definition_29_7_1`. The Stacks tag
-- evidence is consistent: item tag `056D` matches the source URL `/tag/056D`.

variable {X : Scheme.{u}} [IsReduced X]

/-- Lemma 29.7.8: for an open subscheme `U ⊆ X` of a reduced scheme `X`, topological density of
`U` in `X`, equality of the scheme-theoretic closure of `U` with `X`, and
scheme-theoretic density of `U` in `X` are equivalent. -/
@[stacks 056D]
theorem tfae_dense_schemeTheoreticClosure_eq_self_schemeTheoreticallyDense_of_isReduced
    (U : X.Opens) :
    List.TFAE [Dense (U : Set X), schemeTheoreticClosure U = X, schemeTheoreticallyDense U] := sorry

end AlgebraicGeometry
