import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall: `lean_leansearch` returned
`AlgebraicGeometry.IsSeparated.valuativeCriterion`, the canonical theorem saying that a separated
scheme morphism satisfies the uniqueness part of the valuative criterion. Local Lemma 29.42.2
phrases its dotted-arrow uniqueness hypothesis through `AlgebraicGeometry.ValuativeCommSq` and
the lift structures of the underlying commutative square. -/

/- Remark 29.42.3: the uniqueness assumption on the dotted arrows in Lemma 29.42.2 is a genuine
hypothesis; when `f` is separated, uniqueness is supplied by Schemes, Lemma 26.22.1, formalized as
the valuative-criterion uniqueness theorem for separated morphisms. -/
recall AlgebraicGeometry.IsSeparated.valuativeCriterion
