import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Cardinal Polynomial

universe u v

section

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]

-- Layering for this item:
-- * source-facing: the Stacks statement is the existence of a monic polynomial whose value at an
--   endomorphism is not a unit.
-- * core/canonical owner: `IsAlgebraic k T` for `T : Module.End k V`.
-- * bridge: under the same cardinal bound, the endomorphism is algebraic, and the source-facing
--   statement follows from its minimal polynomial.

-- Proof sketch: Assume every monic polynomial evaluated at `T` is a unit. Then the polynomial
-- functional calculus for `T` extends from `k[X]` to `RatFunc k`, so `V` becomes a vector space
-- over `k(t)`. Since `k(t)` has `k`-dimension at least `#k`, cardinality estimates force
-- `Module.rank k V` to be at least `#k`, contradicting the hypothesis.
/-- Companion bridge: under the same small-rank hypothesis, an endomorphism is algebraic over the
base field. -/
theorem isAlgebraic_of_rank_lt_cardinal
    (T : Module.End k V)
    (hV : lift.{max u v} (Module.rank k V) < lift.{max u v} (#k)) :
    IsAlgebraic k T := by
  sorry

/-- Lemma 10.35.10 (Tag 00FT): if `V` is a nontrivial `k`-vector space whose dimension is
strictly smaller than the cardinality of `k`, then every endomorphism of `V` admits a monic
polynomial whose evaluation at that endomorphism is not a unit. -/
theorem exists_monic_polynomial_aeval_not_isUnit_of_rank_lt_cardinal
    (T : Module.End k V)
    (hV : lift.{max u v} (Module.rank k V) < lift.{max u v} (#k)) :
    ∃ P : k[X], P.Monic ∧ ¬ IsUnit (aeval T P) := by
  refine ⟨minpoly k T, minpoly.monic (isAlgebraic_of_rank_lt_cardinal T hV).isIntegral, ?_⟩
  simp [minpoly.aeval k T]

end
