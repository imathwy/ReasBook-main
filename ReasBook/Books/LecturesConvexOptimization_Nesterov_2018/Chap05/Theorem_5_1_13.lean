import Nesterov.Chap05.Definition_5_0_21
import Nesterov.Chap05.Definition_5_0_23
import Nesterov.Chap05.Definition_5_0_24
import Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient NewtonDecrement SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.13 lies in the Chapter 5 self-concordant minimization domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for strict Hessian
  positivity on the domain;
* `newtonDecrement` and `NewtonDecrement.ofPosDefMem` from `Definition_5_0_24`, the canonical
  Newton-decrement owner, its domain-membership bridge, and the canonical small-decrement
  `ω_*` argument `NewtonDecrement.omegaStarArgOfPosDefMem`;
* `selfConcordantOmegaStar` and the notation `ω_*` from `Definition_5_0_21`, the standard
  self-concordant remainder term.

Best owner abstraction:
* source-facing: existence and uniqueness of a minimizer together with the `ω_*` suboptimality
  bound under the small-Newton-decrement hypothesis;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `HasPositiveDefiniteHessianOn dom f`, and
  `NewtonDecrement.ofPosDefMem`;
* bridge/view: the canonical `ω_*` argument `M_f λ_f(x) ∈ (-∞, 1)`.

This file keeps the textbook theorem as a single source-facing declaration. After correcting
`Theorem_5_0_25` back to the convex recession-direction theorem, this result now depends directly
on the underlying Chapter 5 self-concordant owners instead of a transitive theorem from the wrong
numbered item.
-/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f]

-- Proof sketch: the small-Newton-decrement hypothesis already forces `Mf > 0`, because
-- `NewtonDecrement.ofPosDefMem_nonneg` gives `0 ≤ λ_f(x)` while `Mf = 0` would rewrite
-- `λ_f(x) < 1 / M_f` to the impossible inequality `λ_f(x) < 0`. From that hypothesis we obtain a
-- minimizer and then apply the standard self-concordant upper model `ω_*` at that minimizer.
-- Strict convexity from the positive-definite Hessian gives uniqueness.
/-- Theorem 5.1.13: if `f` is self-concordant on `dom`, its Hessian is positive definite on
`dom`, and some `x ∈ dom` satisfies `λ_f(x) < 1 / M_f`, then `f` admits a unique minimizer on
`dom`, and that minimizer satisfies the standard `ω_*` suboptimality bound measured from `x`.
The small-decrement hypothesis forces `M_f > 0` internally, so no separate positivity binder is
needed on the theorem surface. -/
theorem existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv
    {x : E} (hx : x ∈ dom)
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ∃! xStar : dom,
      IsMinOn f dom (xStar : E) ∧
        f x - f xStar ≤
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  have hMf : 0 < Mf := by
    by_contra hMf
    have hMf0 : Mf = 0 := le_antisymm (not_lt.mp hMf) Mf.2
    have hnonneg : 0 ≤ λ[f; x | hx] :=
      NewtonDecrement.ofPosDefMem_nonneg f x hx
    have hlt0 : λ[f; x | hx] < 0 := by
      simpa [hMf0] using hlambda
    linarith
  sorry

end

end
