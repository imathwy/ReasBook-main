import Mathlib

open scoped Topology
open Set

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem III.1-extra-2: Liouville's theorem is the canonical result
`Differentiable.exists_eq_const_of_bounded`; for functions `ℂ → ℂ`, being holomorphic on the whole
plane is equivalent to `Differentiable ℂ` by `analyticOnNhd_univ_iff_differentiable`. -/
recall Differentiable.exists_eq_const_of_bounded

/- This is a `bridge/view` theorem: the owner theorem is
`Differentiable.exists_eq_const_of_bounded`, and
`analyticOnNhd_univ_iff_differentiable` supplies the entire-function specialization. -/
/-- A bounded entire function on `ℂ` is equal to a constant function. -/
-- Proof sketch: rewrite the hypothesis `AnalyticOnNhd ℂ f Set.univ` as `Differentiable ℂ f` using
-- `analyticOnNhd_univ_iff_differentiable`, then apply
-- `Differentiable.exists_eq_const_of_bounded`.
theorem exists_eq_const_of_bounded_of_analyticOnNhd_univ
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) (hb : Bornology.IsBounded (range f)) :
    ∃ c : ℂ, f = Function.const ℂ c := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable] at hf
  simpa using hf.exists_eq_const_of_bounded hb
