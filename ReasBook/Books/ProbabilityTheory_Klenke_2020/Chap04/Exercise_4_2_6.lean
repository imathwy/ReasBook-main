import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators ENNReal

/-- A real-valued step function on `ℝ` is constant on the finitely many intervals cut out by a
strictly increasing finite family of breakpoints, namely on `(-∞, t₀]`, on each
`(tᵢ, tᵢ₊₁]`, and on `(tₙ, ∞)`. -/
def IsStepFunction (h : ℝ → ℝ) : Prop :=
  ∃ n : ℕ, ∃ t : Fin (n + 1) → ℝ, StrictMono t ∧
    ∃ a b : ℝ, ∃ α : Fin n → ℝ,
      h = fun x ↦
        (Set.Iic (t 0)).indicator (fun _ ↦ a) x +
          ∑ k, (Set.Ioc (t (Fin.castSucc k)) (t k.succ)).indicator (fun _ ↦ α k) x +
            (Set.Ioi (t (Fin.last n))).indicator (fun _ ↦ b) x

-- Proof sketch: unfold the representation of a step function, note that `Set.Iic a`,
-- `Set.Ioc a b`, and `Set.Ioi a` are measurable in `ℝ`, each indicator summand is measurable, and
-- finite sums preserve measurability.
/-- Every real-valued step function is measurable. -/
theorem IsStepFunction.measurable {h : ℝ → ℝ} (hh : IsStepFunction h) :
    Measurable h := sorry

namespace IsStepFunction

/-- A real-valued step function on `ℝ` has finite range. -/
theorem finite_range {h : ℝ → ℝ} (hh : IsStepFunction h) :
    (Set.range h).Finite := sorry

end IsStepFunction

/-- Exercise 4.2.6: every real-valued `L^p` function on `ℝ` with respect to Lebesgue measure can
be approximated arbitrarily well in `eLpNorm` by a real-valued step function. -/
-- Proof sketch: first approximate `f` in `eLpNorm` by a simple function using
-- `MemLp.exists_simpleFunc_eLpNorm_sub_lt`; then approximate the measurable fibers of that simple
-- function by a finite interval partition of `ℝ`, and finally transfer the approximation argument
-- from Exercise 4.2.5.
theorem exists_stepFunction_eLpNorm_sub_lt_of_memLp
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      IsStepFunction h ∧
        eLpNorm (f - h) (ENNReal.ofReal p) volume < ENNReal.ofReal ε := sorry
