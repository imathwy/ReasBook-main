module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- Exercise 21.11 (1): A bounded increasing sequence of real numbers converges. -/
theorem tendsto_of_bounded_monotone {s : ℕ → ℝ}
    (h_bounded : Bornology.IsBounded (Set.range s)) (h_mono : Monotone s) :
    ∃ l : ℝ, Filter.Tendsto s Filter.atTop (nhds l) :=
  ⟨⨆ n, s n, tendsto_atTop_ciSup h_mono h_bounded.bddAbove⟩

/-- Exercise 21.11 (2): Real series are closed under adding a constant multiple of one
series to another, using mathlib's zero-based indexing. -/
theorem hasSum_const_mul_add {a b : ℕ → ℝ} {s t : ℝ} (c : ℝ)
    (ha : HasSum a s) (hb : HasSum b t) :
    HasSum (fun n ↦ c * a n + b n) (c * s + t) :=
  (ha.mul_left c).add hb

/- Exercise 21.11 (3): The comparison test for infinite series. For real-valued
sequences, the norm bound in `Summable.of_norm_bounded` is exactly `|a n| ≤ b n`. -/
#check Summable.of_norm_bounded

/- Exercise 21.11 (4): The Weierstrass M-test. Specializing
`tendstoUniformly_tsum_nat` to real-valued functions gives the textbook statement,
with `Finset.range N` expressing the zero-based partial sum through the first `N` terms. -/
#check tendstoUniformly_tsum_nat

end
