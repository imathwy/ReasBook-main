import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_0_1 (from Chap12) -/
/-
Lemma 12.0.1 is `bridge/view`. Domain sampling in mathlib's real-logarithm API gives:
- `Real.log_lt_sub_one_of_pos` as the owner inequality;
- `Real.strictMonoOn_log` as the ambient order-theoretic owner on `(0, ∞)`;
- `Real.strictConcaveOn_log_Ioi` as the ambient convex-analytic owner on `(0, ∞)`;
- `Real.lt_log_one_add_of_pos` as a nearby `log (1 + x)` comparison theorem.

The primitive data for the textbook statement are only `x : ℝ` and `hx : 0 < x`. The target
inequality is the source-facing specialization of `Real.log_lt_sub_one_of_pos` at `1 + x`, so the
public API should stay a thin theorem-level bridge rather than a parallel local owner. -/

/-- Lemma 12.0.1: for every real `x > 0`, one has `log (1 + x) < x`. -/
-- Proof sketch: apply `Real.log_lt_sub_one_of_pos` to `1 + x`; positivity follows from `x > 0`,
-- and the right-hand side simplifies to `(1 + x) - 1 = x`.
theorem log_one_add_lt_self {x : ℝ} (hx : 0 < x) : Real.log (1 + x) < x := by
  have hpos : 0 < 1 + x := by positivity
  have hne : 1 + x ≠ 1 := by linarith
  simpa using Real.log_lt_sub_one_of_pos hpos hne

/-! ### Proposition_12_0_2 (from Chap12) -/
/- Proposition 12.0.2 is a `bridge/view` item: the source-facing series starts at `n = 1`,
while the core owner abstraction is the mathlib `p`-series theorem
`Real.summable_one_div_nat_pow`, stated on `n : ℕ` starting at `0`. The proposition is the
canonical shift-by-one specialization of that owner. -/
recall summable_nat_add_iff
recall Real.summable_one_div_nat_pow

/-- Proposition 12.0.2: the series `∑_{n=1}^{\infty} 1 / n^2` converges. -/
theorem one_div_nat_sq_summable_from_one :
    Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  -- The owner result is the `p`-series theorem at exponent `2`.
  have hpow : 1 < (2 : ℕ) := by
    decide
  have hsummable : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr hpow
  -- Shifting the summation index from `0` to `1` matches the textbook series.
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
    (summable_nat_add_iff 1).2 hsummable

/-! ### Theorem_12_0_3 (from Chap12) -/
/- Theorem 12.0.3 is a `core/canonical` recall in one-variable calculus. Domain sampling:
- `exists_hasDerivAt_eq_slope` is the `HasDerivAt` owner form of Lagrange's theorem;
- `exists_deriv_eq_slope` is the canonical `deriv` owner matching the textbook statement;
- `exists_deriv_eq_slope'` is the same theorem in `slope` notation;
- `exists_deriv_eq_zero` is the nearby Rolle specialization.

The Chapter 12 item adds no new source-facing data or bridge construction, so the correct public
surface is the direct recall of `exists_deriv_eq_slope`. -/
recall exists_deriv_eq_slope

/-! ### Theorem_12_0_4 (from Chap12) -/
open scoped BigOperators
open Bornology

/- Theorem 12.0.4 is `source-facing`: the textbook object is the partial-sum sequence
`s_m = ∑_{n=1}^m 1 / n^2`. Domain sampling shows that the owner abstraction is the chapter's
summability theorem `one_div_nat_sq_summable_from_one`, together with mathlib's canonical
derived API `Summable.hasSum`, `HasSum.tendsto_sum_nat`, and
`CauchySeq.isBounded_range`. The primitive data are only the summable sequence
`n ↦ 1 / ((n + 1 : ℕ) : ℝ)^2`; boundedness of its partial sums is derived API. -/

/-- Theorem 12.0.4: the sequence `s_m = ∑_{n=1}^m 1 / n^2` is bounded. -/
theorem one_div_nat_sq_partialSums_isBounded :
    IsBounded
      (Set.range (fun m : ℕ ↦ ∑ n ∈ Finset.range m, 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
  simpa using
    one_div_nat_sq_summable_from_one.hasSum.tendsto_sum_nat.cauchySeq.isBounded_range

/-! ### Definition_12_0_6 (from Chap12) -/
open scoped ContDiff

section

variable (f : ℝ → ℝ) (I : Set ℝ)

/- Definition 12.0.6 is a `core/canonical` recall in one-variable smooth calculus. Domain sampling
in mathlib's same-domain owner API gives:
- `ContDiffWithinAt ℝ ∞ f I x` for smoothness at a point within a set;
- `ContDiffOn ℝ ∞ f I` for smoothness on a set;
- `ContDiff ℝ ∞ f` for global smoothness.

The source-facing textbook specialization adds no owner beyond `ContDiffOn`. The primitive data are
only the function `f` and interval `I`; openness of `I` remains ambient source setup rather than
primitive data of a second public wrapper. -/

/- Definition 12.0.6: the textbook notion of a smooth real-valued function on an open interval `I`
is the canonical mathlib predicate `ContDiffOn ℝ ∞ f I`. -/
#check ContDiffOn ℝ ∞ f I

end
