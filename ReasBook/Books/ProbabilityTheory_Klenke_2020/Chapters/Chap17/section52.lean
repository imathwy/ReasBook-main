import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_17_52 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- A reset-walk parameter sequence is a sequence of one-step upward-jump probabilities `p_n`
lying in the interval `[0, 1]`. -/
def IsResetWalkProbabilitySequence (p : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1

/-- The source data of the reset walk: a probability sequence `(p_n)` for the upward move
`n ↦ n + 1`, with reset probability `1 - p_n`. -/
abbrev ResetWalkParameters := {p : ℕ → ℝ // IsResetWalkProbabilitySequence p}

instance : CoeFun ResetWalkParameters (fun _ ↦ ℕ → ℝ) :=
  ⟨Subtype.val⟩

/- Layering for Example 17.52:
- source-facing data: the probability sequence `(p_n)`, its prefix products, and the chain-level
  recurrence criteria for realizations of the reset walk;
- core/canonical owner: the stochastic matrix `resetWalkTransitionMatrix p`, its discrete kernel
  `resetWalkKernel p`, and invariant measures expressed by `Kernel.Invariant`;
- bridge/view data: the weighted counting measure attached to the explicit singleton masses
  `c ∏_{k < n} p_k`. -/

/-- The stochastic transition matrix of the upward-jump/reset-to-zero chain determined by the
probability sequence `(p_n)`. -/
def resetWalkTransitionMatrix (p : ResetWalkParameters) : ℕ → ℕ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then
      ENNReal.ofReal (p x)
    else if y = 0 then
      ENNReal.ofReal (1 - p x)
    else
      0

-- Proof sketch: unfold `resetWalkTransitionMatrix`; this is exactly the piecewise definition of
-- the example's one-step probabilities.
/-- Evaluating the reset-walk transition matrix reproduces the textbook piecewise formula. -/
theorem resetWalkTransitionMatrix_apply (p : ResetWalkParameters) (x y : ℕ) :
    resetWalkTransitionMatrix p x y =
      if y = x + 1 then ENNReal.ofReal (p x) else
        if y = 0 then ENNReal.ofReal (1 - p x) else 0 := rfl

-- Proof sketch: for the row at `x`, only the entries at `x + 1` and `0` are nonzero, and their
-- masses are `p_x` and `1 - p_x`, which add up to `1`.
/-- The reset-walk transition matrix is stochastic. -/
theorem resetWalkTransitionMatrix_isStochasticMatrix (p : ResetWalkParameters) :
    IsStochasticMatrix (resetWalkTransitionMatrix p) := sorry

/-- The chapter-canonical discrete kernel attached to the reset walk. -/
def resetWalkKernel (p : ResetWalkParameters) : Kernel ℕ ℕ :=
  discreteMatrixKernel (resetWalkTransitionMatrix p)

/-- The reset-walk kernel carries the canonical Markov-kernel instance. -/
instance (p : ResetWalkParameters) : IsMarkovKernel (resetWalkKernel p) :=
  discreteMatrixKernel_isMarkovKernel _ (resetWalkTransitionMatrix_isStochasticMatrix p)

/-- The finite prefix product `∏_{k=0}^{n-1} p_k`. -/
def resetWalkPrefixProduct (p : ResetWalkParameters) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) p

-- Proof sketch: every factor `p_k` is nonnegative, so the finite product is nonnegative.
/-- The reset-walk prefix products are nonnegative. -/
theorem resetWalkPrefixProduct_nonneg (p : ResetWalkParameters) (n : ℕ) :
    0 ≤ resetWalkPrefixProduct p n := sorry

/-- The `ℝ≥0∞`-valued prefix product attached to the reset walk. -/
def resetWalkPrefixProductENNReal (p : ResetWalkParameters) (n : ℕ) : ℝ≥0∞ :=
  ((show NNReal from ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩) : ℝ≥0∞)

-- Proof sketch: unfold `resetWalkPrefixProduct`; the empty product equals `1`.
/-- The zeroth prefix product is `1`. -/
theorem resetWalkPrefixProduct_zero (p : ResetWalkParameters) :
    resetWalkPrefixProduct p 0 = 1 := by
  simp [resetWalkPrefixProduct]

-- Proof sketch: unfold `resetWalkPrefixProduct`; extending the range from `n` to `n + 1`
-- multiplies by the new factor `p n`.
/-- The prefix products satisfy the one-step recursion `a_{n+1} = a_n p_n`. -/
theorem resetWalkPrefixProduct_succ (p : ResetWalkParameters) (n : ℕ) :
    resetWalkPrefixProduct p (n + 1) = resetWalkPrefixProduct p n * p n := by
  simp [resetWalkPrefixProduct, Finset.prod_range_succ]

/-- The series `M = ∑_{n=0}^∞ ∏_{k=0}^{n-1} p_k` attached to the chain, taken in `ℝ≥0∞` so that
divergent cases retain the value `∞`. -/
def resetWalkMassSeries (p : ResetWalkParameters) : ℝ≥0∞ :=
  ∑' n : ℕ, resetWalkPrefixProductENNReal p n

-- Proof sketch: unfold `resetWalkMassSeries`; it is defined as the `ℝ≥0∞`-sum of the
-- prefix-product sequence.
/-- The extended mass series is the `ℝ≥0∞`-sum of the reset-walk prefix products. -/
theorem resetWalkMassSeries_eq_tsum (p : ResetWalkParameters) :
    resetWalkMassSeries p = ∑' n : ℕ, resetWalkPrefixProductENNReal p n := rfl

/-- The explicit singleton-mass profile `μ {n} = c ∏_{k < n} p_k` attached to an initial mass
`c`. -/
def resetWalkInvariantMass (p : ResetWalkParameters) (c : ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun n ↦ c * resetWalkPrefixProductENNReal p n

/-- The weighted counting measure on `ℕ` with singleton masses
`resetWalkInvariantMass p c`. -/
def resetWalkInvariantMeasure (p : ResetWalkParameters) (c : ℝ≥0∞) : Measure ℕ :=
  Measure.count.withDensity (resetWalkInvariantMass p c)

-- Proof sketch: unfold `resetWalkInvariantMass`; the singleton mass at `n` is the initial mass
-- `c` multiplied by the prefix product up to `n - 1`.
/-- The explicit singleton-mass profile is given pointwise by the prefix-product formula. -/
theorem resetWalkInvariantMass_apply (p : ResetWalkParameters) (c : ℝ≥0∞) (n : ℕ) :
    resetWalkInvariantMass p c n = c * resetWalkPrefixProductENNReal p n := rfl

-- Proof sketch: on the discrete state space `ℕ`, `Measure.count.withDensity` evaluates on a
-- singleton `{n}` as the density value at `n`.
/-- The weighted counting measure `resetWalkInvariantMeasure p c` has singleton mass
`resetWalkInvariantMass p c n` at `{n}`. -/
theorem resetWalkInvariantMeasure_apply_singleton
    (p : ResetWalkParameters) (c : ℝ≥0∞) (n : ℕ) :
    resetWalkInvariantMeasure p c {n} = resetWalkInvariantMass p c n := sorry

-- Proof sketch: evaluate the stationarity equation on singletons. The resulting recursion
-- `μ {n + 1} = p_n μ {n}` forces the singleton masses to match the explicit prefix-product
-- profile with `c = μ {0}`.
/-- Any invariant measure for the reset walk is determined by its singleton mass at `0` and the
prefix-product formula. -/
theorem invariant_singletonMass_eq_resetWalkInvariantMass
    (p : ResetWalkParameters) (μ : Measure ℕ) (hμ : Kernel.Invariant (resetWalkKernel p) μ)
    (n : ℕ) :
    μ {n} = resetWalkInvariantMass p (μ {0}) n := sorry

-- Proof sketch: for the weighted counting measure with singleton masses
-- `c ∏_{k < n} p_k`, the singleton balance equation is automatic away from `0`. At `0`, the
-- stationarity equation becomes `c = c * (1 - ∏' n, p n)`, so vanishing of the infinite product
-- is exactly the remaining condition. Finiteness of `c` matters only for later finite-measure
-- statements, not for invariance itself.
/-- If the infinite product `∏' n, p n` vanishes, then the weighted counting measure with
singleton masses `c ∏_{k < n} p_k` is invariant for the reset-walk kernel. -/
theorem resetWalkInvariantMeasure_isInvariant
    (p : ResetWalkParameters) (c : ℝ≥0∞)
    (hprod : ∏' n : ℕ, p n = 0) :
    Kernel.Invariant (resetWalkKernel p) (resetWalkInvariantMeasure p c) := sorry

-- Proof sketch: any invariant measure is determined by its singleton mass at `0`, and evaluating
-- the invariant equation at `{0}` shows that a positive finite value of `μ {0}` is possible
-- exactly when `∏' n, p n = 0`. Conversely, if the product vanishes then the weighted counting
-- measure with `c = 1` is invariant.
/-- Example 17.52: for the chain on `ℕ` with transition probabilities `p(x,x+1)=p_x` and
`p(x,0)=1-p_x`, there exists an invariant measure with positive finite singleton mass at `0` if
and only if the infinite product `∏' n, p n` is `0`. -/
theorem exists_nontrivial_resetWalkInvariantMeasure_iff_tprod_eq_zero
    (p : ResetWalkParameters) :
    (∃ μ : Measure ℕ, 0 < μ {0} ∧ μ {0} < ∞ ∧ Kernel.Invariant (resetWalkKernel p) μ) ↔
      ∏' n : ℕ, p n = 0 := sorry

-- Proof sketch: under `0 < p_n ≤ 1`, the logarithmic criterion for infinite products identifies
-- vanishing of `∏' n, p n` with divergence of the nonnegative defect series `∑ (1 - p_n)`.
/-- Vanishing of the infinite product is equivalent to divergence of the defect series
`∑ (1 - p_n)`. Here divergence is expressed as non-summability. -/
theorem resetWalk_tprod_eq_zero_iff_not_summable_one_sub
    (p : ResetWalkParameters) (hp : ∀ n : ℕ, 0 < p n) :
    (∏' n : ℕ, p n = 0) ↔ ¬ Summable (fun n : ℕ ↦ 1 - p n) := sorry

-- Proof sketch: use the explicit formula `μ {n} = μ {0} * ∏_{k < n} p_k`; once the total mass is
-- finite, the singleton mass `μ {0}` is automatically finite, so finiteness of the whole measure
-- is equivalent to summability of the prefix-product sequence.
/-- A nontrivial invariant measure is finite exactly when the prefix-product series
`∑ ∏_{k < n} p_k` converges. -/
theorem exists_finite_nontrivial_resetWalkInvariantMeasure_iff_summable_prefixProducts
    (p : ResetWalkParameters) :
    (∃ μ : Measure ℕ, 0 < μ {0} ∧ Kernel.Invariant (resetWalkKernel p) μ ∧ μ Set.univ < ∞) ↔
      Summable (resetWalkPrefixProduct p) := sorry

section ResetWalkRealization

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ resetWalkKernel p ^ n) P X]

-- Proof sketch: for the reset walk, Example 17.52 identifies recurrence with the vanishing of the
-- infinite product `∏' n, p n`; combine that with
-- `resetWalk_tprod_eq_zero_iff_not_summable_one_sub`. The positivity hypothesis makes the
-- realization irreducible in the source sense, so the chain-level criterion is faithful to the
-- textbook statement.
/-- Example 17.52: under the natural realization of the reset walk with `0 < p_n`, the chain is
recurrent exactly when the defect series `∑ (1 - p_n)` diverges, written here as
non-summability. -/
theorem resetWalk_isRecurrentMarkovChain_iff_not_summable_one_sub
    (hp : ∀ n : ℕ, 0 < p n) :
    IsRecurrentMarkovChain P X ↔ ¬ Summable (fun n : ℕ ↦ 1 - p n) := sorry

-- Proof sketch: under `0 < p_n`, the reset walk is irreducible, so positive recurrence is
-- equivalent to existence of a finite invariant measure. The explicit invariant-measure formula
-- above shows that this happens exactly when the prefix-product mass series is finite.
/-- Example 17.52: under the natural realization of the reset walk with `0 < p_n`, the chain is
positive recurrent exactly when the mass series
`M = ∑_{n=0}^\infty ∏_{k=0}^{n-1} p_k` is finite. -/
theorem resetWalk_isPositiveRecurrentMarkovChain_iff_massSeries_lt_top
    (hp : ∀ n : ℕ, 0 < p n) :
    IsPositiveRecurrentMarkovChain P X ↔ resetWalkMassSeries p < ∞ := sorry

end ResetWalkRealization

-- Proof sketch: compare `∏_{k < n} p_k` with the exponential bound
-- `exp (- ∑_{k < n} (1 - p_k))`; summability of the latter implies summability of the former.
/-- The exponential summability condition from the example is sufficient for convergence of the
prefix-product series. -/
theorem summable_resetWalkPrefixProduct_of_summable_exp_neg_sum_one_sub
    (p : ResetWalkParameters) (hp : ∀ n : ℕ, 0 < p n)
    (h : Summable (fun n : ℕ ↦ Real.exp (-Finset.sum (Finset.range n) (fun k ↦ 1 - p k)))) :
    Summable (resetWalkPrefixProduct p) := sorry

end ProbabilityTheory
