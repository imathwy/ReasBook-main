import ProbabilityTheory_Klenke_2020.Chap05.Theorem_5_7
import ProbabilityTheory_Klenke_2020.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Theorem 5.30: normalize the `N₀`-tail of the sequence `X` by the weights `a`. -/
private def normalizedTail (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ) : ℕ → Ω → ℝ :=
  fun n ω ↦ ((a (n + N0) : ℝ)⁻¹) * X (n + N0) ω

/-- Helper for Theorem 5.30: a `NNReal` sequence tending to `∞` is eventually strictly positive. -/
private lemma eventually_pos_of_tendsto_atTop_nnreal
    (a : ℕ → NNReal) (ha_tendsto : Tendsto a atTop atTop) :
    ∃ N0, ∀ n ≥ N0, 0 < a n := by
  -- Proof comment: since `a n → ∞`, the tail eventually dominates `1`, hence it is positive.
  have h_tail : ∀ᶠ n in atTop, (1 : NNReal) ≤ a n := (tendsto_atTop.1 ha_tendsto) 1
  rcases Filter.mem_atTop_sets.1 h_tail with ⟨N0, hN0⟩
  refine ⟨N0, fun n hn ↦ ?_⟩
  exact zero_lt_one.trans_le (hN0 n hn)

/-- Helper for Theorem 5.30: the normalized tail remains square-integrable termwise. -/
private lemma normalizedTail_memLp
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hX_memLp : ∀ n, MemLp (X n) 2 P) :
    ∀ n, MemLp (normalizedTail X a N0 n) 2 P := by
  intro n
  -- Proof comment: multiplying an `L²` random variable by a scalar preserves membership in `L²`.
  simpa [normalizedTail] using (hX_memLp (n + N0)).const_mul (((a (n + N0) : ℝ)⁻¹))

/-- Helper for Theorem 5.30: centering is preserved by the tail normalization. -/
private lemma normalizedTail_mean_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hX_centered : ∀ n, P[X n] = 0) :
    ∀ n, P[normalizedTail X a N0 n] = 0 := by
  intro n
  -- Proof comment: expectation is linear, so the scalar normalization factors out immediately.
  change P[fun ω ↦ ((a (n + N0) : ℝ)⁻¹) * X (n + N0) ω] = 0
  rw [integral_const_mul, hX_centered]
  simp

/-- Helper for Theorem 5.30: covariance of two normalized tail terms is the rescaled covariance of
the original tail terms. -/
private lemma normalizedTail_covariance_eq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 i j : ℕ) :
    cov[normalizedTail X a N0 i, normalizedTail X a N0 j; P] =
      ((((a (i + N0) : ℝ)⁻¹) * ((a (j + N0) : ℝ)⁻¹)) *
        cov[X (i + N0), X (j + N0); P]) := by
  -- Proof comment: pull the two deterministic normalization factors through covariance.
  change cov[fun ω ↦ ((a (i + N0) : ℝ)⁻¹) * X (i + N0) ω,
      fun ω ↦ ((a (j + N0) : ℝ)⁻¹) * X (j + N0) ω; P] = _
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- Helper for Theorem 5.30: pairwise uncorrelatedness is preserved by the tail normalization. -/
private lemma normalizedTail_pairwise_uncorrelated
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    Pairwise fun i j ↦ cov[normalizedTail X a N0 i, normalizedTail X a N0 j; P] = 0 := by
  intro i j hij
  have hij_shift : i + N0 ≠ j + N0 := by
    exact fun hEq ↦ hij (Nat.add_right_cancel hEq)
  -- Proof comment: after shifting indices, the original covariance hypothesis still applies.
  rw [normalizedTail_covariance_eq]
  simp [hX_uncorrelated hij_shift]

/-- Bridge from the chapter's sequential `partialSum` to the owner `Fin n` finite-sum API. -/
private lemma partialSum_eq_sum_univ {α : Type*} [MeasurableSpace α] (X : ℕ → α → ℝ) (n : ℕ) :
    partialSum X n = ∑ i : Fin n, X i := by
  ext ω
  simpa [partialSum] using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) n).symm

/-- Helper for Theorem 5.30: the variance of a normalized tail term rescales quadratically. -/
private lemma normalizedTail_variance_eq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ) :
    Var[normalizedTail X a N0 n; P] =
      (((a (n + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (n + N0); P] := by
  -- Proof comment: variance is homogeneous of degree two under scalar multiplication.
  change Var[fun ω ↦ ((a (n + N0) : ℝ)⁻¹) * X (n + N0) ω; P] = _
  rw [ProbabilityTheory.variance_const_mul]
  simp [inv_pow]

/-- Helper for Theorem 5.30: the variance of a finite normalized-tail partial sum is the sum of
the term variances. -/
private lemma normalizedTail_partialSum_variance_eq_sum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ)
    (hX_memLp : ∀ k, MemLp (X k) 2 P)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    Var[partialSum (normalizedTail X a N0) n; P] =
      ∑ i ∈ Finset.range n, Var[normalizedTail X a N0 i; P] := by
  let Y : Fin n → Ω → ℝ := fun i ↦ normalizedTail X a N0 i
  have hY_memLp : ∀ i, MemLp (Y i) 2 P := by
    intro i
    simpa [Y] using normalizedTail_memLp P X a N0 hX_memLp i
  have hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    intro i j hij
    have hval : (i : ℕ) ≠ j := by
      intro hEq
      exact hij (Fin.ext hEq)
    simpa [Y] using normalizedTail_pairwise_uncorrelated P X a N0 hX_uncorrelated hval
  calc
    Var[partialSum (normalizedTail X a N0) n; P]
      = Var[∑ i, Y i; P] := by
          rw [partialSum_eq_sum_univ (normalizedTail X a N0) n]
    _ = ∑ i, Var[Y i; P] := by
          simpa using variance_sum_eq_sum_variance_of_pairwise_uncorrelated hY_memLp hY_uncorrelated
    _ = ∑ i ∈ Finset.range n, Var[normalizedTail X a N0 i; P] := by
          simpa [Y] using
            (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Var[normalizedTail X a N0 i; P]) n)

/-- Helper for Theorem 5.30: the variance of a finite normalized-tail partial sum is the shifted
logarithmically weighted variance prefix from the hypothesis. -/
private lemma normalizedTail_partialSum_variance_eq_weighted_sum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ)
    (hX_memLp : ∀ k, MemLp (X k) 2 P)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    Var[partialSum (normalizedTail X a N0) n; P] =
      ∑ i ∈ Finset.range n,
        ((((a (i + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (i + N0); P]) := by
  -- Proof comment: combine orthogonal additivity of variance with the quadratic rescaling formula.
  rw [normalizedTail_partialSum_variance_eq_sum P X a N0 n hX_memLp hX_uncorrelated]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact normalizedTail_variance_eq P X a N0 i

/-- Helper for Theorem 5.30: after shifting by `N₀`, the logarithmically weighted variance series
for the normalized tail is still summable. -/
private lemma normalizedTail_weighted_variance_summable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 : ℕ)
    (hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[X n; P])) :
    Summable (fun n : ℕ ↦ ((Real.log (n + N0 + 1)) ^ 2) * Var[normalizedTail X a N0 n; P]) := by
  -- Proof comment: shift the original series by `N₀`, then rewrite the normalized-tail variances.
  have hshift :
      Summable (fun n : ℕ ↦
        ((Real.log (n + N0 + 1)) ^ 2) *
          (((a (n + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (n + N0); P]) := by
    simpa [add_assoc] using
      ((summable_nat_add_iff N0).2 hseries)
  simpa [normalizedTail_variance_eq, mul_assoc] using hshift

/-- Helper for Theorem 5.30: multiplying the normalized tail by the tail weights recovers the
corresponding tail increment of the original partial sums. -/
private lemma weighted_normalizedTail_partialSum_eq_tail_increment
    (X : ℕ → Ω → ℝ) (a : ℕ → NNReal) (N0 n : ℕ) (ω : Ω)
    (hN0_pos : ∀ k, 0 < a (k + N0)) :
    ∑ i ∈ Finset.range n, (a (i + N0) : ℝ) * normalizedTail X a N0 i ω =
      partialSum X (n + N0) ω - partialSum X N0 ω := by
  -- Proof comment: positivity on the tail lets the weight cancel the normalization factor
  -- termwise, and the remaining shifted sum is exactly the tail increment.
  calc
    ∑ i ∈ Finset.range n, (a (i + N0) : ℝ) * normalizedTail X a N0 i ω
      = ∑ i ∈ Finset.range n, X (i + N0) ω := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hne : (a (i + N0) : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (hN0_pos i))
          rw [normalizedTail, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = ∑ i ∈ Finset.range n, X (N0 + i) ω := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Nat.add_comm]
    _ = ∑ i ∈ Finset.Ico N0 (n + N0), X i ω := by
          symm
          simpa using (Finset.sum_Ico_eq_sum_range (fun i : ℕ ↦ X i ω) N0 (n + N0))
    _ = partialSum X (n + N0) ω - partialSum X N0 ω := by
          symm
          exact partialSum_sub_eq_sum_Ico X (Nat.le_add_left _ _) ω

-- Proof sketch: apply Chebyshev's inequality to the normalized partial sums, use the
-- covariance-zero hypotheses to expand the variance of each `partialSum` into the sum of the
-- individual variances, and then invoke Borel-Cantelli from the summability assumption.
/-- Theorem 5.30: the Rademacher--Menshov criterion. In the canonical `0`-based Lean indexing,
if `X 0, X 1, …` are centered pairwise uncorrelated square-integrable real random variables and
`a 0, a 1, …` is a monotone nonnegative normalizing sequence with `a n → ∞`, then summability of
the real logarithmically weighted variance series implies that the normalized absolute partial
sums have almost-sure limsup `0`. For the textbook sequences `X₁, X₂, …` and `a₁, a₂, …`, apply
this statement to `fun n ↦ X (n + 1)` and `fun n ↦ a (n + 1)`. -/
theorem rademacher_menshov_ae_limsup_weighted_partial_sums_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → NNReal)
    (ha_mono : Monotone a) (ha_tendsto : Tendsto a atTop atTop)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0)
    (hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[X n; P])) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n : ℕ ↦
          ENNReal.ofReal |partialSum X (n + 1) ω| * ((a n : ℝ≥0∞)⁻¹))
        atTop = 0 := by
  obtain ⟨N0, hN0_pos⟩ := eventually_pos_of_tendsto_atTop_nnreal a ha_tendsto
  let Y : ℕ → Ω → ℝ := normalizedTail X a N0
  have hY_memLp : ∀ n, MemLp (Y n) 2 P := by
    -- Proof comment: the normalized tail inherits `L²` bounds termwise from `X`.
    simpa [Y] using normalizedTail_memLp P X a N0 hX_memLp
  have hY_centered : ∀ n, P[Y n] = 0 := by
    -- Proof comment: centering is preserved because each tail term is only rescaled.
    simpa [Y] using normalizedTail_mean_zero P X a N0 hX_centered
  have hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    -- Proof comment: scalar rescaling and a fixed index shift preserve zero covariance.
    simpa [Y] using normalizedTail_pairwise_uncorrelated P X a N0 hX_uncorrelated
  have hY_variance : ∀ n, Var[Y n; P] = (((a (n + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (n + N0); P] := by
    -- Proof comment: this is the exact quadratic rescaling needed for the orthogonal-series route.
    intro n
    simpa [Y] using normalizedTail_variance_eq P X a N0 n
  have hY_log_variance_summable :
      Summable (fun n : ℕ ↦ ((Real.log (n + N0 + 1)) ^ 2) * Var[Y n; P]) := by
    -- Proof comment: the hypothesis `(5.14)` survives the fixed tail shift after normalization.
    simpa [Y] using normalizedTail_weighted_variance_summable P X a N0 hseries
  have hY_partialSum_variance :
      ∀ n, Var[partialSum Y n; P] = ∑ i ∈ Finset.range n, Var[Y i; P] := by
    intro n
    -- Proof comment: pairwise uncorrelatedness lets the variance of each finite prefix add exactly.
    simpa [Y] using normalizedTail_partialSum_variance_eq_sum P X a N0 n hX_memLp hX_uncorrelated
  have hY_partialSum_variance_weighted :
      ∀ n, Var[partialSum Y n; P] =
        ∑ i ∈ Finset.range n, ((((a (i + N0) : ℝ) ^ (2 : ℕ))⁻¹) * Var[X (i + N0); P]) := by
    intro n
    -- Proof comment: each normalized-tail variance is the original variance divided by the square
    -- of the corresponding weight.
    simpa [Y] using
      normalizedTail_partialSum_variance_eq_weighted_sum P X a N0 n hX_memLp hX_uncorrelated
  -- Route correction: the direct single-time Chebyshev route is too weak. The stabilized route now
  -- passes to the normalized tail `Y`, where square-integrability, centering, covariance control,
  -- and the variance-rescaling bridge are already formalized. The remaining gap is now isolated to
  -- the dyadic maximal inequality, the Borel-Cantelli summation step, and the Kronecker bridge.
  -- TODO: prove the dyadic maximal estimate for the partial sums of `Y`, sum the dyadic event
  -- probabilities via Borel-Cantelli using `hseries` and `hY_variance`, then apply a deterministic
  -- Kronecker/Abel summation lemma to recover the normalized partial sums of `X`.
  have hN0_pos' : ∀ n, 0 < a (n + N0) := by
    intro n
    exact hN0_pos (n + N0) (Nat.le_add_left _ _)
  have hY_weighted_prefix :
      ∀ n ω, ∑ i ∈ Finset.range n, (a (i + N0) : ℝ) * Y i ω =
        partialSum X (n + N0) ω - partialSum X N0 ω := by
    intro n ω
    -- Proof comment: this is the exact tail identity needed for the later Kronecker/Abel step.
    simpa [Y] using weighted_normalizedTail_partialSum_eq_tail_increment X a N0 n ω hN0_pos'
  let _ := hN0_pos'
  let _ := ha_mono
  let _ := hseries
  let _ := hY_memLp
  let _ := hY_centered
  let _ := hY_uncorrelated
  let _ := hY_variance
  let _ := hY_log_variance_summable
  let _ := hY_partialSum_variance
  let _ := hY_partialSum_variance_weighted
  let _ := hY_weighted_prefix
  sorry
