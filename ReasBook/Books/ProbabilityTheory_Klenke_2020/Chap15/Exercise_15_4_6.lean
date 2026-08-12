import ProbabilityTheory_Klenke_2020.Chap15.Theorem_15_37

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u v

variable {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
variable {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

-- Proof sketch: expand the odd power of the partial sum, group terms by mixed moments, use
-- independence and centering to discard the configurations with singleton indices, and count the
-- surviving terms to obtain an `n^(k-1)` bound.
/-- Odd moments of centered iid partial sums grow at most like `n^(k - 1)`. -/
theorem exists_odd_moment_bounds_of_iid_centered
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P) :
    ∃ d : ℕ → ℝ,
      ∀ k n : ℕ,
        1 ≤ k →
          |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ (2 * k - 1) ∂P| ≤
            d (2 * k - 1) * (n : ℝ) ^ (k - 1) := sorry

-- Proof sketch: expand the even power of the partial sum, isolate the leading contribution from
-- pairings of distinct squared factors, identify its combinatorial coefficient
-- `(2k)! / (2^k k!)`, and bound all remaining index patterns by `n^(k-1)`.
/-- Even moments of centered iid partial sums have the Gaussian leading term up to an
`n^(k - 1)` error. -/
theorem exists_even_moment_expansion_bounds_of_iid_centered
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P) :
    ∃ d : ℕ → ℝ,
      ∀ k n : ℕ,
        1 ≤ k →
          |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ (2 * k) ∂P -
              (((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
                (∫ ω, X 0 ω ^ 2 ∂P) ^ k * (n : ℝ) ^ k)| ≤
            d (2 * k) * (n : ℝ) ^ (k - 1) := sorry

-- Proof sketch: apply the characteristic-function derivative formula from Theorem 15.31(i) to a
-- standard Gaussian law and evaluate the odd derivatives at the origin.
/-- Standard Gaussian odd moments vanish. -/
theorem gaussianReal_odd_moments_eq_zero (hY : HasLaw Y (gaussianReal 0 1) P') :
    ∀ k : ℕ,
      ∫ ω, Y ω ^ (2 * k + 1) ∂P' = 0 := sorry

-- Proof sketch: differentiate the standard Gaussian characteristic function at `0`, then compare
-- the resulting even derivatives with the moment formula from Theorem 15.31(i).
/-- Standard Gaussian even moments are the factorial-ratio constants
`(2k)! / (2^k k!)`. -/
theorem gaussianReal_even_moments_eq_factorial_ratio (hY : HasLaw Y (gaussianReal 0 1) P') :
    ∀ k : ℕ,
      ∫ ω, Y ω ^ (2 * k) ∂P' =
        (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ)) := sorry

-- Proof sketch: combine the moment bounds from the odd and even expansions with the Gaussian
-- moment identities, use the moment-convergence criterion from Exercise 15.4.5, and then pass
-- from convergence of moments to convergence in distribution against a standard Gaussian limit law.
/-- Centered iid real variables with finite absolute moments of every order have standardized
partial sums converging in distribution to the standard Gaussian law. -/
theorem standardizedPartialSum_tendstoInDistribution_standardGaussian_of_iid_all_moments
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    (hvar : Var[X 0; P] ≠ 0)
    (hY : HasLaw Y (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ↦ standardizedPartialSum P X n) atTop Y (fun _ ↦ P) P' := sorry

-- Proof sketch: first obtain convergence in distribution of `standardizedPartialSum P X n` to a
-- standard Gaussian variable from the previous theorem, then rewrite this as convergence of the
-- associated pushforward probability measures in
-- `ProbabilityMeasure ℝ`.
/-- Exercise 15.4.6: item (iii). If `X₁, X₂, ...` are iid centered real random variables with
finite absolute moments of every order and nonzero variance, then the laws of the standardized
partial sums `S_n^*` converge weakly to the standard Gaussian law. -/
theorem standardizedPartialSumLaw_tendsto_standardGaussian_of_iid_all_moments
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    (hvar : Var[X 0; P] ≠ 0) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map ⟨P, inferInstance⟩
          (aemeasurable_standardizedPartialSum P X (fun n ↦ (hident n).aemeasurable_fst) n))
      atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := sorry
