import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_37 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u

noncomputable section

/-- The standardized partial sum appearing in the central limit theorem, written with Lean's
`0`-based indexing for the i.i.d. sequence. -/
def standardizedPartialSum {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ (Real.sqrt (n * Var[X 0; P]))⁻¹ *
    (Finset.sum (Finset.range n) (fun k ↦ X k ω) - n * P[X 0])

-- Proof sketch: combine the `AEMeasurable` hypotheses for the summands, then use closure of
-- `AEMeasurable` under finite sums, subtraction of constants, and scalar multiplication.
/-- The standardized partial sums are measurable whenever the underlying sequence is measurable. -/
theorem aemeasurable_standardizedPartialSum {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, AEMeasurable (X n) P) (n : ℕ) :
    AEMeasurable (standardizedPartialSum P X n) P := sorry

-- Proof sketch: apply the one-dimensional central limit theorem in mathlib to the centered sums
-- `(√n)⁻¹ (∑_{k < n} X k - n * P[X 0])`, then use the continuous mapping theorem for division by
-- `√(Var[X 0; P])` to identify the limit law as `gaussianReal 0 1`.
/-- Theorem 15.37 (1): the laws of the standardized partial sums converge weakly to the standard
Gaussian law. -/
theorem standardizedPartialSumLaw_tendsto_standardGaussian {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 P)
    (hVar : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map ⟨P, inferInstance⟩
          (aemeasurable_standardizedPartialSum P X (fun k ↦ (hident k).aemeasurable_fst) n))
      atTop
      (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := sorry

-- Proof sketch: combine the weak convergence from part (1) with the portmanteau theorem for the
-- Borel set `((↑) : ℝ → EReal) ⁻¹' Set.Icc a b`, using absolute continuity of `gaussianReal 0 1` to see
-- that its boundary has measure zero; then rewrite the limiting Gaussian mass as the integral of
-- the standard Gaussian density over that interval.
/-- Theorem 15.37 (2): for `-∞ ≤ a < b ≤ +∞`, the probabilities of the standardized partial sums
falling in the closed interval determined by `a` and `b` converge to the integral of the standard
Gaussian density over that interval. -/
theorem standardizedPartialSum_intervalProb_tendsto {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 P)
    (hVar : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P) {a b : EReal} (hab : a < b) :
    Tendsto
      (fun n ↦
        ((ProbabilityMeasure.map ⟨P, inferInstance⟩
            (aemeasurable_standardizedPartialSum P X (fun k ↦ (hident k).aemeasurable_fst) n) :
            Measure ℝ).real (((↑) : ℝ → EReal) ⁻¹' Set.Icc a b)))
      atTop
      (𝓝
        (∫ x, Set.indicator ((((↑) : ℝ → EReal) ⁻¹' Set.Icc a b)) (gaussianPDFReal 0 1) x
          ∂volume)) := sorry
