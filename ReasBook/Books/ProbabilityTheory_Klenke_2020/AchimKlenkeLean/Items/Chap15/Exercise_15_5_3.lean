import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Example_15_52

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u v

noncomputable section

/-- A convenient explicit normalization for the inverse-cube-tail central limit theorem. -/
def inverseCubeTailCLTNormingSequence : ℕ → ℝ :=
  fun n ↦ Real.sqrt ((n + 2 : ℝ) * Real.log (n + 2 : ℝ))

-- Proof sketch: rewrite the left-hand side using `hX.map_eq`, then compute the square moment of
-- `symmetricParetoMeasure (1 / 2)` using the density formula from `symmetricParetoDensityReal_eq`;
-- the resulting square moment reduces to `∫_1^∞ x⁻¹ dx`, which diverges.
/-- A random variable with law `symmetricParetoMeasure (1 / 2)`, equivalently with density
`x ↦ |x|⁻³ 1_{ℝ \ [-1,1]}(x)`, has infinite second moment. -/
theorem secondMoment_eq_top_of_hasLaw_inverseCubeTail {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X (symmetricParetoMeasure (1 / 2)) P) :
    ∫⁻ ω, ENNReal.ofReal ((X ω) ^ (2 : ℕ)) ∂P = ⊤ := sorry

-- Proof sketch: this law is centered and lies in the normal domain of attraction of the standard
-- Gaussian with slowly varying truncated second moment `L(t) ~ 2 log t`; apply the
-- one-dimensional domain-of-attraction CLT with the explicit choice
-- `A_n = √((n + 2) log (n + 2))`, using `hX_indep` and `hX_law` to identify the common law of the
-- summands.
/-- Exercise 15.5.3: one explicit norming sequence for i.i.d. real random variables with density
`x ↦ |x|⁻³ 1_{ℝ \ [-1,1]}(x)` is `A_n = √((n + 2) log (n + 2))`; with this normalization, the
partial sums converge in distribution to the standard Gaussian law. -/
theorem tendstoInDistribution_sum_div_inverseCubeTailCLTNormingSequence
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n : ℕ, HasLaw (X (n + 1)) (symmetricParetoMeasure (1 / 2)) P) :
    TendstoInDistribution
      (fun n ω ↦ (inverseCubeTailCLTNormingSequence n)⁻¹ *
        ∑ k ∈ Finset.range n, X (k + 1) ω)
      atTop Y (fun _ ↦ P) P' := sorry
