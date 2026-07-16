import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap23.Definition_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Topology
open scoped Topology NNReal ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E]

/-- The exponential Laplace functional `∫ exp (φ / ε) dμ_ε` appearing in Varadhan's lemma. -/
def varadhanLaplaceFunctional
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (ε : PositiveParameter) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂(μ ε : Measure E)

-- Proof sketch: unfold `varadhanLaplaceFunctional`.
/-- Unfolding `varadhanLaplaceFunctional` gives the exponential integral
`∫ exp (φ(x) / ε) μ_ε(dx)` as an `ℝ≥0∞`-valued `lintegral`. -/
theorem varadhanLaplaceFunctional_def
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (ε : PositiveParameter) :
    varadhanLaplaceFunctional μ φ ε =
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂(μ ε : Measure E) := sorry

/-- The tail-truncated exponential Laplace functional over the set `{x | M ≤ φ x}`. -/
def varadhanTailLaplaceFunctional
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (M : ℝ) (ε : PositiveParameter) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict {x | M ≤ φ x})

-- Proof sketch: unfold `varadhanTailLaplaceFunctional`.
/-- Unfolding `varadhanTailLaplaceFunctional` gives the exponential integral restricted to the tail
set `{x | M ≤ φ x}`. -/
theorem varadhanTailLaplaceFunctional_def
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (M : ℝ) (ε : PositiveParameter) :
    varadhanTailLaplaceFunctional μ φ M ε =
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict {x | M ≤ φ x}) :=
  sorry

-- Proof sketch: for the lower bound, localize the exponential integral to small neighborhoods of a
-- point `x` and use the LDP lower bound together with continuity of `φ`. For the upper bound,
-- split the integral into the tail part controlled by the hypothesis and the bounded part, cover a
-- compact level set of the good rate function by finitely many neighborhoods, and apply the LDP
-- upper bound to each piece before sending the auxiliary parameters to their limits.
/-- Theorem 23.17: Varadhan's lemma. If `I` is a good rate function, `μ_ε` satisfies the large
deviations principle with rate function `I`, `φ` is continuous, and the tail logarithmic
asymptotics in (23.17) are negligible, then the scaled logarithmic exponential integral converges
to `sup_x (φ x - I x)` as in (23.18). -/
theorem varadhan_lemma
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hI_good : IsGoodRateFunction I)
    (hLDP_open :
      ∀ ⦃U : Set E⦄, IsOpen U →
        -sInf ((fun x ↦ (I x : EReal)) '' U) ≤
          Filter.liminf
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * (((μ ε : Measure E) U).log))
            positiveParameterFilter)
    (hLDP_closed :
      ∀ ⦃C : Set E⦄, IsClosed C →
        Filter.limsup
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * (((μ ε : Measure E) C).log))
            positiveParameterFilter
          ≤ -sInf ((fun x ↦ (I x : EReal)) '' C))
    (hφ : Continuous φ)
    (h_tail :
      sInf (Set.range fun M : {M : ℝ // 0 < M} ↦
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M.1 ε))
          positiveParameterFilter) = ⊥) :
    Tendsto
      (fun ε : PositiveParameter ↦
        ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
      positiveParameterFilter
      (𝓝 (sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))))) := sorry

end ProbabilityTheory
