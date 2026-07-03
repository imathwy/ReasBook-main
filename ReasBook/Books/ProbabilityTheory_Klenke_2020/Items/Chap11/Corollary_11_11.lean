import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_4
import ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

-- Proof sketch: use Theorem 10.4 to identify the expectations of the canonical square variation
-- with the variances of the martingale increments via
-- `squareVariation_expectation_eq_variance`, so (i) and (ii) are equivalent. Then apply the
-- owner martingale convergence theorem
-- `MeasureTheory.martingale_convergence_to_memLp_limitProcess_of_lp_bounded` at `p = 2` to pass
-- from uniform `L²` boundedness to almost-sure and `L²` convergence, while the implications
-- `(iv) → (iii) → (i)` are immediate.
/-- Corollary 11.11: for a square-integrable discrete-time martingale with canonical square
variation process `⟨X⟩[ℱ, μ]`, the following are equivalent:
(i) the second moments `μ[(X n)^2]` are uniformly bounded;
(ii) the expectations of the square variation converge to a finite limit;
(iii) the martingale converges in `L²` to the canonical limit `ℱ.limitProcess X μ`;
(iv) the martingale converges almost surely and in `L²` to `ℱ.limitProcess X μ`. -/
theorem square_integrable_martingale_tfae {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ) :
    let squareVariation : ℕ → Ω → ℝ := predictablePart (fun n ω ↦ X n ω ^ 2) ℱ μ
    let uniformlyBoundedSecondMoments : Prop :=
      Exists fun C : ℝ ↦ ∀ n, μ[fun ω ↦ X n ω ^ 2] ≤ C
    let convergentSquareVariationExpectation : Prop :=
      Exists fun a : ℝ ↦ Tendsto (fun n ↦ μ[squareVariation n]) atTop (𝓝 a)
    List.TFAE [
      uniformlyBoundedSecondMoments,
      convergentSquareVariationExpectation,
      TendstoInLp 2 μ X (ℱ.limitProcess X μ),
      (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
        TendstoInLp 2 μ X (ℱ.limitProcess X μ)
    ] := sorry
