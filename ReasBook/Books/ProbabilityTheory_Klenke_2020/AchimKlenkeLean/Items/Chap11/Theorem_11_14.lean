import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

/- Theorem 11.14 is `source-facing`: it is a convergence criterion for a square-integrable
martingale under pathwise boundedness of its square variation. Its `core/canonical` owner layers
are the chapter's square-variation notion from Chapter 10 and mathlib's martingale convergence API
around `ℱ.limitProcess`. The statement below reuses the chapter owner notation `⟨X⟩[ℱ, μ]` and
avoids introducing a parallel wrapper around those owners. -/

-- Proof sketch: for each `K > 0`, stop `X` at the first time when the canonical square variation
-- reaches `K`; the stopped martingale then has uniformly bounded square variation, so Corollary
-- 11.11 gives almost-sure convergence of the stopped process. On the event where the stopping time
-- is infinite, the stopped process agrees with `X`, and these events exhaust almost all sample
-- points because the square variation is almost surely bounded above.
/-- Theorem 11.14: if a square-integrable discrete-time martingale has almost surely bounded
canonical square variation `⟨X⟩[ℱ, μ]`, equivalently `sup_n ⟨X⟩_n < ∞` almost surely, then
the martingale converges almost surely to its canonical limit process. -/
theorem square_integrable_martingale_ae_tendsto_limitProcess_of_ae_bddAbove_squareVariation
    (hX : Martingale X ℱ μ) (hX2 : ∀ n, MemLp (X n) 2 μ)
    (h_bddSquareVariation : ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω)) := sorry

end
