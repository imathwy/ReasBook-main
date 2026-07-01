import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_66

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ

-- Proof sketch: choose a localizing sequence for `M`; each stopped process is a martingale, so
-- for `A ∈ ℱ s` one has equality of expectations on `A ∩ {τₙ ≤ s}`. The uniform almost-sure bound
-- gives integrability of every time slice, and dominated convergence lets `n → ∞` pass through the
-- stopped identities to recover the martingale conditional-expectation relation for `M` itself.
/-- Remark 21.68: on a probability space, a bounded local martingale is a martingale. The same
argument only uses that `μ` has finite total mass, so we state the result for an arbitrary finite
measure. Here boundedness means that there is a deterministic constant `C` such that
`|M t ω| ≤ C` almost surely for every `t ≥ 0`. -/
theorem martingale_of_bounded_local_martingale
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ}
    (hlocal : IsLocalMartingale ℱ μ M)
    (hbounded : ∃ C : ℝ, ∀ t : NNReal, ∀ᵐ ω ∂μ, |M t ω| ≤ C) :
    Martingale M ℱ μ := sorry

end ProbabilityTheory
