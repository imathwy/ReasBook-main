import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap11.Lemma_11_18
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap03.Definition_3_9
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap03.Theorem_3_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

section

variable (Z : ℕ → Ω → ℕ) (p : PMF ℕ)
variable (hZ_sm : ∀ n, StronglyMeasurable (Z n))

local notation "m" => ENNReal.toReal (galtonWatsonOffspringMean p)
local notation "ℱZ" => Filtration.natural Z hZ_sm
local notation "W" => branchingNormalizedProcess (fun n ω ↦ (Z n ω : ℝ)) m
local notation "W∞" => Filtration.limitProcess W ℱZ μ

-- Proof sketch: derive the normalized-process martingale from the Galton--Watson owner structure,
-- apply the almost-sure martingale convergence theorem to the normalized population for the
-- natural filtration of `Z`, and combine the finite-variance `L²` bound with Theorem 11.10 and
-- the Chapter 3 supercriticality/extinction criterion for the offspring law `p`.
/- Theorem 11.19 is `source-facing`: it concerns the normalized branching-process population and
the supercriticality criterion expressed through its canonical terminal random variable. Its
`core/canonical` owner layer is the Chapter 3 Galton--Watson owner `IsGaltonWatsonProcess Z μ p`,
the offspring-law mean `galtonWatsonOffspringMean p`, and the normalized process
`branchingNormalizedProcess (fun n ω ↦ (Z n ω : ℝ)) (galtonWatsonOffspringMean p).toReal` for the
natural filtration of `Z`. Any auxiliary offspring array is part of the internal `bridge/view`
layer via `IsGaltonWatsonProcess.exists_offspring`, not the public theorem interface. -/
/-- Theorem 11.19: for a Galton--Watson process `Z` with offspring law `p`, if the offspring
variance is strictly positive, then the normalized population
`W_n = Z_n / (galtonWatsonOffspringMean p)^n` converges almost surely to its canonical limit
process for the natural filtration of `Z`, and the following are equivalent: the offspring mean is
strictly greater than `1`; the expectation of the limit equals `1`; the expectation of the limit
is strictly positive. -/
theorem branchingProcess_normalizedPopulation_limitProcess_and_supercriticality_tfae
    (Z : ℕ → Ω → ℕ) (p : PMF ℕ)
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hvar_pos : 0 < Var[fun k : ℕ ↦ (k : ℝ); p.toMeasure]) :
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ W n ω) atTop (𝓝 (W∞ ω))) ∧
      List.TFAE [1 < m, μ[W∞] = 1, 0 < μ[W∞]] := sorry

end
