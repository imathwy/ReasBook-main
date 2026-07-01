import Mathlib
import AchimKlenkeLean.Items.Chap11.Exercise_11_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

local notation "incrementSupNorm" =>
  fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal |X (n + 1) ω - X n ω|
local notation "Converges" =>
  fun ω ↦ ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c)
local notation "PathBddAbove" =>
  fun ω ↦ BddAbove (Set.range fun n ↦ X n ω)
local notation "PathBddBelow" =>
  fun ω ↦ BddBelow (Set.range fun n ↦ X n ω)

/- Exercise 11.2.6 is `source-facing`: it upgrades Exercise 11.2.5 from uniformly bounded
increments to the weaker hypothesis that the pathwise increment envelope has finite expectation.
Its `core/canonical` owner layer is still the martingale convergence API around `Martingale`,
`Submartingale.ae_tendsto_limitProcess`, and the pathwise boundedness/convergence predicates
isolated in Exercise 11.2.5. The increment envelope is only a local `bridge/view` quantity, so it
should not survive as a separate public owner-level definition here. -/

-- Proof sketch: for each level `K`, stop the martingale at a suitable time `ρ_K` before the
-- increment envelope exceeds `K`; the stopped martingale then has uniformly bounded increments, so
-- Exercise 11.2.5 and the martingale convergence theorem apply to it. Letting `K → ∞` and using
-- the integrability of `sup_n |X_{n+1} - X_n|` shows that the stopping events exhaust almost every
-- sample path, yielding the claimed three-way equivalence almost surely.
/-- Exercise 11.2.6: if a real-valued martingale has finite expectation of the supremum of its
absolute increments, then almost every sample path satisfies the same three-way equivalence between
convergence and one-sided boundedness as in Exercise 11.2.5. -/
theorem martingale_convergence_tfae_of_integrable_increment_sup
    (hX : Martingale X ℱ μ)
    (hinc : (∫⁻ ω, incrementSupNorm ω ∂μ) < (⊤ : ENNReal)) :
    ∀ᵐ ω ∂μ,
      List.TFAE [Converges ω, PathBddAbove ω, PathBddBelow ω] := sorry

end
