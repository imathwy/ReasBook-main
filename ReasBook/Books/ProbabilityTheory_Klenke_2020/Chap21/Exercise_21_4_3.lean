import Mathlib
import ProbabilityTheory_Klenke_2020.Chap07.Definition_7_2
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {p : ℝ}
variable {X : ℕ → NNReal → Ω → ℝ} {Xtilde : NNReal → Ω → ℝ}

private theorem fact_one_le_ofReal_of_one_le (hp : 1 ≤ p) :
    Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp⟩

section TimewiseLpLimit

-- Proof sketch: for each fixed `s ≤ t`, pass to the limit in the martingale identities
-- `E[Xⁿ_t | ℱ_s] = Xⁿ_s`. The owner hypothesis
-- `TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xtilde t)` gives the `L^p` marginals and
-- their timewise convergence, hence `L¹` convergence on the probability space for `p ≥ 1`.
-- Conditional expectation is continuous in `L¹`, so the identities pass to the limit and show
-- directly that the given limit family `X̃` is itself an `ℱ`-martingale.
/-- Exercise 21.4.3 (1): if each deterministic-time slice `X^n_t` converges in `L^p` to
`X̃_t`, then the limit family `X̃` is itself an `ℱ`-martingale. -/
theorem martingale_of_timewise_lp_limit
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hp : 1 ≤ p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp
        TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xtilde t)) :
    Martingale Xtilde ℱ μ := sorry

-- Proof sketch: part (1) first shows that the given limit family `X̃` is already a martingale.
-- For each time horizon `T`, Doob's `L^p` maximal inequality upgrades the owner timewise `L^p`
-- convergence of `Xⁿ - Xᵐ` to convergence of the path suprema on `[0,T]`, so a subsequence
-- converges uniformly almost surely on every compact interval. The limit defines a process with
-- almost surely continuous paths, is a modification of `X̃`, and still receives the same timewise
-- `TendstoInLp` limit.
/-- Exercise 21.4.3 (2): if `p > 1` and every approximating martingale has almost surely
continuous paths, then the timewise `L^p` limit admits a martingale modification with almost
surely continuous paths, and the approximants still converge to that modification in `L^p` at
each deterministic time. -/
theorem exists_continuous_martingale_modification_of_timewise_lp_limit
    (hX : ∀ n : ℕ, Martingale (X n) ℱ μ)
    (hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n))
    (hp : 1 < p)
    (hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
        TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xtilde t)) :
    ∃ Xc : NNReal → Ω → ℝ,
      Martingale Xc ℱ μ ∧
        AreModifications μ Xc Xtilde ∧
        HasAlmostSurelyContinuousPaths μ Xc ∧
        (∀ t : NNReal,
          letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_le hp.le
          TendstoInLp (ENNReal.ofReal p) μ (fun n ↦ X n t) (Xc t)) := sorry

end TimewiseLpLimit

end ProbabilityTheory
