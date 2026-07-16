import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Definition_5_12
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Theorem_5_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable section

omit [IsProbabilityMeasure P] in
private lemma centered_average_eq_partialSum_centered
    (X : ℕ → Ω → ℝ) :
    centered_average P (fun n ↦ X (n + 1)) =
      fun n ω ↦
        partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) n ω / n := by
  funext n ω
  rw [centered_average, centered_partial_sum, partialSum]

-- Proof sketch: combine the pairwise-independent variance estimate for centered partial sums with
-- the bounded-variance hypothesis to obtain summable tail bounds along a dyadic subsequence, apply
-- Borel--Cantelli, and then upgrade the dyadic almost sure convergence of centered averages to the
-- full strong law.
/-- Exercise 5.3.1: the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, satisfies
the strong law of large numbers as soon as its terms are pairwise independent, square integrable,
and have uniformly bounded variances. -/
theorem satisfies_strong_law_of_large_numbers_of_pairwise_indep_memLp_two_bounded_variance
    (X : ℕ → Ω → ℝ) (hX_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (hX_pairwise_indep : Pairwise fun i j ↦ X (i + 1) ⟂ᵢ[P] X (j + 1))
    (hX_var_bdd : BddAbove (Set.range fun n : ℕ ↦ Var[X (n + 1); P])) :
    satisfies_strong_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X (n + 1) ω - P[X (n + 1)]
  have hY_memLp : ∀ n, MemLp (Y n) 2 P := by
    intro n
    exact (hX_memLp n).sub (memLp_const _)
  have hY_centered : ∀ n, P[Y n] = 0 := by
    intro n
    rw [show Y n = fun ω ↦ X (n + 1) ω - P[X (n + 1)] by rfl]
    rw [integral_sub ((hX_memLp n).integrable (by simp)) (integrable_const _)]
    simp
  have hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    intro i j hij
    have hXi_int : Integrable (X (i + 1)) P := (hX_memLp i).integrable (by simp)
    have hXj_int : Integrable (X (j + 1)) P := (hX_memLp j).integrable (by simp)
    have hcov :
        cov[X (i + 1), X (j + 1); P] = 0 :=
      (hX_pairwise_indep hij).covariance_eq_zero (hX_memLp i) (hX_memLp j)
    simpa [Y, hXi_int, hXj_int] using hcov
  have hY_var :
      ∀ n, Var[Y n; P] = Var[X (n + 1); P] := by
    intro n
    simp [Y, variance_sub_const (hX_memLp n).aestronglyMeasurable]
  let a : ℕ → NNReal := fun n ↦ n + 1
  -- Canonical route: apply `rademacher_menshov_ae_limsup_weighted_partial_sums_eq_zero` to the
  -- centered sequence `Y` with the owner normalization `a n = n + 1`, using `hY_var` together
  -- with `hX_var_bdd` to bound the logarithmically weighted variance series, then rewrite the
  -- resulting normalized partial sums back to `centered_average` via
  -- `centered_average_eq_partialSum_centered`.
  refine ⟨fun n ↦ (hX_memLp n).integrable (by simp), ?_⟩
  sorry
