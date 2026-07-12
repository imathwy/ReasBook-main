import ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25
import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The finite measure obtained by restricting Lebesgue measure to the unit interval. -/
def unit_interval_restrict_volume : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Icc (0 : ℝ) 1), inferInstance⟩

/-- The canonical uniform empirical distribution on the mesh
`{k / (n + 1) | 0 ≤ k ≤ n + 1}`. -/
noncomputable def unit_interval_mesh_distribution (n : ℕ) : ProbabilityMeasure ℝ :=
  empiricalDistributionTuple (fun k : Fin (Nat.succPNat (n + 1)) ↦ (k : ℝ) / (n + 1 : ℝ))

/-- The empirical finite-measure sequence on the uniform mesh `{k / (n + 1) | 0 ≤ k ≤ n + 1}`.
This keeps the textbook weights `1 / (n + 1)` while deriving the mesh data from the Chapter 12
owner abstraction `empiricalDistributionTuple`. -/
def unit_interval_dirac_riemann_sequence (n : ℕ) : FiniteMeasure ℝ :=
  ((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0)) • (unit_interval_mesh_distribution n).toFiniteMeasure

-- Proof sketch: use `FiniteMeasure.tendsto_iff_forall_integral_tendsto` to test weak convergence
-- against bounded continuous real-valued functions. The resulting integrals are the Riemann sums
-- `(1 / (n + 1)) * ∑_{k=0}^{n+1} f (k / (n + 1))`, which converge to `∫_[0,1] f dλ`; the extra
-- endpoint term is of order `(n + 1)⁻¹` and therefore does not change the limit.
/-- Exercise 13.2.3: after the harmless reindexing `n ↦ n + 1` needed to avoid the undefined term
`1 / 0`, the empirical measures `μₙ = (1 / n) ∑_{k=0}^n δ_{k / n}` converge weakly to Lebesgue
measure restricted to `[0,1]`. -/
theorem unit_interval_dirac_riemann_sequence_tendsto_restrict_volume :
    Tendsto unit_interval_dirac_riemann_sequence atTop (𝓝 unit_interval_restrict_volume) := sorry
