import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Theorem_1_60
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/- Source-facing layer: the Lévy distance on real distribution functions.
Core owner layer: the Lévy-Prokhorov metric on `ProbabilityMeasure ℝ`.
Bridge layer: pull the owner metric back along the canonical cdf/distribution-function
equivalence `probabilityMeasureEquivDistributionFunction`. -/
private noncomputable def distributionFunctionProbabilityMeasure
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] : ProbabilityMeasure ℝ :=
  probabilityMeasureEquivDistributionFunction.symm ⟨F, inferInstance⟩

private noncomputable def distributionFunctionLevyProkhorov
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    LevyProkhorov (ProbabilityMeasure ℝ) :=
  LevyProkhorov.ofMeasure (distributionFunctionProbabilityMeasure F)

/-- The Lévy distance on real distribution functions is the infimum of the nonnegative radii
`ε` for which `F x` stays between `G (x - ε) - ε` and `G (x + ε) + ε` for every `x`. -/
def levyDistance (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε}

/-- Unfolding `levyDistance F G` gives the textbook infimum formula for the Lévy distance. -/
theorem levyDistance_def
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G =
      sInf {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε} := rfl

private theorem levyDistance_eq_dist_levyProkhorov
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G =
      dist (distributionFunctionLevyProkhorov F) (distributionFunctionLevyProkhorov G) := by
  sorry

-- Proof sketch: compare the textbook infimum formula with the canonical Lévy-Prokhorov metric on
-- the corresponding probability measures, then use nonnegativity of the ambient metric distance.
/-- Exercise 13.2.6 (1): Item (i). The Lévy distance is nonnegative on real distribution
functions. -/
theorem levyDistance_nonneg
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    0 ≤ levyDistance F G := by
  rw [levyDistance_eq_dist_levyProkhorov]
  exact dist_nonneg

-- Proof sketch: identify the textbook Lévy distance with the canonical Lévy-Prokhorov metric, then
-- use the metric-space equality criterion together with injectivity of
-- `probabilityMeasureEquivDistributionFunction.symm`.
/-- Exercise 13.2.6 (2): Item (i). On distribution functions, the Lévy distance vanishes exactly
when the two functions are equal. -/
theorem levyDistance_eq_zero_iff
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G = 0 ↔ F = G := by
  constructor
  · intro h
    have h' :
        distributionFunctionLevyProkhorov F = distributionFunctionLevyProkhorov G := by
      apply eq_of_dist_eq_zero
      simpa [levyDistance_eq_dist_levyProkhorov] using h
    exact congrArg Subtype.val <|
      probabilityMeasureEquivDistributionFunction.symm.injective <|
        congrArg LevyProkhorov.toMeasure h'
  · intro h
    subst h
    simp [levyDistance_eq_dist_levyProkhorov]

-- Proof sketch: compare with the canonical Lévy-Prokhorov metric and use symmetry of `dist`.
/-- Exercise 13.2.6 (3): Item (i). The Lévy distance is symmetric on real distribution
functions. -/
theorem levyDistance_comm
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G = levyDistance G F := by
  simpa [levyDistance_eq_dist_levyProkhorov] using
    dist_comm (distributionFunctionLevyProkhorov F) (distributionFunctionLevyProkhorov G)

-- Proof sketch: compare with the canonical Lévy-Prokhorov metric and use the ambient triangle
-- inequality.
/-- Exercise 13.2.6 (4): Item (i). The Lévy distance satisfies the triangle inequality on real
distribution functions. -/
theorem levyDistance_triangle
    {F G H : StieltjesFunction ℝ}
    [IsDistributionFunction F] [IsDistributionFunction G] [IsDistributionFunction H] :
    levyDistance F H ≤ levyDistance F G + levyDistance G H := by
  simpa [levyDistance_eq_dist_levyProkhorov] using
    dist_triangle
      (distributionFunctionLevyProkhorov F)
      (distributionFunctionLevyProkhorov G)
      (distributionFunctionLevyProkhorov H)

-- Proof sketch: identify distribution functions with probability measures on `ℝ`, use the bridge
-- theorem `levyDistance_eq_dist_levyProkhorov` to replace the source-facing textbook formula by
-- the canonical Lévy-Prokhorov metric, and then transport the convergence characterization back
-- through `probabilityMeasureEquivDistributionFunction`. In the project the source-facing weak
-- convergence predicate is `distribution_function_weakly_converges_to`.
/-- Exercise 13.2.6 (5): Item (ii). A sequence of real distribution functions converges weakly to
`F` exactly when its Lévy distances to `F` converge to `0`. -/
theorem distribution_function_convergence_iff_levyDistance_tendsto_zero
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ) :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F ↔
      Tendsto (fun n ↦ levyDistance (Fs n) F) atTop (𝓝 0) := sorry

-- Proof sketch: approximate `P` by discrete probability measures obtained from quantizing the
-- real line into finer and finer partitions, then show their laws converge weakly to `P`.
/-- Exercise 13.2.6 (6): Item (iii). Every probability measure on `ℝ` is the weak limit of a
sequence of finitely supported probability measures. -/
theorem exists_tendsto_probabilityMeasure_with_finite_support
    (P : ProbabilityMeasure ℝ) :
    ∃ Ps : ℕ → ProbabilityMeasure ℝ,
      (∀ n, ((Ps n : Measure ℝ).support).Finite) ∧
      Tendsto Ps atTop (𝓝 P) := sorry
