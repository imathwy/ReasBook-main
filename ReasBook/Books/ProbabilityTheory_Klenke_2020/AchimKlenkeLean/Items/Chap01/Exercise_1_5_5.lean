import ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_44
import ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_60

open MeasureTheory Filter
open ProbabilityTheory

open scoped Topology

/-- A finite-dimensional distribution function on `ℝⁿ` is the closed-lower-orthant cumulative
mass function of some probability measure on `ℝⁿ`. -/
def IsFiniteDimensionalDistributionFunction {n : ℕ} (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ μ : ProbabilityMeasure (Fin n → ℝ), ∀ x, F x = (μ : Measure (Fin n → ℝ)).real (Set.Iic x)

/-- A probability measure on `ℝⁿ` realizing a finite-dimensional distribution function by its
closed-lower-orthant cdf is automatically unique. -/
theorem finiteDimensionalDistributionFunction_probabilityMeasure_unique
    {n : ℕ} {F : (Fin n → ℝ) → ℝ} {μ ν : ProbabilityMeasure (Fin n → ℝ)}
    (hμ : ∀ x, F x = (μ : Measure (Fin n → ℝ)).real (Set.Iic x))
    (hν : ∀ x, F x = (ν : Measure (Fin n → ℝ)).real (Set.Iic x)) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  exact probabilityMeasure_eq_of_closedLowerOrthants fun x ↦ by
    have hμ' : F x = μ (Set.Iic x) := by
      simpa using hμ x
    have hν' : F x = ν (Set.Iic x) := by
      simpa using hν x
    have hIic : μ (Set.Iic x) = ν (Set.Iic x) := by
      exact_mod_cast hμ'.symm.trans hν'
    have hIic' : ((μ (Set.Iic x) : NNReal) : ENNReal) = ν (Set.Iic x) := by
      exact_mod_cast hIic
    simpa using hIic'

-- Proof sketch: realize `F` and `G` as the one-dimensional cdfs of probability measures on `ℝ`,
-- take the corresponding Fréchet--Hoeffding upper coupling on `ℝ²`, and identify its lower-orthant
-- cdf with `(x, y) ↦ min (F x) (G y)`.
/-- Exercise 1.5.5 (1): Item (i). If `F` and `G` are distribution functions on `ℝ`, then
`(x, y) ↦ min (F x) (G y)` is a distribution function on `ℝ²`. -/
theorem min_stieltjesDistributionFunctions_isFiniteDimensionalDistributionFunction
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    IsFiniteDimensionalDistributionFunction
      (fun z : Fin 2 → ℝ ↦ min (F (z 0)) (G (z 1))) := sorry

-- Proof sketch: choose two bivariate distribution functions whose rectangle increments satisfy the
-- two-dimensional positivity criterion, then use the four-dimensional inclusion-exclusion
-- criterion on a suitable box to show that the corresponding minimum fails to be a distribution
-- function on `ℝ⁴`.
/-- Exercise 1.5.5 (2): Item (ii). There exist distribution functions `F` and `G` on `ℝ²` such
that the function `(x, y) ↦ min (F x) (G y)` on `ℝ⁴`, obtained by splitting the four coordinates
into two blocks of length `2`, is not a distribution function on `ℝ⁴`. -/
theorem exists_twoDimensionalDistributionFunctions_whose_min_is_not_distributionFunction :
    ∃ F G : (Fin 2 → ℝ) → ℝ,
      IsFiniteDimensionalDistributionFunction F ∧
      IsFiniteDimensionalDistributionFunction G ∧
      ¬ IsFiniteDimensionalDistributionFunction
        (fun z : Fin 4 → ℝ ↦ min (F ![z 0, z 1]) (G ![z 2, z 3])) := sorry
