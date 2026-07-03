import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_1_5_1 (from Items/Chap01) -/
-- For an integer shape parameter `n > 0`, the generalized binomial coefficient in the
-- negative-binomial mass formula is the usual waiting-time coefficient.
private theorem negativeBinomialCoefficient_eq_natChoose {n k : ℕ} (hn : 0 < n) :
    Ring.choose (-(n : ℝ)) k * (-1 : ℝ) ^ k = (Nat.choose (n + k - 1) k : ℝ) := by
  rcases n with _ | n
  · cases Nat.not_lt_zero _ hn
  · have hreal : ((n.succ : ℝ) + k - 1) = (n + k : ℝ) := by
      calc
        ((n.succ : ℝ) + k - 1) = ((n : ℝ) + 1 + k - 1) := by norm_num
        _ = (n + k : ℝ) := by ring
    have hnat : n.succ + k - 1 = n + k := by
      omega
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add]
      simp
    rw [Ring.choose_neg, hreal, hnat, ← Nat.cast_add, Ring.choose_natCast]
    simpa [Units.smul_def, Int.cast_negOnePow_natCast, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun x : ℝ ↦ (Nat.choose (n + k) k : ℝ) * x) hsign

/-- Exercise 1.5.1: for an integer shape parameter `n > 0`, evaluating
`negativeBinomialMass` agrees with the combinatorial waiting-time mass for the `n`th success. -/
-- Proof sketch: rewrite the generalized binomial coefficient with `Ring.choose_neg` and
-- `Ring.choose_natCast`, then identify the resulting natural binomial coefficient as the number of
-- sequences with exactly `k` failures before the final success.
theorem negativeBinomialMass_eq_waitingTimeMass {n k : ℕ} (hn : 0 < n) (p : ℝ) :
    negativeBinomialMass (n : ℝ) p k =
      (Nat.choose (n + k - 1) k : ℝ) * p ^ n * (1 - p) ^ k := by
  simp [negativeBinomialMass, negativeBinomialCoefficient_eq_natChoose hn]

/-! ### Exercise_1_5_2 (from Items/Chap01) -/
open MeasureTheory ProbabilityTheory

/-- Exercise 1.5.2: there exists a probability measure on `ℝ × Bool` for which the first
coordinate and the signed first coordinate are both Gaussian random variables, but their pair is
not a two-dimensional Gaussian random variable. -/
-- Proof sketch: take a standard Gaussian variable `Z` together with an independent Rademacher
-- sign `ε`, and set `X = Z` and `Y = εZ`. Then `Y` is again Gaussian, while `(X, Y)` is supported
-- on the two lines `y = x` and `y = -x`, so its joint law is not Gaussian.
theorem exists_gaussian_marginals_without_gaussian_pair :
    ∃ P : ProbabilityMeasure (ℝ × Bool),
      HasGaussianLaw (fun ω : ℝ × Bool ↦ ω.1) (P : Measure (ℝ × Bool)) ∧
      HasGaussianLaw (fun ω ↦ if ω.2 then ω.1 else -ω.1) (P : Measure (ℝ × Bool)) ∧
      ¬ HasGaussianLaw (fun ω ↦ (ω.1, if ω.2 then ω.1 else -ω.1)) (P : Measure (ℝ × Bool)) :=
  sorry

/-! ### Exercise_1_5_3 (from Items/Chap01) -/
open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: combine the canonical scaling law `gaussianReal_const_mul` with the translation
-- law `gaussianReal_add_const`; the hypothesis `a ≠ 0` matches the textbook formulation coming
-- from the transformation formula.
/-- Scaling and translating a Gaussian random variable preserves Gaussianity, with the expected
transformed mean and variance. -/
theorem hasLaw_gaussian_affine
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ a b : ℝ}
    (hX : HasLaw X (gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩) P) :
    HasLaw (fun ω ↦ a * X ω + b)
      (gaussianReal (a * μ + b) ⟨(a * σ) ^ 2, sq_nonneg (a * σ)⟩) P := sorry

/-- Exercise 1.5.3 (1): If a real random variable `X` has Gaussian law `N(μ, σ^2)`, then the
affine transform `aX + b` has Gaussian law `N(aμ + b, a^2σ^2)` for `a ≠ 0`. -/
theorem gaussian_affine_hasLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ a b : ℝ}
    (hX : HasLaw X (gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩) P)
    (_ha : a ≠ 0) :
    HasLaw (fun ω ↦ a * X ω + b)
      (gaussianReal (a * μ + b) ⟨(a * σ) ^ 2, sq_nonneg (a * σ)⟩) P := by
  simpa using hasLaw_gaussian_affine hX

-- Proof sketch: apply the one-dimensional transformation formula to the density defining
-- `expMeasure θ` under the measurable equivalence `x ↦ a * x`, using `a > 0` to preserve the
-- support on `[0, ∞)` and to rewrite the transformed density as the exponential density with rate
-- `θ / a`.
/-- Multiplying an exponentially distributed random variable by a positive scalar divides its rate
by that scalar. -/
theorem hasLaw_exponential_pos_mul
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ a : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hθ : 0 < θ) (ha : 0 < a) :
    HasLaw (fun ω ↦ a * X ω) (expMeasure (θ / a)) P := sorry

/-- Exercise 1.5.3 (2): If a real random variable `X` has exponential law with rate `θ` and
`a > 0`, then the scaled variable `aX` has exponential law with rate `θ / a`. -/
theorem exponential_pos_mul_hasLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ a : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hθ : 0 < θ)
    (ha : 0 < a) :
    HasLaw (fun ω ↦ a * X ω) (expMeasure (θ / a)) P := by
  exact hasLaw_exponential_pos_mul hX hθ ha

/-! ### Exercise_1_5_4 (from Items/Chap01) -/
open Filter MeasureTheory ProbabilityMeasure Set

open scoped Topology

/-- The lower-orthant distribution function of a probability measure on `ℝ × ℝ`, viewed as a
map to `[0,1]`. -/
noncomputable def bivariateMeasureDistributionFunction
    (μ : ProbabilityMeasure (ℝ × ℝ)) : ℝ × ℝ → Icc (0 : ℝ) 1 :=
  fun x ↦ ⟨μ.toMeasure.real (Iic x), measureReal_nonneg, measureReal_le_one⟩

/-- The coercion of the bivariate distribution function back to `ℝ` is the lower-orthant mass
`μ (-∞, x₁] × (-∞, x₂]`. -/
@[simp] theorem bivariateMeasureDistributionFunction_apply
    (μ : ProbabilityMeasure (ℝ × ℝ)) (x : ℝ × ℝ) :
    (bivariateMeasureDistributionFunction μ x : ℝ) = μ (Iic x) := by
  rw [show (bivariateMeasureDistributionFunction μ x : ℝ) = μ.toMeasure.real (Iic x) by rfl]
  exact measureReal_eq_coe_coeFn μ (Iic x)

/-- A bivariate distribution function on `ℝ²` is a `[0,1]`-valued function that is monotone,
right-continuous from the upper-right orthant, has the correct limits at `±∞`, and is
2-increasing on rectangles. -/
class IsBivariateDistributionFunction (F : ℝ × ℝ → Icc (0 : ℝ) 1) : Prop where
  monotone : Monotone F
  right_continuous : ∀ x : ℝ × ℝ, ContinuousWithinAt (fun y ↦ (F y : ℝ)) (Ici x) x
  tendsto_neg_comp_atTop_zero :
    Tendsto (fun x : ℝ × ℝ ↦ (F (-x.1, -x.2) : ℝ)) atTop (𝓝 0)
  tendsto_atTop_one : Tendsto (fun x : ℝ × ℝ ↦ (F x : ℝ)) atTop (𝓝 1)
  rectangle_nonneg : ∀ ⦃x1 y1 x2 y2 : ℝ⦄, x1 ≤ y1 → x2 ≤ y2 →
    0 ≤ (F (y1, y2) : ℝ) - F (y1, x2) - F (x1, y2) + F (x1, x2)

/-- The lower-orthant distribution function of a probability measure on `ℝ × ℝ` satisfies the
standard bivariate distribution-function axioms. -/
instance (μ : ProbabilityMeasure (ℝ × ℝ)) :
    IsBivariateDistributionFunction (bivariateMeasureDistributionFunction μ) := sorry

-- Proof sketch: for the forward implication, use monotonicity and right-continuity of lower-orthant
-- masses and compute rectangle increments by inclusion-exclusion. For the reverse implication,
-- construct the unique Borel probability measure on `ℝ × ℝ` from the 2-increasing,
-- right-continuous lower-orthant function and use `Measure.ext_of_Iic` for uniqueness.
/-- Exercise 1.5.4: a function `F : ℝ² → [0,1]` is the distribution function of a uniquely
determined probability measure on `(ℝ², 𝓑(ℝ²))` if and only if it is monotone increasing and
right-continuous, satisfies `F (-x) → 0` and `F x → 1` as `x → ∞`, and is 2-increasing on
rectangles. -/
theorem existsUnique_probabilityMeasure_with_bivariateDistributionFunction_iff
    (F : ℝ × ℝ → Icc (0 : ℝ) 1) :
    (∃! μ : ProbabilityMeasure (ℝ × ℝ), ∀ x : ℝ × ℝ, (F x : ℝ) = μ (Iic x)) ↔
      IsBivariateDistributionFunction F := sorry

/-! ### Exercise_1_5_5 (from Items/Chap01) -/
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

/-! ### Remark_1_5 (from Items/Chap01) -/
/- Remark 1.5: a "disjoint union" of a family of sets is still the ordinary union as a set;
the extra structure is the pairwise-disjointness condition on the indexed family. Mathlib
expresses that condition by `Set.PairwiseDisjoint`. -/
recall Set.PairwiseDisjoint
