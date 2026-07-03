import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_1 (from Items/Chap03) -/
open scoped BigOperators

/-- The real-valued power-series extension of the probability generating function of a law on
`ℕ`. -/
noncomputable abbrev probabilityGeneratingFunctionReal (p : PMF ℕ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, (p n).toReal * z ^ n

/-- The real-valued pgf evaluates to its defining power series. -/
theorem probabilityGeneratingFunctionReal_apply (p : PMF ℕ) (z : ℝ) :
    probabilityGeneratingFunctionReal p z = ∑' n : ℕ, (p n).toReal * z ^ n := by
  rfl

/-- The real-valued pgf takes nonnegative values on the unit interval. -/
theorem probabilityGeneratingFunctionReal_nonneg (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    0 ≤ probabilityGeneratingFunctionReal p z := by
  refine tsum_nonneg ?_
  intro n
  exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg z.2.1 n)

/-- The real-valued pgf is bounded above by `1` on the unit interval. -/
theorem probabilityGeneratingFunctionReal_le_one (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal p z ≤ 1 := by
  have hp_summable : Summable (fun n : ℕ ↦ (p n).toReal) := by
    simpa using ENNReal.summable_toReal p.tsum_coe_ne_top
  have hpgf_summable : Summable (fun n : ℕ ↦ (p n).toReal * (z : ℝ) ^ n) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ ↦ (p n).toReal) ?_ ?_ hp_summable
    · intro n
      exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg z.2.1 n)
    · intro n
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ z.2.1 z.2.2)
  have hp_tsum : ∑' n : ℕ, (p n).toReal = 1 := by
    rw [← ENNReal.toReal_one, ← p.tsum_coe, ENNReal.tsum_toReal_eq]
    intro n
    exact p.apply_ne_top n
  calc
    probabilityGeneratingFunctionReal p z = ∑' n : ℕ, (p n).toReal * (z : ℝ) ^ n := rfl
    _ ≤ ∑' n : ℕ, (p n).toReal :=
      hpgf_summable.tsum_le_tsum
        (fun n ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ z.2.1 z.2.2))
        hp_summable
    _ = 1 := hp_tsum

/-- The real-valued pgf maps the unit interval into itself. -/
theorem probabilityGeneratingFunctionReal_mem_unitInterval (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal p z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨probabilityGeneratingFunctionReal_nonneg p z, probabilityGeneratingFunctionReal_le_one p z⟩

/-- Definition 3.1: For an `ℕ`-valued law `p`, its probability generating function is the map
`z ↦ ∑' n, P[X = n] z^n` from `[0,1]` to `[0,1]`, with the convention `0^0 = 1`. -/
noncomputable def probabilityGeneratingFunction (p : PMF ℕ) :
    Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
  fun z ↦
    ⟨probabilityGeneratingFunctionReal p z, probabilityGeneratingFunctionReal_mem_unitInterval p z⟩

/-- On `[0,1]`, the subtype-valued pgf is the real-valued pgf with its range restricted back to
`[0,1]`. -/
theorem probabilityGeneratingFunction_coe_eq_real (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction p z : ℝ) = probabilityGeneratingFunctionReal p z := by
  rfl

/-- The probability generating function evaluates to the defining power series of the law. -/
theorem probabilityGeneratingFunction_apply (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction p z : ℝ) =
      ∑' n : ℕ, (p n).toReal * (z : ℝ) ^ n := by
  rw [probabilityGeneratingFunction_coe_eq_real, probabilityGeneratingFunctionReal_apply]

/-! ### Exercise_3_1_1 (from Items/Chap03) -/
open MeasureTheory

/-- The negative-binomial mass function gives an `ENNReal`-valued probability mass function on
`ℕ` for positive shape parameter `r` and success parameter `p ∈ (0,1]`, using the real-valued
mass function `negativeBinomialMass` from Example 1.105. -/
theorem negativeBinomialMass_hasSum_ennreal (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) :
    HasSum
      (fun k : ℕ ↦ ENNReal.ofReal (negativeBinomialMass r p k))
      1 := by
  apply ENNReal.hasSum_coe.mpr
  simpa using (negativeBinomialMass_hasSum hr hp hp_le_one).toNNReal
    (fun k ↦ negativeBinomialMass_nonneg hr hp hp_le_one k)

/-- The negative-binomial law with parameters `r` and `p`, realized as a probability mass
function on `ℕ`, built from the canonical real-valued mass function `negativeBinomialMass`. -/
noncomputable def negativeBinomialPMF (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun k ↦
      ENNReal.ofReal (negativeBinomialMass r p k),
    negativeBinomialMass_hasSum_ennreal r p hr hp hp_le_one⟩

/-- The point masses of `negativeBinomialPMF` are given by the textbook negative-binomial mass
formula from `negativeBinomialMass`. -/
theorem negativeBinomialPMF_apply (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1)
    (k : ℕ) :
    negativeBinomialPMF r p hr hp hp_le_one k =
      ENNReal.ofReal (negativeBinomialMass r p k) := rfl

/-- The negative-binomial law with parameters `r` and `p`, viewed as a measure on `ℕ`. -/
noncomputable abbrev negativeBinomialMeasure (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) : Measure ℕ :=
  (negativeBinomialPMF r p hr hp hp_le_one).toMeasure

-- Proof sketch: identify the probability generating function of `negativeBinomialMeasure r p hr hp
-- hp_le_one` as `z ↦ (p / (1 - (1 - p) * z)) ^ r`, multiply the generating functions for the two
-- factors, and use uniqueness of probability generating functions on `ℕ`-valued laws.
/-- Exercise 3.1.1: The convolution of the negative-binomial laws with common success parameter
`p ∈ (0,1]` and shape parameters `r,s > 0` is the negative-binomial law with shape parameter
`r + s`. -/
theorem negativeBinomialMeasure_conv (r s p : ℝ) (hr : 0 < r) (hs : 0 < s) (hp : 0 < p)
    (hp_le_one : p ≤ 1) :
    negativeBinomialMeasure r p hr hp hp_le_one ∗
        negativeBinomialMeasure s p hs hp hp_le_one =
      negativeBinomialMeasure (r + s) p (add_pos hr hs) hp hp_le_one := sorry

/-! ### Exercise_3_1_2 (from Items/Chap03) -/
/-- Two probability generating functions agree on an injective sequence of points in `(0,1)`. -/
def ProbabilityGeneratingFunctionsAgreeOnInjectiveSequence (p q : PMF ℕ) : Prop :=
  ∃ x : ℕ → Set.Ioo (0 : ℝ) 1,
    Function.Injective x ∧
      ∀ n : ℕ,
        probabilityGeneratingFunctionReal p (x n) =
          probabilityGeneratingFunctionReal q (x n)

-- Proof sketch: choose two explicit `ℕ`-valued laws whose generating functions have radius of
-- convergence exactly `1`, and use a standard analytic construction so that their difference has
-- infinitely many zeros accumulating only at the boundary point `1`.
/-- Exercise 3.1.2: There exist two distinct real-valued probability generating functions that
agree on an injective sequence of points in `(0,1)`, showing that the extra hypothesis
`ψ z < ∞` for some `z > 1` in Theorem 3.2 (iii) cannot be omitted. -/
theorem distinct_probabilityGeneratingFunctions_agree_on_countably_many_points :
    ∃ p q : PMF ℕ,
      probabilityGeneratingFunctionReal p ≠ probabilityGeneratingFunctionReal q ∧
        ProbabilityGeneratingFunctionsAgreeOnInjectiveSequence p q := sorry
