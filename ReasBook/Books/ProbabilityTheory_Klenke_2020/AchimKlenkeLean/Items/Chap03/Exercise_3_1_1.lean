import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Example_1_105

-- Declarations for this item will be appended below by the statement pipeline.

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
