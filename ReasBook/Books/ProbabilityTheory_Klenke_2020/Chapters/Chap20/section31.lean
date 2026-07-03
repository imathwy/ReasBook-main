import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_31 (from Items/Chap20) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {E : Type u} [MeasurableSpace E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

local instance (μ : Measure E) [IsProbabilityMeasure μ] :
    ∀ n : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ μ) n) :=
  fun _ ↦ inferInstance

/- Example 20.31 is a `bridge/view`: for the one-sided Bernoulli product shift on `E^ℕ`, the
Chapter 20 owner `kolmogorov_sinai_entropy` is identified with the Chapter 5 owner `entropy` of
the one-coordinate marginal. -/

/-- The one-sided Bernoulli product shift preserves the corresponding product measure. -/
theorem productShift_measurePreserving (π : PMF E) :
    MeasurePreserving Stream'.tail (Measure.infinitePi (fun _ : ℕ ↦ π.toMeasure))
      (Measure.infinitePi (fun _ : ℕ ↦ π.toMeasure)) :=
  (iid_oneSided_product_shift_is_mixing π.toMeasure).1

-- Proof sketch: the coordinate partition at time `0` is a generator for the one-sided Bernoulli
-- shift under the product measure. Its `n`-block names record the first `n` coordinates, whose law
-- is the `n`-fold product of `π`; the normalized block entropy is therefore constantly `entropy π`.
/-- Example 20.31: the Kolmogorov--Sinai entropy of the one-sided product shift with
one-coordinate marginal `π` is the Shannon entropy `entropy π`. -/
theorem productShiftEntropy_eq_entropy (π : PMF E) :
    h(Measure.infinitePi (fun _ : ℕ ↦ π.toMeasure),
      Stream'.tail, (productShift_measurePreserving π).measurable) = entropy π := by
  sorry

-- Proof sketch: combine `productShiftEntropy_eq_entropy` with the canonical Shannon-series formula
-- `entropy_def`.
/-- The entropy of the one-sided Bernoulli product shift is the Shannon series of the marginal
law. -/
theorem productShiftEntropy_eq_shannon_series (π : PMF E) :
    h(Measure.infinitePi (fun _ : ℕ ↦ π.toMeasure),
      Stream'.tail, (productShift_measurePreserving π).measurable) =
      -∑' e : E, ((π e : EReal) * ENNReal.log (π e)) := by
  rw [productShiftEntropy_eq_entropy, entropy_def]
