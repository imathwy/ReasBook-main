import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap20.Definition_20_24
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter

universe u v

local instance {E : Type u} [MeasurableSpace E] : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

local instance {ι : Type*} {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    ∀ i : ι, IsProbabilityMeasure ((fun _ : ι ↦ μ) i) :=
  fun _ ↦ inferInstance

-- Proof sketch: approximate arbitrary measurable events in the one-sided product space by
-- cylinder events depending on finitely many coordinates. For sufficiently large shifts, the
-- coordinate supports of the two cylinder approximants are disjoint, so independence under the
-- product measure makes the shifted intersection factor. Passing from cylinders to general
-- measurable sets yields the mixing criterion for the canonical one-sided shift `Stream'.tail`.
/-- Example 20.26: the one-sided Bernoulli product shift on `E^ℕ` is mixing. The bilateral case
is stated separately below. -/
theorem iid_oneSided_product_shift_is_mixing {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    let P : Measure (Stream' E) := Measure.infinitePi (fun _ : ℕ ↦ μ)
    letI : IsProbabilityMeasure P := by
      change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
      infer_instance
    MeasurePreserving Stream'.tail P P ∧ IsStronglyMixing Stream'.tail P :=
    sorry

-- Proof sketch: the same cylinder-approximation argument works on `E^ℤ`. Large forward shifts
-- separate the finite coordinate supports of the approximating cylinder events, and independence
-- under the product measure gives the required factorization, which implies mixing.
/-- The bilateral Bernoulli product shift on `E^ℤ` is mixing. -/
theorem iid_bilateral_product_shift_is_mixing {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (fun ω : ℤ → E ↦ fun n : ℤ ↦ ω (n + 1))
      (Measure.infinitePi (fun _ : ℤ ↦ μ))
      (Measure.infinitePi (fun _ : ℤ ↦ μ)) ∧
      IsStronglyMixing (fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))
        (Measure.infinitePi (fun _ : ℤ ↦ μ)) :=
    sorry

-- Proof sketch: strong mixing implies ergodicity by Remark 20.27, and `PreErgodic.prob_eq_zero_or_one`
-- is then the zero-one law for invariant measurable events.
/-- Any invariant measurable event in a strongly mixing probability-preserving system has
probability `0` or `1`. -/
theorem prob_eq_zero_or_one_of_isStronglyMixing_of_preimage_eq {Ω : Type v}
    [MeasurableSpace Ω] {τ : Ω → Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hτ : MeasurePreserving τ P P) (hstrong : IsStronglyMixing τ P) {A : Set Ω}
    (hA : MeasurableSet A) (hτA : τ ⁻¹' A = A) :
    P A = 0 ∨ P A = 1 := sorry
