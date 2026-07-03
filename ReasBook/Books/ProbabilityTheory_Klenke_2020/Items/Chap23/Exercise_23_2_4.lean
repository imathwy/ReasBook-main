import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap15.Example_15_33
import ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Helper for the source-facing rate formula below: evaluate the exponential moment of
-- `expMeasure θ` by the standard density integral on `(0, ∞)`, obtaining `θ / (θ - t)`, and then
-- pass to the chapter owner `extendedLogMomentGeneratingFunction`.
private theorem extendedLogMomentGeneratingFunction_id_expMeasure_of_lt
    {θ t : ℝ} (hθ : 0 < θ) (ht : t < θ) :
    Λ(id; expMeasure θ) t = Real.log (θ / (θ - t)) := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hmgf : mgf id (expMeasure θ) t = θ / (θ - t) :=
    expMeasure_mgf_eq θ hθ ht
  have hmgf_pos : 0 < mgf id (expMeasure θ) t := by
    rw [hmgf]
    exact div_pos hθ (sub_pos.mpr ht)
  have ht_mem : t ∈ integrableExpSet id (expMeasure θ) :=
    (mgf_pos_iff).1 hmgf_pos
  calc
    Λ(id; expMeasure θ) t = (cgf id (expMeasure θ) t : EReal) := by
      simpa using
        extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
          id (expMeasure θ) ht_mem
    _ = Real.log (θ / (θ - t)) := by
      rw [cgf, hmgf]

-- Helper for the source-facing rate formula below: when `t ≥ θ`, the exponential moment
-- diverges, so the chapter owner `extendedLogMomentGeneratingFunction` takes the value `∞`.
private theorem extendedLogMomentGeneratingFunction_id_expMeasure_of_ge
    {θ t : ℝ} (hθ : 0 < θ) (ht : θ ≤ t) :
    Λ(id; expMeasure θ) t = ⊤ := by
  simpa using
    extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      id (expMeasure θ) (expMeasure_not_mem_integrableExpSet_of_ge θ hθ ht)

-- Proof sketch: split on `0 < x`; on the positive branch, substitute the explicit optimizer
-- `t = θ - 1 / x` into the Legendre transform of `Λ`, and on the nonpositive branch use that the
-- supremum diverges to `∞`.
/-- Exercise 23.2.4: for the exponential law with rate `θ`, the Legendre transform `Λ*` is
`x ↦ θ x - log (θ x) - 1` on `(0, ∞)` and `∞` on `(-∞, 0]`. -/
theorem legendreFenchelRateFunction_id_expMeasure_eq
    {θ x : ℝ} (hθ : 0 < θ) :
    legendreFenchelRateFunction (Λ(id; expMeasure θ)) x =
      if 0 < x then ((θ * x - Real.log (θ * x) - 1 : ℝ) : EReal) else ⊤ := sorry

-- Proof sketch: on `(0, ∞)`, differentiate `x ↦ θ x - log (θ x) - 1` and solve
-- `θ - 1 / x = 0`, obtaining `x = 1 / θ`; strict convexity then shows this is the unique zero.
/-- The exponential-law Legendre transform has its unique zero at the mean `1 / θ` of `Exp(θ)`. -/
theorem legendreFenchelRateFunction_id_expMeasure_eq_zero_iff {θ x : ℝ} (hθ : 0 < θ) :
    legendreFenchelRateFunction (Λ(id; expMeasure θ)) x = 0 ↔ x = 1 / θ := sorry

-- `bridge/view` layer: the source-facing exercise statement specializes the Chapter 23 owner
-- theorem `cramer_empiricalMean_largeDeviationPrinciple` to the exponential law and then rewrites
-- the rate through the chapter owner `legendreFenchelRateFunction (Λ(id; expMeasure θ))`, whose
-- explicit source-facing formula is recorded above.
/-- For an i.i.d. sequence with common law `Exp(θ)`, the normalized partial sums satisfy the large
deviation principle with the canonical Chapter 23 rate function
`legendreFenchelRateFunction (Λ(id; expMeasure θ))`. The companion theorem
`legendreFenchelRateFunction_id_expMeasure_eq` records the textbook explicit formula for this
rate. -/
theorem normalizedPartialSumLaw_satisfiesLargeDeviationPrinciple_of_hasLaw_expMeasure
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {θ : ℝ}
    (hθ : 0 < θ) (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) (expMeasure θ) P) :
    SatisfiesLargeDeviationPrinciple (normalizedPartialSumLaw X P)
      (legendreFenchelRateFunction (Λ(id; expMeasure θ))) := sorry

end ProbabilityTheory
