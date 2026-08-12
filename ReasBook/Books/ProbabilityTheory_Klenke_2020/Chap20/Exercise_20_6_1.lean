import ProbabilityTheory_Klenke_2020.Chap05.Definition_5_25
import ProbabilityTheory_Klenke_2020.Chap20.Definition_20_30
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨by
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    exact AddCircle.measure_univ (1 : ℝ)
  ⟩

/-- The mod-one doubling map on the additive-circle model of `[0,1)`. -/
def modOneDoubling : UnitAddCircle → UnitAddCircle :=
  fun x ↦ (2 : ℤ) • x

-- Proof sketch: multiplication by `2` on `AddCircle 1` is a continuous surjective group
-- endomorphism preserving Haar measure; identify Haar measure on `AddCircle 1` with Lebesgue
-- measure on `[0,1)`.
/-- The mod-one doubling map preserves Lebesgue/Haar measure on the circle. -/
theorem modOneDoubling_measurePreserving :
    MeasurePreserving modOneDoubling volume volume := by
  simpa [modOneDoubling] using
    (Measure.measurePreserving_zsmul volume (by norm_num : (2 : ℤ) ≠ 0))

-- Proof sketch: code the doubling map by binary expansions to obtain a measurable conjugacy with
-- the fair Bernoulli shift on two symbols, then apply the entropy computation for the fair binary
-- shift and evaluate the entropy of the uniform law on `Fin 2`.
/-- The dyadic coding identifies the entropy of the doubling map with the entropy of the fair
binary Bernoulli shift. -/
theorem kolmogorov_sinai_entropy_modOneDoubling_eq_entropy_uniformFinTwo :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) =
      entropy (PMF.uniformOfFintype (Fin 2)) := sorry

/-- Exercise 20.6.1: the Lebesgue-measure entropy of the doubling map `x ↦ 2x (mod 1)` on
`[0,1)` is `log 2`; equivalently, the corresponding system on `AddCircle 1` has entropy `log 2`. -/
theorem kolmogorov_sinai_entropy_modOneDoubling_eq_log_two :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) =
      ((Real.log 2 : ℝ) : EReal) := by
  rw [kolmogorov_sinai_entropy_modOneDoubling_eq_entropy_uniformFinTwo]
  rw [entropy_eq_sum]
  simp [PMF.uniformOfFintype_apply]
