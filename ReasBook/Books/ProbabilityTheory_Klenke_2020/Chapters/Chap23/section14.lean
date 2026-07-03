import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_23_14 (from Items/Chap23) -/
open MeasureTheory InformationTheory

noncomputable section

namespace ProbabilityTheory

/-- The two-point space `Σ = {-1,1}` underlying the symmetric Rademacher law. -/
inductive RademacherSign
  | negOne
  | one
  deriving DecidableEq, Fintype, Nonempty

open RademacherSign

/-- The two-point space `RademacherSign` carries the discrete measurable structure. -/
instance : MeasurableSpace RademacherSign := ⊤

/-- The measurable structure on `RademacherSign` is discrete. -/
instance : DiscreteMeasurableSpace RademacherSign := by
  infer_instance

/-- The uniform probability law on `Σ = {-1,1}`. -/
def rademacherUniformLaw : ProbabilityMeasure RademacherSign :=
  ⟨(PMF.uniformOfFintype RademacherSign).toMeasure, inferInstance⟩

-- Proof sketch: unfold `rademacherUniformLaw`; it is defined to be the probability measure coming
-- from the uniform pmf on the two-point space `RademacherSign`.
/-- The uniform law on `RademacherSign` is the measure associated with
`PMF.uniformOfFintype`. -/
theorem rademacherUniformLaw_toMeasure :
    (rademacherUniformLaw : Measure RademacherSign) =
      (PMF.uniformOfFintype RademacherSign).toMeasure := sorry

/-- The magnetization `m(ν) = ν({1}) - ν({-1})` of a probability law on `Σ = {-1,1}`. -/
def rademacherMagnetization (ν : ProbabilityMeasure RademacherSign) : ℝ :=
  (ν {one} : ℝ) - (ν {negOne} : ℝ)

-- Proof sketch: unfold `rademacherMagnetization`; the statement is exactly its defining formula.
/-- The magnetization of a law on `Σ = {-1,1}` is the difference between the masses at `1` and
`-1`. -/
theorem rademacherMagnetization_def (ν : ProbabilityMeasure RademacherSign) :
    rademacherMagnetization ν = (ν {one} : ℝ) - (ν {negOne} : ℝ) := sorry

-- Proof sketch: the two-point space has only the atoms `-1` and `1`, and the Radon-Nikodym
-- derivative of `ν` with respect to the uniform law is constant on each singleton. Expanding the
-- finite two-atom Kullback-Leibler divergence yields the stated logarithmic expression.
/-- Example 23.14: on `Σ = {-1,1}`, modeled by `RademacherSign`, the relative entropy of
`ν ∈ M_1(Σ)` with respect to the uniform law is
`((1 + m(ν)) / 2) log (1 + m(ν)) + ((1 - m(ν)) / 2) log (1 - m(ν))`. This is the same explicit
rate function as in Theorem 23.1. -/
theorem rademacher_relativeEntropy_eq_magnetization_formula
    (ν : ProbabilityMeasure RademacherSign) :
    (klDiv (ν : Measure RademacherSign) (rademacherUniformLaw : Measure RademacherSign)).toReal =
      ((1 + rademacherMagnetization ν) / 2) * Real.log (1 + rademacherMagnetization ν) +
        ((1 - rademacherMagnetization ν) / 2) * Real.log (1 - rademacherMagnetization ν) := sorry

end ProbabilityTheory
