import ProbabilityTheory_Klenke_2020.Chap01.Exercise_1_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A binary digit is turned into the corresponding base-four digit `0` or `3`. -/
private def duplicatedBaseFourDigit (b : Bool) : Fin 4 :=
  cond b 3 0

/-- The base-four expansion obtained by replacing binary digits with `0` and `3`. -/
private noncomputable def duplicatedBaseFourMap (ω : BernoulliSequence) : unitInterval :=
  ⟨Real.ofDigits fun n ↦ duplicatedBaseFourDigit (ω n),
    ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩⟩

/-- The textbook binary digits on `[0,1]`: at positive dyadic rationals below `1`, replace the
terminating-zero expansion `...1000` by the equivalent eventually-one expansion `...0111`. -/
private noncomputable def textbookBinaryDigits (x : unitInterval) : BernoulliSequence :=
  let ω := canonicalBinaryDigits x
  if hω : ∃ N, 0 < N ∧ ω (N - 1) = true ∧ ∀ n ≥ N, ω n = false then
    let N := Nat.find hω
    fun n ↦ if n + 1 < N then ω n else if n + 1 = N then false else true
  else
    ω

/-- Exercise 7.4.1: the map `F : [0,1] → [0,1]` obtained by duplicating the textbook binary digits
of `x` into base-four digits `0` and `3`, using the eventually-one expansion at dyadic rationals
below `1`. -/
noncomputable def dyadicDuplicationMap (x : unitInterval) : unitInterval :=
  duplicatedBaseFourMap (textbookBinaryDigits x)

/-- The image measure of the uniform distribution on `[0,1]` under `dyadicDuplicationMap`. -/
noncomputable def dyadicDuplicationMeasure : Measure ℝ :=
  Measure.map (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) volume

/-- `dyadicDuplicationMeasure` is the pushforward of the uniform measure on `[0,1]` under
`dyadicDuplicationMap`. -/
@[simp] theorem dyadicDuplicationMeasure_eq_map_dyadicDuplicationMap :
    dyadicDuplicationMeasure =
      Measure.map (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) volume :=
  rfl

/-- The canonical pushforward description of `dyadicDuplicationMeasure` agrees with the Bernoulli
realization `F(U)` from Chapter 1. -/
theorem dyadicDuplicationMeasure_eq_map_fromBinary :
    dyadicDuplicationMeasure =
      Measure.map (fun ω : BernoulliSequence ↦ (dyadicDuplicationMap (Real.fromBinary ω) : ℝ))
        fairBernoulliMeasure := sorry

-- Proof sketch: identify the mass of a singleton with the probability of a single digit sequence;
-- the Bernoulli digit model has no dyadic ambiguity, so every singleton has measure `0`.
-- A monotone right-continuous cdf with no atoms is continuous.
/-- Exercise 7.4.1 (1): the distribution function of the image measure is continuous. -/
theorem dyadicDuplicationMeasure_cdf_continuous :
    Continuous (cdf dyadicDuplicationMeasure) := sorry

-- Proof sketch: the image of `dyadicDuplicationMap` is contained in the classical Cantor-type set
-- of numbers whose base-four digits are only `0` or `3`; that set has Lebesgue measure `0`, while
-- the pushforward measure assigns it full mass, yielding mutual singularity.
/-- Exercise 7.4.1 (2): the image measure is singular with respect to Lebesgue measure on
`(0,1]`. -/
theorem dyadicDuplicationMeasure_mutuallySingular_restrict_volume :
    dyadicDuplicationMeasure ⟂ₘ volume.restrict (Set.Ioc (0 : ℝ) 1) := sorry

end
