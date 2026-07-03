import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_2_1 (from Items/Chap02) -/
open Set MeasureTheory ProbabilityTheory

noncomputable section

/-- The six outcomes of a single fair die, modeled by `Fin 6`. -/
abbrev Die := Fin 6

/-- The sample space of two successive die rolls. -/
abbrev TwoRolls := Die × Die

/-- The uniform law of a single fair die roll. -/
noncomputable abbrev dieMeasure : Measure Die :=
  (PMF.uniformOfFintype Die).toMeasure

/-- The law of two independent fair die rolls. -/
noncomputable abbrev twoRollMeasure : Measure TwoRolls :=
  dieMeasure.prod dieMeasure

/-- The event that the sum of the two rolls is odd. With the `Fin 6` encoding of die faces by
`0, 1, ..., 5`, this is equivalent to oddness of the textbook face sum after adding `1` to each
coordinate. -/
def oddSumEvent : Set TwoRolls :=
  {ω | Odd ((ω.1 : ℕ) + (ω.2 : ℕ))}

/-- The event that the first roll is at most three. In the `Fin 6` encoding this is the condition
`ω.1 < 3`, corresponding to the textbook faces `{1, 2, 3}`. -/
def firstRollAtMostThreeEvent : Set TwoRolls :=
  {ω | (ω.1 : ℕ) < 3}

-- Proof sketch: under the product law `twoRollMeasure`, the coordinate projections are
-- independent; apply this to the preimages of `A` and `B` under `Prod.fst` and `Prod.snd`.
/-- Example 2.1: Item (i). Under the uniform distribution on two die rolls, an event depending only
on the first roll is independent of an event depending only on the second roll. -/
theorem firstRollCylinder_indep_secondRollCylinder (A B : Set Die) :
    IndepSet (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) twoRollMeasure := sorry

-- Proof sketch: compute the uniform probabilities of `oddSumEvent`,
-- `firstRollAtMostThreeEvent`, and their intersection by counting favorable outcomes in the `36`
-- point sample space, then conclude with the characterization of independence by
-- `μ (A ∩ B) = μ A * μ B`.
/-- Item (ii) of the rolling-two-dice example: the event that the sum is odd is independent of the
event that the first roll is at most three. -/
theorem oddSumEvent_indep_firstRollAtMostThreeEvent :
    IndepSet oddSumEvent firstRollAtMostThreeEvent twoRollMeasure := sorry
