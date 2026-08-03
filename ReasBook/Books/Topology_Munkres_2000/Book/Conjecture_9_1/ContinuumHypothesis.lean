module

public import Mathlib.SetTheory.Cardinal.Continuum

public section

open scoped Cardinal

namespace Cardinal

universe u

/-- The continuum hypothesis asserts that no cardinal lies strictly between
`ℵ₀` and `𝔠`. -/
def ContinuumHypothesis : Prop :=
  ¬ ∃ c : Cardinal.{u}, ℵ₀ < c ∧ c < 𝔠

/-- The generalized continuum hypothesis asserts that no cardinal lies strictly between an
infinite cardinal `c` and its powerset cardinal `2 ^ c`. -/
def GeneralizedContinuumHypothesis : Prop :=
  ∀ c : Cardinal.{u}, ℵ₀ ≤ c → ¬ ∃ d : Cardinal.{u}, c < d ∧ d < 2 ^ c

/-- The defining no-intermediate-cardinal formulation of the continuum hypothesis. -/
theorem continuumHypothesis_iff :
    ContinuumHypothesis.{u} ↔
      ¬ ∃ c : Cardinal.{u}, ℵ₀ < c ∧ c < 𝔠 := Iff.rfl

/-- The defining no-intermediate-cardinal formulation of the generalized continuum
hypothesis. -/
theorem generalizedContinuumHypothesis_iff :
    GeneralizedContinuumHypothesis.{u} ↔
      ∀ c : Cardinal.{u}, ℵ₀ ≤ c → ¬ ∃ d : Cardinal.{u}, c < d ∧ d < 2 ^ c := Iff.rfl


end Cardinal
