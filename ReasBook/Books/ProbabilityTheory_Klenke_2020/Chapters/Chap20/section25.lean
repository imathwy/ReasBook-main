import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_20_25 (from Items/Chap20) -/
open Filter MeasureTheory
open scoped BigOperators

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Remark 20.25: a probability-preserving system is weakly mixing when the Cesàro means of the
absolute correlation errors `|P (A ∩ (τ^[i])⁻¹(B)) - P A * P B|` converge to `0` for every pair of
measurable events `A` and `B`. -/
def IsWeaklyMixing (τ : Ω → Ω) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto
      (fun n : ℕ ↦
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|))
      atTop
      (nhds 0)

-- Proof sketch: apply Cesàro summability to the real sequence
-- `P.real (A ∩ (τ^[n])⁻¹(B)) - P.real A * P.real B`, using strong mixing to get convergence of
-- that sequence to
-- `0`; then take absolute values and use the continuity of `abs`.
/-- Strong mixing implies weak mixing. -/
theorem isWeaklyMixing_of_isStronglyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hstrong : IsStronglyMixing τ P) :
    IsWeaklyMixing τ P := sorry

-- Proof sketch: instantiate a standard weakly mixing but not strongly mixing example from the
-- ergodic-theory literature, equip it with its invariant probability measure, and verify the two
-- predicates against that example.
/-- There exist probability-preserving systems that are weakly mixing but not strongly mixing. -/
theorem exists_measurePreserving_weaklyMixing_not_stronglyMixing :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω) (τ : Ω → Ω),
      MeasurePreserving τ (P : Measure Ω) (P : Measure Ω) ∧
      IsWeaklyMixing τ (P : Measure Ω) ∧
      ¬ IsStronglyMixing τ (P : Measure Ω) := sorry
