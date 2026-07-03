import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_20_5_1 (from Items/Chap20) -/
open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 20.5.1 (1): strongly mixing implies weak mixing. This is exactly the already
formalized theorem `isWeaklyMixing_of_isStronglyMixing`. -/
recall isWeaklyMixing_of_isStronglyMixing

-- Proof sketch: apply weak mixing to an invariant measurable set `A` with `B = A`. The Cesàro
-- averages then have constant value `|P A - (P A)^2|`, so the weak-mixing limit forces
-- `P A = 0` or `P A = 1`, which is the defining criterion for ergodicity.
/-- Exercise 20.5.1 (2): every weakly mixing probability-preserving dynamical system is ergodic. -/
theorem ergodic_of_isWeaklyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (hweak : IsWeaklyMixing τ P) :
    Ergodic τ P := sorry

-- Proof sketch: combine `mod_one_rotation_ergodic_iff_irrational` with `irrational_pi`,
-- then transport the result from `volume` to `AddCircle.haarAddCircle`. The measure-preserving
-- part is already contained in `Ergodic`. Nontrivial Fourier characters on the additive circle
-- give eigenfunctions for the rotation, so the system is not weakly mixing.
/-- Exercise 20.5.1 (3-5): rotation by `π` on `AddCircle 1` with Haar probability measure is an
ergodic but not weakly mixing dynamical system. -/
theorem rotation_by_pi_ergodic_not_weaklyMixing :
    Ergodic ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle ∧
      ¬ IsWeaklyMixing ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle := by
  constructor
  · simpa [AddCircle.volume_eq_smul_haarAddCircle] using
      ((mod_one_rotation_ergodic_iff_irrational Real.pi).2 irrational_pi)
  · sorry

/-! ### Definition_20_5 (from Items/Chap20) -/
open scoped MeasureTheory
open MeasureTheory

universe u

variable {Ω : Type u}

section MeasurableSpace

variable [MeasurableSpace Ω]

/-- Definition 20.5 (1): an event is invariant if it is measurable and its preimage under `τ`
is itself. -/
def is_invariant_event (τ : Ω → Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ τ ⁻¹' A = A

/-- This unfolds the definition of an invariant event. -/
@[simp] theorem is_invariant_event_iff (τ : Ω → Ω) (A : Set Ω) :
    is_invariant_event τ A ↔ MeasurableSet A ∧ τ ⁻¹' A = A :=
  Iff.rfl

/-- Definition 20.5 (2): an event is quasiinvariant if it agrees almost everywhere with its
preimage under `τ`. -/
def is_quasiinvariant_event (P : Measure Ω) (τ : Ω → Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ τ ⁻¹' A =ᵐ[P] A

/-- This unfolds the definition of a quasiinvariant event. -/
@[simp] theorem is_quasiinvariant_event_iff (P : Measure Ω) (τ : Ω → Ω) (A : Set Ω) :
    is_quasiinvariant_event P τ A ↔ MeasurableSet A ∧ τ ⁻¹' A =ᵐ[P] A :=
  Iff.rfl

/-- This rewrites quasiinvariance in the indicator-function form used in the text. -/
-- Proof sketch: use `indicator_ae_eq_of_ae_eq_set` for the forward implication and recover the
-- set equality almost everywhere by evaluating the indicator functions.
theorem is_quasiinvariant_event_iff_indicator_ae_eq (P : Measure Ω) (τ : Ω → Ω) (A : Set Ω) :
    is_quasiinvariant_event P τ A ↔
      MeasurableSet A ∧
        (τ ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) =ᵐ[P] A.indicator (fun _ ↦ (1 : ℝ)) := by
  rw [is_quasiinvariant_event]
  constructor
  · rintro ⟨hA, hAeq⟩
    exact ⟨hA, indicator_ae_eq_of_ae_eq_set hAeq⟩
  · rintro ⟨hA, hIndicator⟩
    refine ⟨hA, hIndicator.mono ?_⟩
    intro x hx
    by_cases hxA : x ∈ A
    · by_cases hτxA : τ x ∈ A
      · apply propext
        constructor <;> intro _ <;> assumption
      · have : False := by
          simp [hxA, hτxA] at hx
        exact False.elim this
    · by_cases hτxA : τ x ∈ A
      · have : False := by
          simp [hxA, hτxA] at hx
        exact False.elim this
      · apply propext
        constructor <;> intro h
        · exact False.elim <| hτxA h
        · exact False.elim <| hxA h

/- Definition 20.5 (3): the invariant `σ`-algebra is the canonical measurable-space owner
`MeasurableSpace.invariants τ`. -/
recall MeasurableSpace.invariants

/-- This characterizes the measurable sets of the invariant `σ`-algebra in the source-facing
language of invariant events. -/
theorem measurableSet_invariants_iff_is_invariant_event (τ : Ω → Ω) {A : Set Ω} :
    MeasurableSet[MeasurableSpace.invariants τ] A ↔ is_invariant_event τ A := by
  rw [MeasurableSpace.measurableSet_invariants, is_invariant_event]

/-- Definition 20.5 (4): a `σ`-algebra is `P`-trivial if every one of its events has probability
`0` or `1`. -/
def is_p_trivial (P : Measure Ω) [IsProbabilityMeasure P] (I : MeasurableSpace Ω) : Prop :=
  let _ : MeasurableSpace Ω := I
  ∀ A : Set Ω, MeasurableSet A → P A = 0 ∨ P A = 1

end MeasurableSpace
