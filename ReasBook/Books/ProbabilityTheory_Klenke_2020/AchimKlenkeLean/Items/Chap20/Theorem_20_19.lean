import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_34
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

universe u

variable {E : Type u}

section PathSpace

variable [AddCommMonoid E]

/-- The partial sum `S_n = X₀ + ⋯ + X_{n-1}` of a one-sided increment path `ω`. -/
def randomWalkPathPartialSum (ω : ℕ → E) (n : ℕ) : E :=
  ∑ i ∈ Finset.range n, ω i

/-- The event that the walk never returns to the origin after time `0`. -/
def neverReturnsToOriginEvent : Set (ℕ → E) :=
  {ω | ∀ n : ℕ, 0 < n → randomWalkPathPartialSum ω n ≠ 0}

-- Proof sketch: unfold `randomWalkPathPartialSum` at `0`; the finite sum over an empty range
-- vanishes.
/-- The zeroth partial sum of a path is the origin. -/
theorem randomWalkPathPartialSum_zero (ω : ℕ → E) :
    randomWalkPathPartialSum ω 0 = 0 := by
  simp [randomWalkPathPartialSum]

-- Proof sketch: unfold `neverReturnsToOriginEvent`; membership is exactly the stated no-return
-- condition on positive times.
/-- Membership in `neverReturnsToOriginEvent` is the no-return condition for all positive times. -/
theorem mem_neverReturnsToOriginEvent_iff (ω : ℕ → E) :
    ω ∈ neverReturnsToOriginEvent ↔
      ∀ n : ℕ, 0 < n → randomWalkPathPartialSum ω n ≠ 0 :=
  Iff.rfl

/-- The range count `R_n`, i.e. the number of distinct visited partial sums `S₀, …, S_n`. -/
noncomputable def randomWalkPathRangeCount (ω : ℕ → E) (n : ℕ) : ℕ :=
  (Set.range fun k : Fin (n + 1) ↦ randomWalkPathPartialSum ω k).ncard

-- Proof sketch: at time `0` the walk has visited only the initial position `0`, so the image of
-- `range 1` under the partial-sum map is the singleton `{0}`.
/-- The initial range count is `1`, corresponding to the starting point alone. -/
theorem randomWalkPathRangeCount_zero (ω : ℕ → E) :
    randomWalkPathRangeCount ω 0 = 1 := by
  simp [randomWalkPathRangeCount, randomWalkPathPartialSum]

end PathSpace

section Measurability

variable [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Each finite random-walk partial sum on path space is measurable. -/
theorem measurable_randomWalkPathPartialSum (n : ℕ) :
    Measurable (fun ω : ℕ → E ↦ randomWalkPathPartialSum ω n) := by
  simpa [randomWalkPathPartialSum] using
    Finset.measurable_sum (Finset.range n) fun i _ ↦ measurable_pi_apply i

variable [MeasurableSingletonClass E]

/-- The no-return event is measurable on path space once addition and singleton fibers are
measurable on the state space. -/
theorem measurableSet_neverReturnsToOriginEvent :
    MeasurableSet (neverReturnsToOriginEvent : Set (ℕ → E)) := by
  have h_eq :
      (neverReturnsToOriginEvent : Set (ℕ → E)) =
        ⋂ n : {n : ℕ // 0 < n},
          (fun ω : ℕ → E ↦ randomWalkPathPartialSum ω n.1) ⁻¹' ({(0 : E)}ᶜ) := by
    ext ω
    simp [neverReturnsToOriginEvent]
  rw [h_eq]
  refine MeasurableSet.iInter fun n ↦ ?_
  exact measurable_randomWalkPathPartialSum n.1
    (measurableSet_singleton (0 : E)).compl

end Measurability

section CancellativeMeasurability

variable [AddCancelCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
variable [MeasurableSingletonClass E]

local instance theorem2019MeasurableSpaceStream : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

local notation "ℐ" => MeasurableSpace.invariants Stream'.tail

-- Proof sketch: use the owner abstraction `IsStationaryProcess Function.eval P` for the canonical
-- coordinate process on path space; via the Chapter 20 bridge this is the shift-invariance of the
-- path law under `Stream'.tail`. In a cancellative additive state space, the event
-- `neverReturnsToOriginEvent` on the shifted increment path is exactly the event that the original
-- walk never revisits its current position after the shift time. Apply Birkhoff's ergodic theorem
-- to the indicators of this event and its finite-horizon approximations. The lower and upper
-- bounds on `R_n / n` coming from last-visit indicators then squeeze the limit to the conditional
-- probability `P⟦A | 𝒯⟧` of the no-return event `A` given the invariant `σ`-algebra
-- `𝒯 = MeasurableSpace.invariants Stream'.tail` of the shift.
/-- Theorem 20.19: for the canonical coordinate process on path space under a stationary path
law with values in a cancellative commutative additive state space, the normalized range count
converges almost surely to the conditional probability of the no-return event given the invariant
`σ`-algebra `𝒯 = MeasurableSpace.invariants Stream'.tail` of the shift. Cancellativity is the
structural hypothesis that identifies the no-return event of the shifted increment path with the
event that the original walk never revisits its current position after the shift time. The
measurability hypotheses on `E` ensure that this no-return event is a genuine measurable event, so
the right-hand side is canonically `P⟦neverReturnsToOriginEvent | ℐ⟧`. Example 20.12 supplies only
the bridge `ℐ ≤ tailRandomVariableMeasurableSpace Function.eval`, so the source-facing theorem must
stay at the invariant owner rather than the tail view. -/
theorem randomWalkPathRangeCount_tendsto_ae_condProb_invariants
    (P : Measure (ℕ → E)) [IsProbabilityMeasure P]
    (hstationary : IsStationaryProcess Function.eval P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (randomWalkPathRangeCount ω n : ℝ) / n) atTop
        (nhds ((P⟦neverReturnsToOriginEvent | ℐ⟧) ω)) := sorry

end CancellativeMeasurability
