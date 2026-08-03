module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.LocallyFinite

public section

open Set

universe u v w

/- Exercise 18.9 (a): a function continuous on every member of a finite closed cover is
continuous. A finite family is locally finite, so this is `LocallyFinite.continuous`. -/
#check fun {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [TopologicalSpace X] [TopologicalSpace Y] (A : ι → Set X) (f : X → Y)
    (h_cover : ⋃ i, A i = Set.univ) (h_closed : ∀ i, IsClosed (A i))
    (h_continuous : ∀ i, ContinuousOn f (A i)) ↦
  (locallyFinite_of_finite A).continuous h_cover h_closed h_continuous

/- Exercise 18.9 (b): use the countable closed cover of `ℚ` by singleton subsets and the
`Bool`-valued function that is true exactly at zero. -/
/-- The singleton cover of `ℚ` used in the counterexample. -/
def rationalSingletonCover : ℚ → Set ℚ := fun q ↦ {q}

/-- The `Bool`-valued function on `ℚ` that is true exactly at zero. -/
def rationalZeroIndicator : ℚ → Bool := fun q ↦ decide (q = 0)

/- The collection of rational singleton subsets is countable. -/
#check countable_range rationalSingletonCover

/- The rational singleton subsets cover `ℚ`. -/
#check (iUnion_of_singleton ℚ : ⋃ q, rationalSingletonCover q = Set.univ)

/- Every member of the rational singleton cover is closed. -/
#check fun q : ℚ ↦ (isClosed_singleton : IsClosed (rationalSingletonCover q))

/- The zero indicator is continuous on every rational singleton. -/
#check fun q : ℚ ↦ (continuousOn_singleton rationalZeroIndicator q :
  ContinuousOn rationalZeroIndicator (rationalSingletonCover q))

/-- The rational zero indicator is not continuous. -/
theorem not_continuous_rationalZeroIndicator : ¬Continuous rationalZeroIndicator := by
  intro h_continuous
  -- Continuity into `Bool` would make the fiber over `true` clopen.
  have h_fiber_clopen := (continuous_bool_rng true).mp h_continuous
  -- For this indicator, that fiber is exactly the singleton containing zero.
  have h_fiber : rationalZeroIndicator ⁻¹' {true} = ({0} : Set ℚ) := by
    ext q
    simp [rationalZeroIndicator]
  -- The resulting openness contradicts the fact that rational singletons are not open.
  rw [h_fiber] at h_fiber_clopen
  exact not_isOpen_singleton (0 : ℚ) h_fiber_clopen.isOpen

/- Exercise 18.9 (c): a function continuous on every member of a locally finite closed cover is
continuous. -/
#check LocallyFinite.continuous
