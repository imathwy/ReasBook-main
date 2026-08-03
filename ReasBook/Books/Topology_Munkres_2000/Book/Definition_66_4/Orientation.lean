module

public import Topology_Munkres_2000.Book.Definition_66_4.Predicates
public import Topology_Munkres_2000.Book.Lemma_66_1
public import Topology_Munkres_2000.Book.Theorem_66_2

public section

open Set

namespace PlaneLoop

/-- Winding number `1` at one point propagates throughout its connected component in the loop
complement. -/
theorem windingNumber_eq_one_of_mem_connectedComponentIn {x : ℂ} (f : Path x x) (a b : ℂ)
    (h_avoid : a ∉ Set.range f) (h_avoid' : b ∉ Set.range f)
    (h_one : windingNumber f a h_avoid = 1)
    (h_component : b ∈ connectedComponentIn (Set.range f)ᶜ a) :
    windingNumber f b h_avoid' = 1 := by
  -- Constancy on the component transports the given value from `a` to `b`.
  calc
    windingNumber f b h_avoid' = windingNumber f a h_avoid :=
      (windingNumber_eq_of_mem_connectedComponentIn f a b h_component).symm
    _ = 1 := h_one

/-- Winding number `-1` at one point propagates throughout its connected component in the loop
complement. -/
theorem windingNumber_eq_neg_one_of_mem_connectedComponentIn {x : ℂ} (f : Path x x) (a b : ℂ)
    (h_avoid : a ∉ Set.range f) (h_avoid' : b ∉ Set.range f)
    (h_neg_one : windingNumber f a h_avoid = -1)
    (h_component : b ∈ connectedComponentIn (Set.range f)ᶜ a) :
    windingNumber f b h_avoid' = -1 := by
  -- Constancy on the component transports the given value from `a` to `b`.
  calc
    windingNumber f b h_avoid' = windingNumber f a h_avoid :=
      (windingNumber_eq_of_mem_connectedComponentIn f a b h_component).symm
    _ = -1 := h_neg_one

/-- A bounded complementary component of a simple plane loop determines one of the two
orientations. -/
theorem counterclockwise_or_clockwise_of_component_bounded {x : ℂ} (f : Path x x)
    (h_simple : f.toContinuousMap.IsSimpleLoop) (a : ℂ) (h_avoid : a ∉ Set.range f)
    (h_bounded : Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a)) :
    IsCounterclockwise f ∨ IsClockwise f := by
  rcases windingNumber_eq_one_or_neg_one_of_component_bounded
      f a h_simple h_avoid h_bounded with h_one | h_neg_one
  · left
    exact (isCounterclockwise_iff f).2 ⟨a, h_avoid, h_bounded, h_one⟩
  · right
    exact (isClockwise_iff f).2 ⟨a, h_avoid, h_bounded, h_neg_one⟩

/-- Reversing a simple loop preserves simplicity. -/
theorem isSimpleLoop_symm {x : ℂ} (f : Path x x)
    (h_simple : f.toContinuousMap.IsSimpleLoop) :
    f.symm.toContinuousMap.IsSimpleLoop := by
  rw [ContinuousMap.isSimpleLoop_iff] at h_simple ⊢
  constructor
  · -- Reversal exchanges the two equal endpoint values.
    rw [ContinuousMap.isLoop_iff]
    exact f.symm.source.trans f.symm.target.symm
  · -- Reflection is injective and exchanges only the two endpoints.
    intro s₁ s₂ heq
    have hreflected : f (unitInterval.symm s₁) = f (unitInterval.symm s₂) := by
      simpa only [Path.coe_toContinuousMap, Path.symm_apply, Function.comp_apply] using heq
    rcases h_simple.2 _ _ hreflected with h | h | h
    · left
      exact unitInterval.symm_bijective.injective h
    · right
      right
      exact ⟨unitInterval.symm_eq_zero.mp h.1, unitInterval.symm_eq_one.mp h.2⟩
    · right
      left
      exact ⟨unitInterval.symm_eq_one.mp h.1, unitInterval.symm_eq_zero.mp h.2⟩

/-- Reversing a loop exchanges counterclockwise and clockwise orientation. -/
theorem isCounterclockwise_symm_iff {x : ℂ} (f : Path x x) :
    IsCounterclockwise f.symm ↔ IsClockwise f := by
  constructor
  · rw [isCounterclockwise_iff, isClockwise_iff]
    rintro ⟨a, h_avoid_symm, h_bounded, h_one⟩
    have h_avoid : a ∉ Set.range f := by
      simpa only [Path.symm_range] using h_avoid_symm
    refine ⟨a, h_avoid, ?_, ?_⟩
    · simpa only [Path.symm_range] using h_bounded
    · have hreverse := windingNumber_reverse f a h_avoid
      have hone : windingNumber f.symm a (symm_not_mem_range f a h_avoid) = 1 := by
        exact h_one
      rw [hreverse] at hone
      simpa using congrArg Neg.neg hone
  · rw [isCounterclockwise_iff, isClockwise_iff]
    rintro ⟨a, h_avoid, h_bounded, h_neg_one⟩
    refine ⟨a, symm_not_mem_range f a h_avoid, ?_, ?_⟩
    · simpa only [Path.symm_range] using h_bounded
    · rw [windingNumber_reverse f a h_avoid, h_neg_one]
      norm_num

/-- Reversing a loop exchanges clockwise and counterclockwise orientation. -/
theorem isClockwise_symm_iff {x : ℂ} (f : Path x x) :
    IsClockwise f.symm ↔ IsCounterclockwise f := by
  -- Apply the preceding equivalence to the reversed loop and cancel double reversal.
  simpa only [Path.symm_symm] using (isCounterclockwise_symm_iff f.symm).symm

end PlaneLoop
