module

public import Mathlib.Topology.Homotopy.Basic

public section

noncomputable section

open unitInterval

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- A continuous map from the unit interval whose endpoint values agree. -/
def IsLoop (f : C(unitInterval, X)) : Prop :=
  f 0 = f 1

/-- A continuous map is a loop exactly when its endpoint values agree. -/
theorem isLoop_iff {f : C(unitInterval, X)} : IsLoop f ↔ f 0 = f 1 :=
  Iff.rfl

/-- A free homotopy between loops, represented by a homotopy all of whose slices are loops. -/
abbrev FreeHomotopy (f₀ f₁ : C(unitInterval, X)) :=
  HomotopyWith f₀ f₁ IsLoop

namespace FreeHomotopy

/--
Constructs a free homotopy from a continuous square map in the source's coordinates: the first
coordinate parametrizes the loops and the second coordinate parametrizes the homotopy.
-/
def ofSquare {f₀ f₁ : C(unitInterval, X)} (F : C(unitInterval × unitInterval, X))
    (map_zero_right : ∀ s, F (s, 0) = f₀ s) (map_one_right : ∀ s, F (s, 1) = f₁ s)
    (apply_zero_eq_apply_one : ∀ t, F (0, t) = F (1, t)) : FreeHomotopy f₀ f₁ where
  toHomotopy :=
    { toContinuousMap := F.comp .prodSwap
      map_zero_left := map_zero_right
      map_one_left := map_one_right }
  prop' := apply_zero_eq_apply_one

/-- The continuous square map underlying a free homotopy, in loop-parameter-first coordinates. -/
@[expose]
def square {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁) :
    C(unitInterval × unitInterval, X) :=
  F.toHomotopy.toContinuousMap.comp .prodSwap

/-- Evaluating the source-coordinate square recovers the underlying free homotopy. -/
@[simp]
theorem square_apply {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁)
    (s t : unitInterval) : F.square (s, t) = F (t, s) :=
  rfl

/-- Every time slice of a free homotopy is a loop. -/
theorem isLoop {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁) (t : unitInterval) :
    IsLoop (F.toHomotopy.curry t) :=
  F.prop t

/-- At each time, the two loop-parameter endpoint values of a free homotopy agree. -/
theorem apply_zero_eq_apply_one {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁)
    (t : unitInterval) : F (t, 0) = F (t, 1) :=
  F.isLoop t

/-- The source of a free homotopy is a loop. -/
theorem source_isLoop {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁) : IsLoop f₀ := by
  simpa using F.isLoop 0

/-- The target of a free homotopy is a loop. -/
theorem target_isLoop {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁) : IsLoop f₁ := by
  simpa using F.isLoop 1

/-- A point avoided by a free homotopy is avoided by its source loop. -/
theorem source_not_mem_range {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁)
    (a : X) (h_avoid : a ∉ Set.range F) :
    a ∉ Set.range f₀ := by
  rintro ⟨s, rfl⟩
  exact h_avoid ⟨(0, s), F.apply_zero s⟩

/-- A point avoided by a free homotopy is avoided by its target loop. -/
theorem target_not_mem_range {f₀ f₁ : C(unitInterval, X)} (F : FreeHomotopy f₀ f₁)
    (a : X) (h_avoid : a ∉ Set.range F) :
    a ∉ Set.range f₁ := by
  rintro ⟨s, rfl⟩
  exact h_avoid ⟨(1, s), F.apply_one s⟩

end FreeHomotopy

end ContinuousMap
