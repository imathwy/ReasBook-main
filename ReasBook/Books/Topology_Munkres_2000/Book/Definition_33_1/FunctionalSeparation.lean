module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Set

universe u

/-- Two subsets are functionally separated when a continuous map to the closed unit
interval is zero on the first set and one on the second. -/
def FunctionallySeparated {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  ∃ f : C(X, Icc (0 : ℝ) 1),
    EqOn f (fun _ ↦ (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1)) A ∧
      EqOn f (fun _ ↦ (⟨1, zero_le_one, le_rfl⟩ : Icc (0 : ℝ) 1)) B

namespace FunctionallySeparated

variable {X : Type u} [TopologicalSpace X] {A B : Set X}

/-- Functional separation can equivalently be witnessed by a real-valued continuous map
whose range lies in the closed unit interval. -/
theorem iff_exists_continuousMap_real :
    FunctionallySeparated A B ↔
      ∃ f : C(X, ℝ), EqOn f 0 A ∧ EqOn f 1 B ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · intro h
    obtain ⟨f, hA, hB⟩ := h
    -- Forget the interval subtype while retaining its pointwise bounds.
    have hcontinuous : Continuous (fun x ↦ (f x : ℝ)) :=
      continuous_subtype_val.comp f.continuous
    let g : C(X, ℝ) := ⟨fun x ↦ (f x : ℝ), hcontinuous⟩
    refine ⟨g, ?_, ?_, ?_⟩
    · intro x hx
      exact congrArg Subtype.val (hA hx)
    · intro x hx
      exact congrArg Subtype.val (hB hx)
    · intro x
      exact (f x).property
  · rintro ⟨f, hA, hB, hf⟩
    -- Restrict the bounded real-valued witness to the closed unit interval.
    have hcontinuous : Continuous (fun x ↦ (⟨f x, hf x⟩ : Icc (0 : ℝ) 1)) :=
      f.continuous.subtype_mk hf
    let g : C(X, Icc (0 : ℝ) 1) :=
      ⟨fun x ↦ ⟨f x, hf x⟩, hcontinuous⟩
    refine ⟨g, ?_, ?_⟩
    · intro x hx
      apply Subtype.ext
      exact hA hx
    · intro x hx
      apply Subtype.ext
      exact hB hx

/-- A real-valued continuous map into the closed unit interval separates the sets on which it is
constantly zero and one. -/
theorem of_continuousMap_real (f : C(X, ℝ)) (hA : EqOn f 0 A) (hB : EqOn f 1 B)
    (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) : FunctionallySeparated A B :=
  iff_exists_continuousMap_real.2 ⟨f, hA, hB, hf⟩

/-- Functional separation is symmetric in the two subsets. -/
theorem symm (h : FunctionallySeparated A B) : FunctionallySeparated B A := by
  obtain ⟨f, hA, hB, hf⟩ := iff_exists_continuousMap_real.1 h
  -- Complementing the witness exchanges its endpoint values.
  have hcontinuous : Continuous (fun x ↦ 1 - f x) := continuous_const.sub f.continuous
  let g : C(X, ℝ) := ⟨fun x ↦ 1 - f x, hcontinuous⟩
  apply iff_exists_continuousMap_real.2
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx
    have hfx : f x = 1 := by
      simpa using hB hx
    calc
      g x = 1 - f x := rfl
      _ = 0 := by rw [hfx, sub_self]
  · intro x hx
    have hfx : f x = 0 := by
      simpa using hA hx
    calc
      g x = 1 - f x := rfl
      _ = 1 := by rw [hfx, sub_zero]
  · intro x
    obtain ⟨hzero, hone⟩ := hf x
    change 1 - f x ∈ Icc (0 : ℝ) 1
    constructor
    · linarith
    · linarith

/-- Functionally separated subsets are disjoint. -/
theorem disjoint (h : FunctionallySeparated A B) : Disjoint A B := by
  obtain ⟨f, hA, hB, _⟩ := iff_exists_continuousMap_real.1 h
  -- A common point would force the witness to equal both distinct endpoints.
  rw [Set.disjoint_left]
  intro x hxA hxB
  have hzero_one : (0 : ℝ) = 1 := (hA hxA).symm.trans (hB hxB)
  exact zero_ne_one hzero_one

end FunctionallySeparated


end
