module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

namespace IntervalFold

/-- The union of the closed intervals `[0, 1]` and `[2, 3]`, as a subspace of `ℝ`. -/
abbrev Domain := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1 ∪ Set.Icc 2 3}

/-- The closed interval `[0, 2]`, as a subspace of `ℝ`. -/
abbrev Codomain := Set.Icc (0 : ℝ) 2

/-- The real-valued interval-folding formula on `Domain`. -/
@[expose]
noncomputable def value (x : Domain) : ℝ :=
  if (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 then x else x - 1

/-- On the left component `[0, 1]`, the interval-folding formula fixes each point. -/
@[simp]
theorem value_of_mem_left {x : Domain} (hx : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    value x = x := by simp [value, hx]

/-- On the right component `[2, 3]`, the interval-folding formula translates by `-1`. -/
@[simp]
theorem value_of_mem_right {x : Domain} (hx : (x : ℝ) ∈ Set.Icc (2 : ℝ) 3) :
    value x = x - 1 := by
  rw [value]
  split_ifs with h
  · have : False := by linarith [h.2, hx.1]
    contradiction
  · rfl

/-- The interval-folding formula takes values in `Codomain`. -/
theorem value_mem (x : Domain) : value x ∈ Set.Icc (0 : ℝ) 2 := by
  -- On each source component, use the corresponding affine formula and interval bounds.
  rcases x.property with hx_left | hx_right
  · rw [value_of_mem_left hx_left]
    constructor
    · exact hx_left.1
    · linarith [hx_left.2]
  · rw [value_of_mem_right hx_right]
    constructor
    · linarith [hx_right.1]
    · linarith [hx_right.2]

/-- The map folding `[2, 3]` onto `[1, 2]` while fixing `[0, 1]`. -/
@[expose]
noncomputable def map (x : Domain) : Codomain := ⟨value x, value_mem x⟩

/-- The underlying real value of `map x` is `value x`. -/
@[simp]
theorem coe_map (x : Domain) : (map x : ℝ) = value x := rfl

/-- The left interval `[0, 1]`, regarded as a subset of `Domain`. -/
def leftComponent : Set Domain := Subtype.val ⁻¹' Set.Icc (0 : ℝ) 1

/-- Helper for Example 22.1: `leftComponent` is the preimage of `[0, 1]` under the subtype map. -/
lemma leftComponent_eq_preimage_Icc :
    leftComponent = Subtype.val ⁻¹' Set.Icc (0 : ℝ) 1 := by
  -- Expose the defining subset once in the module that owns the opaque definition.
  rfl


end IntervalFold

end
