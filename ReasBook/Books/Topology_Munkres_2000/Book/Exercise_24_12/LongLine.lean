module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Order.Basic

public section

open Prod.Lex
open Set

namespace LongLine

/-- The point `(a, 0)` in the lexicographic product
`OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1`. -/
@[expose]
def axisPoint (a : OpenOmegaOne) : OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1 :=
  (a, ⟨0, le_rfl, zero_lt_one⟩)

/-- The least element of `OpenOmegaOne`. -/
@[expose]
def leastOrdinal : OpenOmegaOne :=
  CountableOrdinal.zero

/-- The least point of `OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1`. -/
@[expose]
def origin : OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1 := axisPoint leastOrdinal

end LongLine

/-- Munkres' long line: the lexicographic product
`OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1` with its least point deleted. -/
@[expose]
def LongLine := Set.Ioi LongLine.origin

namespace LongLine

/-- The order topology on the long line. -/
noncomputable instance instTopologicalSpace : TopologicalSpace LongLine :=
  Preorder.topology LongLine

/-- The first coordinate of an axis point is its ordinal coordinate. -/
@[simp] theorem axisPoint_fst (a : OpenOmegaOne) : (axisPoint a).1 = a := rfl

/-- The second coordinate of an axis point is zero. -/
@[simp] theorem axisPoint_snd (a : OpenOmegaOne) :
    (axisPoint a).2 = (⟨0, le_rfl, zero_lt_one⟩ : Set.Ico (0 : ℝ) 1) := rfl

/-- The first coordinate of the origin is the least countable ordinal. -/
@[simp] theorem origin_fst : origin.1 = leastOrdinal := rfl

/-- The second coordinate of the origin is zero. -/
@[simp] theorem origin_snd :
    origin.2 = (⟨0, le_rfl, zero_lt_one⟩ : Set.Ico (0 : ℝ) 1) := rfl

/-- Membership in the long line is strict inequality above the deleted origin. -/
theorem mem_iff {x : OpenOmegaOne ×ₗ Set.Ico (0 : ℝ) 1} : x ∈ LongLine ↔ origin < x := Iff.rfl

/-- The topology on `LongLine` is its order topology. -/
instance instOrderTopology : OrderTopology LongLine := ⟨rfl⟩

end LongLine
