import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped NNReal ENNReal Topology

universe u

variable {E : Type u} [TopologicalSpace E]

/- Definition 23.6 (1): A rate function on `E` is exactly a lower semicontinuous map
`E → [0, ∞]`, modeled in Lean as `LowerSemicontinuous I` for `I : E → ℝ≥0∞`. -/
recall LowerSemicontinuous

/-- Definition 23.6 (2): A good rate function is a rate function whose finite sublevel sets
`I ⁻¹' ([0, a])` are compact for every `a ∈ [0, ∞)`, written in Lean as
`I ⁻¹' Iic (a : ℝ≥0∞)` for `a : ℝ≥0`. -/
@[mk_iff isGoodRateFunction_iff]
class IsGoodRateFunction (I : E → ℝ≥0∞) : Prop where
  /-- A good rate function is lower semicontinuous. -/
  lowerSemicontinuous : LowerSemicontinuous I
  /-- Every finite sublevel set of a good rate function is compact. -/
  isCompact_sublevel : ∀ a : ℝ≥0, IsCompact (I ⁻¹' Iic (a : ℝ≥0∞))

/-- A good rate function is canonically lower semicontinuous. -/
instance instLowerSemicontinuousOfIsGoodRateFunction
    (I : E → ℝ≥0∞) [hI : IsGoodRateFunction I] : LowerSemicontinuous I :=
  hI.lowerSemicontinuous

/-- On a compact space, the constant zero map is a good rate function. -/
instance instIsGoodRateFunctionZero [CompactSpace E] :
    IsGoodRateFunction (fun _ : E ↦ (0 : ℝ≥0∞)) := sorry
