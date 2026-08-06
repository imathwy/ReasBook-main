import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

/-- The closed unit disk in `ℂ`, written `D²` in Chapter 1. -/
abbrev closedUnitDisk : Set ℂ := Metric.closedBall (0 : ℂ) 1

scoped[ClosedUnitDisk] notation "D²" => closedUnitDisk

namespace ClosedUnitDisk

open scoped ClosedUnitDisk

/-- Membership in `D²` is exactly the norm bound `‖z‖ ≤ 1`. -/
@[simp] theorem mem_iff {z : ℂ} : z ∈ D² ↔ ‖z‖ ≤ 1 := by
  simp [closedUnitDisk, Metric.mem_closedBall, dist_eq_norm]

@[simp] theorem zero_mem : (0 : ℂ) ∈ D² := by
  simp

/-- Any point of `D²` has norm at most `1`. -/
theorem norm_coe_le_one (z : D²) : ‖(z : ℂ)‖ ≤ 1 :=
  mem_iff.mp z.2

instance instContractibleSpace : ContractibleSpace D² :=
  Metric.contractibleSpace_closedBall zero_le_one

end ClosedUnitDisk
