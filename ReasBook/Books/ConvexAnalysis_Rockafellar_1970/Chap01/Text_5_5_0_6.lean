import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped ENNReal NNReal Rockafellar

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Canonical owner-side formula: Rockafellar's gauge of the closed unit ball is the extended
norm. -/
theorem egauge_closedBall_zero_one_eq_enorm (x : X) :
    γ(x | closedBall (0 : X) 1) = ‖x‖ₑ := by
  refine le_antisymm ?_ ?_
  · simpa [enorm_eq_nnnorm] using
      (egauge_le_of_mem_smul (x := x) (s := closedBall (0 : X) 1) <| by
        refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
        · simpa using inv_norm_smul_mem_unitClosedBall x
        · by_cases hx : x = 0
          · simp [hx]
          · change ((‖x‖₊ : ℝ) • (‖x‖⁻¹ • x)) = x
            rw [smul_smul]
            change (‖x‖ * ‖x‖⁻¹) • x = x
            simp [norm_ne_zero_iff.mpr hx])
  · rw [le_egauge_iff]
    intro c hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [mem_closedBall_zero_iff] at hy
    have h : ‖((c : ℝ) • y)‖₊ ≤ c := by
      calc
        ‖((c : ℝ) • y)‖₊ = ‖(c : ℝ)‖₊ * ‖y‖₊ := by
          simpa using nnnorm_smul (c : ℝ) y
        _ = c * ‖y‖₊ := by simp
        _ ≤ c * 1 := by gcongr; simpa using hy
        _ = c := by simp
    simpa [enorm_eq_nnnorm] using h

end

section

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [SeminormedAddCommGroup X]

local notation "E" => ι → X

/-
Source/core/bridge triage:
- `source-facing`: the intrinsic owner-side proposition fixes the centered unit cube as the closed
  sup-norm unit ball on a finite coordinate family and identifies Rockafellar's gauge of this set
  with the canonical sup norm.
- `core/canonical`: the chapter owner for Rockafellar's gauge is `γ(x | C) = egauge ℝ≥0 C x` from
  `Defintion_4_8_2`.
- `bridge/view`: the source-facing centered-cube language is bridged directly through the intrinsic
  owner `closedBall (0 : E) 1`; coordinate inequalities are recovered by a downstream bridge
  theorem.
- Domain-style sampling used here: the chapter owner `γ(x | C) = egauge ℝ≥0 C x`,
  mathlib's `egauge`, `egauge_le_of_mem_smul`, `le_egauge_iff`,
  `inv_norm_smul_mem_unitClosedBall`, and `pi_norm_le_iff_of_nonneg`.
- Primitive data vs derived API: the intrinsic closed-ball owner is the primitive set datum; the
  coordinate formulas are bridge theorems.
- Layer target: `core/canonical`; keep theorem surfaces on the intrinsic owner and expose the
  coordinate inequality surface through bridge API.
-/

/-- Intrinsic bridge for `centeredUnitCube`: closed-ball membership is equivalent to pointwise norm
bounds. -/
theorem mem_centeredUnitCube_iff_norm (y : E) :
    y ∈ (closedBall (0 : E) 1 : Set E) ↔ ∀ i : ι, ‖y i‖ ≤ 1 := by
  rw [mem_closedBall_zero_iff]
  exact pi_norm_le_iff_of_nonneg zero_le_one

end

section

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "E" => ι → X

-- Proof sketch: specialize the canonical owner theorem
-- `egauge_closedBall_zero_one_eq_enorm`.
/-- Text 5.5.0.6 (canonical owner-side form): for any finite coordinate family in a real normed
space, Rockafellar's gauge `γ(· | C)` of the centered unit cube is the canonical sup norm. -/
theorem egauge_centeredUnitCube_eq_enorm (x : E) :
    γ(x | (closedBall (0 : E) 1 : Set E)) = ‖x‖ₑ := by
  simpa using (egauge_closedBall_zero_one_eq_enorm (x := x))

end

section

variable {ι : Type*} [Fintype ι]

local notation "E" => ι → ℝ

/-- Source-facing real-coordinate bridge for `centeredUnitCube`: coordinate inequalities are
equivalent to closed-ball membership. -/
theorem mem_centeredUnitCube (y : E) :
    y ∈ (closedBall (0 : E) 1 : Set E) ↔ ∀ i : ι, -(1 : ℝ) ≤ y i ∧ y i ≤ 1 := by
  rw [mem_centeredUnitCube_iff_norm]
  constructor
  · intro hy i
    simpa [Real.norm_eq_abs, abs_le] using hy i
  · intro hy i
    simpa [Real.norm_eq_abs, abs_le] using hy i

end
end
