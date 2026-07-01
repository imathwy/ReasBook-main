import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

scoped[Rockafellar] notation "B" => Metric.closedBall (0 : _) (1 : ℝ)

section

variable {E : Type*} [PseudoMetricSpace E] [Zero E]

open scoped Rockafellar

/-- Text 6.3 owner bridge: the chapter notation `B` is the canonical unit closed ball. -/
@[simp] theorem B_eq_closedBall : (B : Set E) = Metric.closedBall (0 : E) (1 : ℝ) := rfl

/-
Source/core/bridge triage:
- `source-facing`: Text 6.3 fixes the textbook unit ball and gives it the reusable chapter
  notation `B`, with membership surface `x ∈ B`.
- `core/canonical`: mathlib's owner object is the closed ball `closedBall (0 : E) 1`.
- `bridge/view`: the notation `B` is a thin source-facing surface for the canonical owner
  `closedBall (0 : E) 1`; metric and norm membership are bridge views.
- Primitive data vs derived API: no wrapper data is introduced; the source's membership
  descriptions stay derived API over the closed-ball owner.
- Domain-style sampling: `closedBall`, `mem_closedBall`, `mem_closedBall_zero_iff`,
  and the project bridge `closedBall_eq_add_smul_unitClosedBall` that uses this fixed unit ball
  downstream.
- Layer target: `source-facing` notation over the canonical closed-ball owner.
- Ambient-space refinement: the canonical owner and the metric membership view
  `mem_closedBall` live at the pseudometric + zero layer, so this file keeps those as the
  owner assumptions and isolates the norm-language view in a separate seminormed section.
-/

/-
Text 6.3 fixes the textbook unit ball as the notation `B`, i.e. the canonical closed ball
`closedBall (0 : E) 1`.
-/
theorem mem_B_iff_dist_zero_le_one {x : E} :
    x ∈ B ↔ dist x (0 : E) ≤ 1 := by
  exact (Metric.mem_closedBall : x ∈ (B : Set E) ↔ dist x (0 : E) ≤ 1)

end

section

variable {E : Type*} [SeminormedAddGroup E]

open scoped Rockafellar

/- Text 6.3's norm-language unit-ball membership surface is the canonical theorem
`mem_closedBall_zero_iff`, specialized to the chapter notation `B`. -/
theorem mem_B_iff_norm_le_one {x : E} :
    x ∈ B ↔ ‖x‖ ≤ 1 := by
  exact (mem_closedBall_zero_iff (a := x) (r := (1 : ℝ)))

end
