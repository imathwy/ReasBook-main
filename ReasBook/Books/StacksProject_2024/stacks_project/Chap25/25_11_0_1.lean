import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {I0 : Type v} (U0 : I0 → Opens X)

/-
Source/core/bridge triage:
- `source-facing`: the level-`0` opens `U0` cover `X`;
- `core/canonical`: `TopologicalSpace.IsOpenCover U0`;
- `bridge/view`: the source's union equality is the canonical theorem
  `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`.

This item only recalls the standard open-cover owner and its source-facing companion theorem, so a
direct `recall` surface is the canonical refine outcome. -/

/- 25.11.0.1: the equality `X = ⋃_{i ∈ I_0} U_i` is the canonical open-cover condition for the
level-`0` family `U0`. In mathlib this is the owner `TopologicalSpace.IsOpenCover U0`, and the
source-facing union equality is recovered by `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`. -/
recall TopologicalSpace.IsOpenCover

/- The source-facing union equation for an open cover is the canonical theorem
`TopologicalSpace.IsOpenCover.iSup_set_eq_univ`. -/
recall TopologicalSpace.IsOpenCover.iSup_set_eq_univ

end
