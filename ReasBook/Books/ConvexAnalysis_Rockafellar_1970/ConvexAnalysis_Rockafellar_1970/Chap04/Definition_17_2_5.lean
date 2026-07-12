import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_6_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

universe u v

variable {E : Type u} {R : Type v} [Zero E] [One R]

local notation "EStar" => E × R

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.5 adjoins the vertical unit vector `((0 : E), 1)` to
  `SStar ⊆ E × R`; this primitive generating-set step itself only needs `0` in `E` and `1` in
  the vertical codomain `R`.
- `core/canonical`: the chapter owner abstraction for generated cones is `cone[R]`,
  i.e. `PointedCone.hull`.
- `bridge/view`: `adjoin_vertical_unit SStar` records the textbook generating set, while the
  generated cone is exposed through textbook notation `K⋆[R] SStar` on the canonical owner.

Domain-style sampling used here:
- the owner notation `cone[R]` from `Chap01.Definition_2_6_10`;
- `PointedCone.hull`;
- `PointedCone.subset_hull`;
- `(cone[R] (adjoin_vertical_unit SStar)).zero_mem`.

Primitive data vs derived API:
- primitive source data: the set `SStar : Set (E × R)`;
- source-facing owner data: `adjoin_vertical_unit SStar`;
- derived owner-side cone: `K⋆[R] SStar = cone[R] (adjoin_vertical_unit SStar)`.

Layer target: `source-facing`.
-/

/-- The distinguished vertical unit point used in Definition 17.2.5. -/
def vertical_unit : EStar := ((0 : E), (1 : R))

/-- Definition 17.2.5: adjoin the vertical unit point to `SStar`. -/
def adjoin_vertical_unit (SStar : Set EStar) : Set EStar :=
  insert vertical_unit SStar

@[simp] theorem mem_adjoin_vertical_unit {SStar : Set EStar} {pStar : EStar} :
    pStar ∈ adjoin_vertical_unit SStar ↔ pStar = vertical_unit ∨ pStar ∈ SStar := by
  simp [adjoin_vertical_unit]

theorem subset_adjoin_vertical_unit (SStar : Set EStar) :
    SStar ⊆ adjoin_vertical_unit SStar :=
  Set.subset_insert _ _

@[simp] theorem vertical_unit_mem_adjoin_vertical_unit (SStar : Set EStar) :
    vertical_unit ∈ adjoin_vertical_unit SStar := by
  simp [adjoin_vertical_unit]

end

section

open scoped Rockafellar

/-! Textbook owner notation for Definition 17.2.5. -/
scoped[Rockafellar] notation:max "K⋆[" R "] " SStar =>
  cone[R] (adjoin_vertical_unit SStar)

end
