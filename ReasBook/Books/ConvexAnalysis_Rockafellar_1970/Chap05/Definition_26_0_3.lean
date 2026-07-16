import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.0.3 says a multivalued mapping is one-to-one exactly when both
  the mapping and its inverse are single-valued.
- `core/canonical`: on the chapter owner `SetRel`, one-to-one-ness is the canonical relation
  owner `Relator.BiUnique (· ~[ρ] ·)`.
- `bridge/view`: the chapter's multivalued-mapping owner is `SetRel α β`, and inversion is the
  canonical `SetRel.inv`; the source inverse wording is therefore a thin bridge from
  `(ρ⁻¹).RightUnique` to the intrinsic owner `ρ.LeftUnique`.

Domain-style sampling used here:
- `SetRel` and `SetRel.inv` from `Mathlib/Data/Rel.lean`;
- `Relator.RightUnique`;
- `Relator.LeftUnique`;
- `Relator.BiUnique`.

Primitive data vs derived API:
- primitive owner data: the relation `ρ : SetRel α β`;
- primitive canonical owner surface on `SetRel`: the one-to-one owner `ρ.BiUnique`,
  aligned with `Relator.BiUnique (· ~[ρ] ·)`;
- primitive theorem-level decomposition: right- and left-uniqueness of `ρ` through
  `ρ.RightUnique` and `ρ.LeftUnique`;
- derived source-facing bridge API: single-valuedness of `ρ⁻¹`,
  i.e. `(ρ⁻¹).RightUnique`.

Layer target: `bridge/view`.
-/

/- Definition 26.0.3: the canonical owner of “one-to-one” for a multivalued mapping is the
relation predicate `Relator.BiUnique`. -/
recall Relator.BiUnique

namespace SetRel

-- `SetRel.LeftUnique` and `SetRel.BiUnique` are part of the base Chapter 26 owner layer in
-- `Definition_26_0_1`; this file provides source-facing inverse/order bridge theorems.

/-- Inverse single-valuedness is exactly the left-uniqueness clause on the original relation. -/
@[simp] theorem rightUnique_inv_iff_leftUnique (ρ : SetRel α β) :
    (ρ⁻¹).RightUnique ↔ ρ.LeftUnique := by
  constructor
  · intro h a b c hac hbc
    exact h (by simpa [SetRel.mem_inv] using hac) (by simpa [SetRel.mem_inv] using hbc)
  · intro h c a b hca hcb
    exact h (by simpa [SetRel.mem_inv] using hca) (by simpa [SetRel.mem_inv] using hcb)

/-! The inverse bridge is symmetric: inverse left-uniqueness is right-uniqueness of the original
relation, and one-to-one-ness is invariant under inversion. -/

/-- Inverse left-uniqueness is exactly the right-uniqueness clause on the original relation. -/
@[simp] theorem leftUnique_inv_iff_rightUnique (ρ : SetRel α β) :
    (ρ⁻¹).LeftUnique ↔ ρ.RightUnique := by
  constructor
  · intro h c a b hca hcb
    exact h (by simpa [SetRel.mem_inv] using hca) (by simpa [SetRel.mem_inv] using hcb)
  · intro h a b c hac hbc
    exact h (by simpa [SetRel.mem_inv] using hac) (by simpa [SetRel.mem_inv] using hbc)

/-! Definition 26.0.3 has intrinsic canonical decomposition in terms of left- and right-uniqueness
on `ρ`, with source-order and source-inverse phrasings kept as bridge theorems. -/

/-- Canonical owner decomposition: one-to-one means left- and right-uniqueness on `ρ`
itself, in the intrinsic owner order of `Relator.BiUnique`. -/
@[simp] theorem biUnique_iff_leftUnique_and_rightUnique (ρ : SetRel α β) :
    ρ.BiUnique ↔
      ρ.LeftUnique ∧ ρ.RightUnique := by
  rw [SetRel.BiUnique, SetRel.LeftUnique, SetRel.RightUnique, Relator.BiUnique]

/-- Source-order bridge of Definition 26.0.3: one-to-one means right- and left-uniqueness on
`ρ` itself. -/
theorem biUnique_iff_rightUnique_and_leftUnique (ρ : SetRel α β) :
    ρ.BiUnique ↔
      ρ.RightUnique ∧ ρ.LeftUnique := by
  rw [biUnique_iff_leftUnique_and_rightUnique, and_comm]

/-- Definition 26.0.3 in the source inverse wording: `ρ` is one-to-one exactly when both
`ρ` and `ρ⁻¹` are single-valued. -/
theorem biUnique_iff_rightUnique_and_inv_rightUnique (ρ : SetRel α β) :
    ρ.BiUnique ↔
      ρ.RightUnique ∧ (ρ⁻¹).RightUnique := by
  rw [biUnique_iff_rightUnique_and_leftUnique, rightUnique_inv_iff_leftUnique]

/-- One-to-one-ness of a multivalued mapping relation is invariant under inversion. -/
@[simp] theorem biUnique_inv_iff (ρ : SetRel α β) :
    (ρ⁻¹).BiUnique ↔ ρ.BiUnique := by
  rw [biUnique_iff_leftUnique_and_rightUnique (ρ := ρ⁻¹)]
  rw [leftUnique_inv_iff_rightUnique (ρ := ρ), rightUnique_inv_iff_leftUnique (ρ := ρ)]
  rw [and_comm]
  rw [biUnique_iff_leftUnique_and_rightUnique (ρ := ρ)]

end SetRel

end
