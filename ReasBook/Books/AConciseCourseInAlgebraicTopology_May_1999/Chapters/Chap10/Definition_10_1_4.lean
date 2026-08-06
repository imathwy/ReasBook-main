import Mathlib.Tactic.Recall
import Mathlib.Topology.CWComplex.Classical.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

-- Semantic recall via `lean_leansearch`: `Topology.RelCWComplex C D` is the canonical mathlib
-- owner for relative CW structures, and `Topology.RelCWComplex.skeleton` is the canonical
-- dimension-truncation API once `[T2Space X]` is available. The source's dimension clause is
-- therefore recorded by equality with the relative `n`-skeleton, with the base-plus-closed-cells
-- formula exposed as a companion theorem.

/- The notion of a relative CW complex `(X, A)` is formalized in mathlib by
`Topology.RelCWComplex C D`, encoding that the ambient subspace `C` is built relative to the
base subspace `D` by attaching cells, including possible relative `0`-cells. -/
recall Topology.RelCWComplex {X : Type u} [TopologicalSpace X] (C D : Set X) : Type (u + 1)

namespace Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
variable [RelCWComplex C D] (n : ℕ)

/-- Definition 10.1.4: for a relative CW complex `Topology.RelCWComplex C D`, the ambient
complex `C` has dimension at most `n` when the relative `n`-skeleton of `(C, D)` is all of `C`. -/
abbrev dimLE [T2Space X] : Prop :=
  (skeleton C n : Set X) = C

/-- `RelCWComplex.dimLE` is equivalent to the explicit description of `C` as the base `D`
together with the closed relative cells of dimensions at most `n`. -/
theorem dimLE_iff_base_union_iUnion_closedCell [T2Space X] :
    dimLE C n ↔ (D ∪ ⋃ (m : ℕ) (_ : m ≤ n) (j : cell C m), closedCell m j) = C := by
  have hmn : ∀ m : ℕ, ((m : ℕ∞) < (n : ℕ∞) + 1) ↔ m ≤ n := by
    intro m
    rw [ENat.lt_coe_add_one_iff, ENat.coe_le_coe]
  simp [dimLE, skeleton, coe_skeletonLT, hmn]

end Topology.RelCWComplex
