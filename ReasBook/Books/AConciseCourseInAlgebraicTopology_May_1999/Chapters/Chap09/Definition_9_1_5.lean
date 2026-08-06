import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for based
-- homotopy groups, and repo search found no existing owner for pair-relative homotopy groups.
-- This item therefore introduces the source-faithful path-space model from Definition 9.1.4.

/-- Definition 9.1.5: for `n ≥ 1`, the relative homotopy group `π_n(X, A)` based at `x : A` is
the based homotopy group `π_ ((n : ℕ) - 1)` of the path space `PathToSet A x.1`, based at the
constant path `PathToSet.refl x`. -/
abbrev relativeHomotopyGroup (n : ℕ+) (A : Set X) (x : A) :=
  π_ ((n : ℕ) - 1) (PathToSet A x.1) (PathToSet.refl x)

/-- Rewriting the positive-degree index `n + 1` recovers the usual shifted formula
`π_(n + 1)(X, A) = π_ n P(X; *, A)`. -/
@[simp] theorem relativeHomotopyGroup_succ (n : ℕ) (A : Set X) (x : A) :
    relativeHomotopyGroup n.succPNat A x = π_ n (PathToSet A x.1) (PathToSet.refl x) := by
  simp [relativeHomotopyGroup]
