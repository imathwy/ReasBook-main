import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

-- Semantic Lean search tool unavailable in this environment; verified directly against local
-- mathlib usage of `volume A = 0` for null subsets of Euclidean space.

variable {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}

/- Definition 6.38-extra-1 is recall-only. The source-facing statement "A has measure zero" is
formalized by the primitive null-set condition `μ A = 0`; in the Euclidean Lebesgue specialization,
this is `volume A = 0`. Derived APIs such as `NullMeasurableSet.of_null` sit above that owner
abstraction. -/
recall NullMeasurableSet.of_null

/- Definition 6.38-extra-1: for `A ⊆ ℝ^n`, having measure zero is expressed as `volume A = 0`. The
textbook covering-by-countably-many open rectangles with arbitrarily small total volume is a
characterization of this null-set condition. -/
#check (volume A = 0)
