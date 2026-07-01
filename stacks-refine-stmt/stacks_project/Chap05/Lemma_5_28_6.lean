import Mathlib
import stacks_project.Chap05.Remark_5_28_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for finite stratification refinements of locally closed partitions:
- inspected project declarations:
  `LocallyClosedPartition`,
  `LocallyClosedPartition.le_iff_forall_exists_mem_subset`,
  `IsStratification.toLocallyClosedPartition`, and
  `IsClosedInitialFamily.frontier_isStratification`
- best owner abstraction: `IsClosedInitialFamily`

Layer triage:
- `source-facing`: the indexed-stratification statement of Lemma 5.28.6
- `core/canonical`: `IsClosedInitialFamily`
- `bridge/view`: `IsClosedInitialFamily.frontier_isStratification` together with
  `IsStratification.toLocallyClosedPartition`

Primitive data are only the finite locally closed partition `P` and the refinement relation to the
eventual stratification. Any auxiliary closed initial family used to construct the ordered strata,
as well as the resulting index type and closure-order bookkeeping, belongs to derived bridge data
rather than the public owner of this source item.
-/

namespace LocallyClosedPartition

-- Proof sketch: replace the finite partition by a finite closed initial family built from the
-- closures of unions of parts, apply `IsClosedInitialFamily.frontier_isStratification`, and then
-- recover refinement of `P` through `IsStratification.toLocallyClosedPartition`.
/-- Lemma 5.28.6: every finite locally closed partition of a topological space is refined by a
finite stratification. -/
theorem exists_finite_stratification_refining (P : LocallyClosedPartition X)
    (hPfinite : P.toSet.Finite) :
    ∃ (I : Type u) (_ : Finite I) (_ : PartialOrder I) (strata : I → Set X)
      (hstrata : IsStratification strata), hstrata.toLocallyClosedPartition ≤ P := by
  sorry

end LocallyClosedPartition

end
