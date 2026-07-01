import Mathlib
import stacks_project.Chap05.Remark_5_28_5
import stacks_project.Chap05.Lemma_5_28_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for finite good refinements of locally closed partitions in Noetherian
spaces:
- primary domain: Noetherian topological spaces, indexed stratifications, and good locally closed
  partitions
- inspected same-domain declarations:
  `LocallyClosedPartition.exists_finite_stratification_refining`,
  `IsStratification.toLocallyClosedPartition`,
  `IsStratification.toLocallyClosedPartition_isGood`, and
  `locallyFinite_of_finite`
- best owner abstraction: `LocallyClosedPartition.IsGood`

Layer triage:
- `source-facing`: the existence of a finite good refinement of a finite locally closed partition
  in a Noetherian space
- `core/canonical`: `LocallyClosedPartition.IsGood`
- `bridge/view`: the passage from a finite indexed stratification to its partition view via
  `IsStratification.toLocallyClosedPartition`

Primitive data are only the finite partition `P`. The indexed stratification and local finiteness
witnesses are derived bridge data, so this file should reuse the chapter owners instead of
introducing a parallel good-refinement package. In particular, the source's Noetherian hypothesis
is redundant for this owner-level statement.
-/

/-- A finite good refinement of `P` is a refining locally closed partition that is both finite and
good. -/
class LocallyClosedPartition.IsFiniteGoodRefinement
    (Q P : LocallyClosedPartition X) : Prop where
  finite : Q.toSet.Finite
  refinement : Q ≤ P
  good : LocallyClosedPartition.IsGood Q

-- Proof sketch: start from Lemma 5.28.6 to obtain a finite stratification refining `P`, then pass
-- to its canonical partition view and apply the chapter theorem that locally finite
-- stratifications are good. Finite index type makes local finiteness automatic.
/-- Lemma 5.28.8: every finite locally closed partition is refined by a finite good locally closed
partition. The source's Noetherian hypothesis is redundant after refining through finite
stratifications. -/
theorem LocallyClosedPartition.exists_finite_good_refinement
    (P : LocallyClosedPartition X) (hPfinite : P.toSet.Finite) :
    ∃ Q : LocallyClosedPartition X, Q.IsFiniteGoodRefinement P := sorry

end
