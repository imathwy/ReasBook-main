import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for catenarity locality:
- chapter owner: `CatenarySpace X` from `Definition_5_11_4`
- same-domain chapter companion: `catenarySpace_iff`
- mathlib locality pattern for open subspaces: `IsLocallyClosed.locallyCompactSpace`
- mathlib owner-level open-cover locality patterns:
  `TopologicalSpace.IsOpenCover.jacobsonSpace_iff` and
  `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`

Layer triage:
- `source-facing`: the existential open-cover statement `Lemma 5.11.5`
- `core/canonical`: the owner class `CatenarySpace`
- `bridge/view`: restriction to an open subspace and locality on a fixed open cover

Primitive data belongs to `CatenarySpace`; the restriction and open-cover statements are derived
API for that owner. The locally closed restriction theorem is a reusable bridge/view companion for
the source-facing “moreover” clause, while the public surface keeps the owner-level fixed-cover
theorem and the source-facing existential restatement.
-/

-- Proof sketch: write a locally closed subset as an open subset of its closure. Closed irreducible
-- subsets of the subtype correspond to closed irreducible subsets of the ambient space meeting the
-- locally closed piece, and the interval of irreducible closed subsets is preserved under this
-- correspondence.
/-- A locally closed subspace of a catenary space is catenary. This is the reusable bridge/view
form of the “moreover” clause in Lemma 5.11.5. -/
protected theorem IsLocallyClosed.catenarySpace [CatenarySpace X] {Y : Set X}
    (hY : IsLocallyClosed Y) : CatenarySpace Y := sorry

namespace TopologicalSpace.IsOpenCover

-- Proof sketch: the forward implication restricts catenarity to each open member of the cover
-- using the locally closed restriction bridge above. For the converse, compare irreducible closed chains in
-- `X` with their restrictions to the cover members meeting the top element.
/-- Catenarity is local on the target for open covers. -/
theorem catenarySpace_iff {ι : Type v} {U : ι → Opens X} (hU : IsOpenCover U) :
    CatenarySpace X ↔ ∀ i, CatenarySpace (U i) := sorry

end TopologicalSpace.IsOpenCover

-- Proof sketch: the canonical owner-level locality statement is
-- `TopologicalSpace.IsOpenCover.catenarySpace_iff`. The forward implication chooses a trivial open
-- cover, while the converse applies that theorem to the given cover.
/-- Lemma 5.11.5: a topological space is catenary if and only if it admits an open cover by
catenary open subspaces.
This is the source-facing existential bridge for the canonical locality theorem
`TopologicalSpace.IsOpenCover.catenarySpace_iff`. -/
theorem catenarySpace_iff_hasOpenCoverByCatenarySpaces :
    CatenarySpace X ↔
      ∃ (ι : Type v) (U : ι → Opens X), IsOpenCover U ∧ ∀ i, CatenarySpace (U i) := by
  constructor
  · intro hX
    haveI : CatenarySpace X := hX
    refine ⟨ULift Unit, fun _ ↦ (⊤ : Opens X), ?_, ?_⟩
    · simp [TopologicalSpace.IsOpenCover]
    · intro i
      simpa using isOpen_univ.isLocallyClosed.catenarySpace
  · rintro ⟨ι, U, hU, hUcat⟩
    exact hU.catenarySpace_iff.2 hUcat
