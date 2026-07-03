import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace
/- The textbook notion of a locally finite family of subsets is mathlib's `LocallyFinite`. -/
recall LocallyFinite {ι : Type v} {X : Type u} [TopologicalSpace X] (f : ι → Set X) : Prop

/- Definition 1-extra-4: Lee's notion of a paracompact topological space is mathlib's
`ParacompactSpace`; its canonical API says that every open cover admits an open locally finite
refinement. -/
recall ParacompactSpace (X : Type u) [TopologicalSpace X] : Prop

/- The canonical owner for an indexed open cover is `TopologicalSpace.IsOpenCover`. -/
recall TopologicalSpace.IsOpenCover {ι : Type v} {X : Type u} [TopologicalSpace X]
  (U : ι → Opens X) : Prop

namespace TopologicalSpace.IsOpenCover

variable {M : Type u} [TopologicalSpace M] {ι : Type v}

-- Proof sketch: apply `precise_refinement` to the underlying family of sets of the open cover
-- `U`, then promote the resulting sets back to opens. The precise pointwise inclusions yield the
-- weaker textbook refinement relation.
/-- An indexed open cover of a paracompact space admits an open locally finite refinement. -/
theorem exists_locallyFinite_refinement [ParacompactSpace M] {U : ι → Opens M}
    (hU : IsOpenCover U) :
    ∃ (κ : Type v) (V : κ → Opens M),
      IsOpenCover V ∧ LocallyFinite (fun j ↦ (V j : Set M)) ∧
        ∀ j, ∃ i, (V j : Set M) ⊆ U i := by
  rcases precise_refinement (fun i ↦ (U i : Set M)) (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ with
    ⟨V, hV_open, hV_cover, hV_locallyFinite, hVU⟩
  exact ⟨ι, fun i ↦ ⟨V i, hV_open i⟩, IsOpenCover.of_sets hV_open hV_cover, hV_locallyFinite,
    fun i ↦ ⟨i, hVU i⟩⟩

end TopologicalSpace.IsOpenCover
