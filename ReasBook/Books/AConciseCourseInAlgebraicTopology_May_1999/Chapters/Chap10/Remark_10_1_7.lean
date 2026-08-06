import Mathlib.Tactic.Recall
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.CWComplex.Classical.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Set.Notation

-- Semantic recall via `lean_leansearch`: `TopologicalSpace.compactlyGenerated` is the canonical
-- k-topology replacement used elsewhere in the project for compactly generated constructions, and
-- `Topology.CWComplex.closed` is the canonical weak-topology theorem for classical CW complexes.

/- The pushouts and unions in the definition of a CW complex use compactly generated topologies;
in this project that convention is represented by the canonical k-ification
`TopologicalSpace.compactlyGenerated X`. -/
recall TopologicalSpace.compactlyGenerated (X : Type u) [TopologicalSpace X] : TopologicalSpace X

namespace Topology.CWComplex

/-- Remark 10.1.7. If `A` is a subset of a CW complex `C`, then `A` is closed exactly when
its intersections with all finite skeleta of `C` are closed in the corresponding skeleton
subspaces. -/
theorem isClosed_iff_isClosed_preimage_skeleton
    {X : Type u} [TopologicalSpace X] [T2Space X] {C A : Set X} [CWComplex C] (hAC : A ⊆ C) :
    IsClosed A ↔ ∀ n : ℕ, IsClosed ((Subtype.val : skeleton C n → X) ⁻¹' A) := by
  constructor
  · intro hA n
    exact hA.preimage continuous_subtype_val
  · intro hA
    rw [CWComplex.closed C A hAC]
    intro n j
    have hskeleton : IsClosed ((skeleton C n : Set X) ∩ A) := by
      exact
        (IsClosed.inter_preimage_val_iff
          (CWComplex.Subcomplex.closed (skeleton C n))).1 (hA n)
    have hinter :
        A ∩ closedCell n j = ((skeleton C n : Set X) ∩ A) ∩ closedCell n j := by
      ext x
      constructor
      · rintro ⟨hxA, hxCell⟩
        exact ⟨⟨closedCell_subset_skeleton n j hxCell, hxA⟩, hxCell⟩
      · rintro ⟨⟨_, hxA⟩, hxCell⟩
        exact ⟨hxA, hxCell⟩
    rw [hinter]
    exact hskeleton.inter (CWComplex.isClosed_closedCell : IsClosed (closedCell n j))

/-- A reusable ambient-space reformulation of Remark 10.1.7. Since each finite skeleton is a
closed subspace, closedness in the skeleton subspace topology is equivalent to ambient closedness
of the corresponding intersection. -/
theorem isClosed_iff_isClosed_inter_skeleton
    {X : Type u} [TopologicalSpace X] [T2Space X] {C A : Set X} [CWComplex C] (hAC : A ⊆ C) :
    IsClosed A ↔ ∀ n : ℕ, IsClosed ((skeleton C n : Set X) ∩ A) := by
  rw [isClosed_iff_isClosed_preimage_skeleton hAC]
  constructor
  · intro h n
    exact
      (IsClosed.inter_preimage_val_iff
        (CWComplex.Subcomplex.closed (skeleton C n))).1 (h n)
  · intro h n
    exact
      (IsClosed.inter_preimage_val_iff
        (CWComplex.Subcomplex.closed (skeleton C n))).2 (h n)

end Topology.CWComplex
