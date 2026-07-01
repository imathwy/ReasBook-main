import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap05.Lemma_5_13_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace
open scoped Topology

universe u v

section

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable {I : Type v}

/- Domain-style sampling for shrinking open covers along a compact subset:
- primary domain: shrinking lemmas in locally compact Hausdorff spaces
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_shrinking`,
  `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`,
  `IsCompact.exists_open_between_and_isCompact_closure`,
  `exists_iUnion_eq_closure_subset`
- best owner abstraction: `IsCompact`

Layer triage:
- `source-facing`: the Stacks lemma below, which attaches prescribed tuplewise intersections to a
  fixed compact subset `Z`
- `core/canonical`: the compact-normal tuplewise shrinking owner
  `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`, together with the compact
  lifting API `IsCompact.exists_open_between_and_isCompact_closure`
- `bridge/view`: the ambient shrinking family `V`, whose cover property, closure control, and
  tuplewise containment are all derived from the compact owner data on the subtype of `Z`

Primitive data are exactly the compact subset `Z`, the ambient open family `U`, the prescribed
tuplewise opens `W`, and the two compatibility hypotheses on `Z`. The shrinking family `V` and its
closure/intersection properties are derived output, so the public API should live on the compact
owner `IsCompact` rather than as a parallel global wrapper.
-/

namespace IsCompact

/- Companion recall: the compact-normal tuplewise shrinking owner for open covers is the
chapter theorem `TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement`; the compact
subset theorem below is the corresponding source-facing bridge, used through the owner call shape
`hZ.exists_open_shrinking_with_prescribed_intersections`. -/
recall TopologicalSpace.IsOpenCover.exists_tuplewise_shrinking_refinement

/-- A shrinking of an open family whose closures stay in the ambient opens and whose
`(p + 1)`-fold intersections land in the prescribed opens along a compact subset. -/
class IsOpenShrinkingWithPrescribedIntersections
    (Z : Set X) (p : ℕ) (U : I → Opens X) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) : Prop where
  /-- The shrunken opens still cover the compact subset. -/
  cover : Z ⊆ ⋃ i, V i
  /-- The closure of each shrunken open stays inside the corresponding ambient open. -/
  closure_subset (i : I) : closure (V i : Set X) ⊆ U i
  /-- Every `(p + 1)`-fold intersection of the shrunken family lands in the prescribed open. -/
  tuplewise_subset (σ : Fin (p + 1) → I) : (⋂ j, (V (σ j) : Set X)) ⊆ W σ

/-- Lemma 5.13.6: a compact subset `Z` of a locally compact Hausdorff space, covered by opens
`U i` with prescribed `(p + 1)`-fold neighborhoods along `Z`, admits an open shrinking whose
closures stay in `U i` and whose `(p + 1)`-fold intersections land in the prescribed opens. -/
-- Proof sketch: reduce to the finite, quasi-compact case, then argue by induction on `p`; use
-- Lemma 5.13.4 to obtain the base-case shrinking, and in the induction step remove finitely many
-- closed error sets from the chosen opens to force the required intersection containments.
theorem exists_open_shrinking_with_prescribed_intersections
    {Z : Set X} (hZ : IsCompact Z) (p : ℕ) (U : I → Opens X)
    (W : (Fin (p + 1) → I) → Opens X)
    (hcover : Z ⊆ ⋃ i, U i)
    (hW_subset : ∀ σ, (W σ : Set X) ⊆ ⋂ j, U (σ j))
    (hW_on_Z : ∀ σ, (W σ : Set X) ∩ Z = (⋂ j, U (σ j)) ∩ Z) :
    ∃ V : I → Opens X, IsOpenShrinkingWithPrescribedIntersections Z p U W V := sorry

end IsCompact

end
