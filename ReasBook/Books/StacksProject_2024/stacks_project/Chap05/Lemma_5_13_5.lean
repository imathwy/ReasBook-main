import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u v w z

section

variable {X : Type u} [TopologicalSpace X]

variable [CompactSpace X] [T2Space X]
variable {ι : Type v}

/- Domain-style sampling for tuplewise shrinking of open covers:
- primary domain: shrinking lemmas for open covers in compact normal spaces
- source-facing owner for the ambient cover data: `TopologicalSpace.IsOpenCover`
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_shrinking`,
  `exists_iUnion_eq_closure_subset`,
  `TopologicalSpace.IsOpenCover.comap`,
  `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`

Layer triage:
- `source-facing`: the Stacks tuplewise shrinking statement below
- `core/canonical`: the fixed-cover owner `TopologicalSpace.IsOpenCover`
- `bridge/view`: the prescribed tuplewise ambient open families, viewed only as covers of the
  corresponding finite intersections

Primitive data are only the open cover `U` and the prescribed tuplewise cover family `W`. The
covering property of each tuplewise family is the equality
`⋂ a, U (s a) = ⋃ k, W s k`; the shrinking family, its closure control, and the tuplewise
subordination are derived theorem output, so they should not be packaged into a separate public
structure or a second exact-interface wrapper theorem. The public statement keeps the source-facing
compact Hausdorff hypotheses, while normality is left implicit for the later proof through the
standard compact-Hausdorff-to-normal instance.
-/

namespace TopologicalSpace.IsOpenCover

/-- A tuplewise shrinking refinement of an open cover consists of a shrinking whose realized
`(p + 1)`-fold intersections are either empty or contained in one member of the prescribed
tuplewise cover of the corresponding intersection of the original cover. -/
class IsTuplewiseShrinkingRefinement
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    {J : Type z} (V : J → Opens X) (α : J → ι) : Prop where
  isOpenCover : IsOpenCover V
  closure_subset (j : J) : closure (V j : Set X) ⊆ U (α j)
  tuplewise_subordinate (jTuple : Fin (p + 1) → J) :
    (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) = ∅ ∨
      ∃ k : κ (fun a ↦ α (jTuple a)),
        (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) ⊆ W (fun a ↦ α (jTuple a)) k

-- Proof sketch: first apply the compact-Hausdorff shrinking lemma to the original cover. Then
-- argue by induction on `p`: repeated source indices are handled by a common refinement of the
-- lower-fold intersection covers, while pairwise distinct source indices are treated by iteratively
-- cutting offending opens into finitely many pieces subordinate to the prescribed cover of the
-- corresponding `(p + 1)`-fold intersection, decreasing the bad-tuple count until it vanishes.
/-- Lemma 5.13.5: a quasi-compact Hausdorff open cover admits a shrinking refinement whose
closures stay inside the original cover and whose realized `(p + 1)`-fold intersections are either
empty or lie in one member of the prescribed open cover of the corresponding `(p + 1)`-fold
intersection of the original cover. -/
theorem exists_tuplewise_shrinking_refinement
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (J : Type (max u v w)) (V : J → Opens X) (α : J → ι),
      IsTuplewiseShrinkingRefinement hU p W V α := sorry

end TopologicalSpace.IsOpenCover

end
