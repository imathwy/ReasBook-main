import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Submodule
open Module

universe u v

section

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/- Corollary 1.4.22 (1): every finite-dimensional `K`-vector space admits the canonical finite
basis `Module.finBasis K V`, indexed by `Fin (Module.finrank K V)`. -/
#check (Module.finBasis K V : Basis (Fin (finrank K V)) K V)

/- Corollary 1.4.22 (2): if `G` spans `V`, the canonical basis `Basis.ofSpan hG` is contained in
`G`. Its index type is finite because `V` is finite-dimensional. -/
#check
  (Basis.ofSpan :
    {G : Set V} → ⊤ ≤ span K G → Basis ((linearIndepOn_empty K id).extend (empty_subset G)) K V)

#check
  (Basis.ofSpan_subset :
    {G : Set V} → (hG : ⊤ ≤ span K G) → range (Basis.ofSpan hG) ⊆ G)

theorem finite_ofSpan_index {G : Set V} (hG : ⊤ ≤ span K G) :
    ((linearIndepOn_empty K id).extend (empty_subset G)).Finite := by
  exact IsNoetherian.finite_basis_index (Basis.ofSpan hG)

/- Corollary 1.4.22 (3): any linearly independent subset extends to the canonical basis
`Basis.extend hL`, and that basis has finite index type in finite dimension. -/
#check
  (Basis.extend :
    {L : Set V} → (hL : LinearIndepOn K id L) → Basis (hL.extend (subset_univ L)) K V)

#check
  (Basis.range_extend :
    {L : Set V} → (hL : LinearIndepOn K id L) →
      range (Basis.extend hL) = hL.extend (subset_univ L))

omit [FiniteDimensional K V] in
theorem subset_range_extend {L : Set V} (hL : LinearIndepOn K id L) :
    L ⊆ range (Basis.extend hL) := by
  simpa [Basis.range_extend hL] using (Basis.subset_extend hL)

theorem finite_extend_index {L : Set V} (hL : LinearIndepOn K id L) :
    (hL.extend (subset_univ L)).Finite := by
  exact IsNoetherian.finite_basis_index (Basis.extend hL)

end
