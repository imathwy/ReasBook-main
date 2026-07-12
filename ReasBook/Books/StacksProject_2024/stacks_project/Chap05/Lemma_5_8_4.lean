import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.8.4:
- primary domain: irreducible components of a topological space
- inspected owner declarations:
  `irreducibleComponents`,
  `irreducibleComponents_eq_maximals_closed`,
  `isIrreducible_iff_sUnion_isClosed`,
  `mem_of_subset_sUnion_irreducibleComponents`
- best owner abstraction: `irreducibleComponents X` is the core/canonical owner; the present lemma
  is a `bridge/view` statement identifying a finite irredundant closed irreducible cover with that
  canonical set of components
- primitive-vs-derived split: the primitive data here are the finite family `S`, the cover
  equality, and the closedness/irreducibility/irredundancy hypotheses on its members; membership in
  `irreducibleComponents X` is derived from the owner maximality and finite-cover membership API
  rather than from a local duplicate notion of component
-/

/-- Lemma 5.8.4: if a topological space is covered by finitely many irreducible closed subsets and
none of them is contained in the union of the others, then the irreducible components are exactly
those subsets. A finite family of closed irreducible subsets is represented canonically by a
finite set `S : Set (Set X)`, and the conclusion is equality with `irreducibleComponents X`. -/
-- Proof sketch: each `Z ∈ S` is maximal among closed irreducible subsets because any larger
-- closed irreducible `Y` is forced by the finite cover to lie in some `W ∈ S`, and irredundancy
-- then gives `W = Z`. Hence `Z` is an irreducible component via
-- `irreducibleComponents_eq_maximals_closed`. Conversely, any irreducible component lies in `S`
-- by `mem_of_subset_sUnion_irreducibleComponents`.
theorem irreducibleComponents_eq_of_finite_irreducible_closed_cover
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirr : ∀ Z ∈ S, IsIrreducible Z)
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z})) :
    irreducibleComponents X = S := by
  classical
  have hS_subset_components : S ⊆ irreducibleComponents X := by
    intro Z hZ
    rw [irreducibleComponents_eq_maximals_closed]
    refine ⟨⟨hclosed Z hZ, hirr Z hZ⟩, ?_⟩
    intro Y hY hZY
    obtain ⟨W, hW, hYW⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp hY.2 hS.toFinset
        (fun W hW ↦ hclosed W (hS.mem_toFinset.mp hW))
        (hS.coe_toFinset.symm ▸ by
          simp [hcover])
    have hWS : W ∈ S := hS.mem_toFinset.mp hW
    have hWZ : W = Z := by
      by_contra hne
      exact hirredundant Z hZ <| by
        intro x hx
        refine mem_sUnion.2 ?_
        exact ⟨W, ⟨hWS, by simpa [mem_singleton_iff] using hne⟩, hYW (hZY hx)⟩
    subst hWZ
    exact hYW
  refine Set.Subset.antisymm ?_ hS_subset_components
  intro Z hZ
  exact mem_of_subset_sUnion_irreducibleComponents Z hZ S hS hS_subset_components
    (by simp [hcover])
