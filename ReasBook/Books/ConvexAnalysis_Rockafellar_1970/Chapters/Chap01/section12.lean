import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_1_12 (from Chap01) -/
open scoped Affine

/- 
Source/core/bridge triage:
- `source-facing`: Text 1.12 says that affine maps send affine subsets to affine subsets and carry
  affine hulls to affine hulls. The coordinate-free affine-space formulation below specializes to
  affine maps between finite-dimensional affine spaces over a common scalar ring.
- `core/canonical`: the owner abstractions are project-local `Set.IsAffine k` (the intrinsic
  affine-subspace carrier owner), together with `affineSpan` and `AffineSubspace.map`.
- `bridge/view`: the first clause is expressed intrinsically as preservation of `Set.IsAffine`;
  the affine-hull image equality is owner-first via `AffineSubspace.map_span`, then read in
  textbook set form through `AffineSubspace.coe_map`.
- Domain-style sampling used here: `Set.IsAffine`, `affineSpan`, `AffineSubspace.map`,
  `AffineSubspace.map_span`, and `AffineSubspace.coe_map`.
- Primitive data vs derived API: `Set.IsAffine` and `AffineSubspace.map` are the public
  owner-level data for the first clause; `AffineSubspace.map_span` is the canonical owner theorem
  for the second clause, and textbook set equalities are thin bridge views.
- Layer target: owner-first (`core/canonical`) with textbook set-level bridge views.
- Canonicalization decision record (this pass):
  - Codomain/ambient check: no ordered-extended codomain is involved; the canonical ambient owner
    remains `AffineSubspace k P`.
  - Scalar check: the reused owners `AffineSubspace.map`/`affineSpan`/`AffineSubspace.map_span`
    currently require `[Ring k]`, so no weaker scalar layer is available here without upstream
    owner changes.
  - Owner check: expose affine-hull transport first at the owner equation
    `(affineSpan k s).map f = ...`, and keep the set-image equality as a bridge theorem.
  - Topology check: this item is not topology-facing.
  - Notation check: no extra notation is mathematically primary for this owner; keep the canonical
    `AffineSubspace`/`affineSpan` surfaces.
-/
recall Set.IsAffine
recall AffineSubspace.map
recall AffineSubspace.map_span
recall AffineSubspace.coe_map

namespace AffineMap

section Module

variable {k : Type*} {V₁ : Type*} {P₁ : Type*} {V₂ : Type*} {P₂ : Type*}
  [Ring k] [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

/-- Text 1.12 in canonical owner form: affine maps carry affine spans to affine spans. -/
theorem map_affineSpan (f : P₁ →ᵃ[k] P₂) (s : Set P₁) :
    (affineSpan k s).map f = affineSpan k (f '' s) := by
  simpa using AffineSubspace.map_span (f := f) s

/-- Text 1.12 (bridge/view): set-level affine-hull transport, read from `map_affineSpan`. -/
theorem image_affineSpan (f : P₁ →ᵃ[k] P₂) (s : Set P₁) :
    f '' affineSpan k s = affineSpan k (f '' s) := by
  simpa [AffineSubspace.coe_map] using
    congrArg (fun t : AffineSubspace k P₂ => (t : Set P₂))
      (map_affineSpan (f := f) (s := s))

end Module

end AffineMap

namespace Set

section Module

variable {k : Type*} {V₁ : Type*} {P₁ : Type*} {V₂ : Type*} {P₂ : Type*}
  [Ring k] [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

namespace IsAffine

/-- Text 1.12 (owner form, first clause): affine maps send affine subsets to affine subsets. -/
theorem image {s : Set P₁} (hs : affine[k] s) (f : P₁ →ᵃ[k] P₂) :
    affine[k] (f '' s) := by
  refine IsAffine.of_affineSpan_eq (k := k) ?_
  calc
    affineSpan k (f '' s) = f '' affineSpan k s := by
      simpa using (AffineMap.image_affineSpan (f := f) (s := s)).symm
    _ = f '' s := by simp [hs.affineSpan_eq (k := k)]

end IsAffine

end Module

end Set
