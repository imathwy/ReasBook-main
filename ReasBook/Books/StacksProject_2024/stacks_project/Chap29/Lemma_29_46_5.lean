import StacksProject_2024.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {B : Type u} [CommRing B]

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Hom.residueFieldMap` as the canonical
-- residue-field map API, and local Chapter 29 precedent supplies `UniversalHomeomorphism` for
-- source-facing universal homeomorphisms.  The Stacks tag evidence is consistent: item tag
-- `0CNB` agrees with the source URL ending in `/tag/0CNB`.

/-- Lemma 29.46.5: if `A ⊂ B` is a ring extension such that `Spec(B) → Spec(A)` is a universal
homeomorphism inducing isomorphisms on residue fields, with `A ≠ B`, then some element
`b ∈ B \ A` satisfies `b ^ 2 ∈ A` as well as `b ^ 3 ∈ A`. -/
@[stacks 0CNB]
theorem exists_sq_cube_mem_subring_of_specMap_universalHomeomorphism_residueFieldMap_isIso
    (A : Subring B)
    (hSpec : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)))
    (hκ :
      ∀ x : Spec (CommRingCat.of B),
        IsIso ((Spec.map (CommRingCat.ofHom A.subtype)).residueFieldMap x))
    (hneq : A ≠ ⊤) :
    ∃ b : B, b ∉ A ∧ ∃ _ : b ^ 2 ∈ A, b ^ 3 ∈ A := sorry

end AlgebraicGeometry
