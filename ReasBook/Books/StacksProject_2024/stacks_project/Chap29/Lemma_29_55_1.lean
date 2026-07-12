import StacksProject_2024.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

-- Semantic recall: `lean_leansearch` surfaced the affine-spectrum dominant-morphism owner
-- `IsDominant`; local Chapter 29 precedent uses `UniversalHomeomorphism` for the source-facing
-- universal-homeomorphism condition and `Subalgebra A B` for affine subalgebras. The Stacks tag
-- evidence is consistent: item tag `0H3J` agrees with the source URL ending in `/tag/0H3J`.

/-- Lemma 29.55.1: if a ring map `A → B` induces a dominant morphism
`Spec(B) → Spec(A)`, then there is an `A`-subalgebra `B' ⊆ B` whose affine spectrum maps to
`Spec(A)` by a universal homeomorphism, and every factorization `A → C → B` through a ring `C`
whose spectrum is universally homeomorphic to `Spec(A)` has image contained in `B'`. -/
@[stacks 0H3J]
theorem exists_universalHomeomorphism_subalgebra_of_isDominant_specMap
    (hAB : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    ∃ B' : Subalgebra A B,
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
        ∀ {C : Type u} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B],
          UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C))) →
            ∀ c : C, algebraMap C B c ∈ B' := sorry

end

end AlgebraicGeometry
