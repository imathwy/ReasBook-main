import StacksProject_2024.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A subalgebra satisfying the weak-normalization universal homeomorphism condition,
residue-field isomorphism condition, and universal containment property. -/
class IsWeakNormalizationSubalgebra (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (B' : Subalgebra A B) : Prop where
  universalHomeomorphism :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B')))
  residueFieldMap_isIso :
    ∀ x : Spec (CommRingCat.of B'),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B'))).residueFieldMap x)
  contains_image_of_universalHomeomorphism_residueFieldMap_isIso :
    ∀ {C : Type u} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B],
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C))) →
        (∀ x : Spec (CommRingCat.of C),
          IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap x)) →
          ∀ c : C, algebraMap C B c ∈ B'

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-spectrum dominant-morphism
-- owner `IsDominant` and `Scheme.Hom.residueFieldMap`; local Chapter 29 precedent uses
-- `UniversalHomeomorphism` for source-facing affine universal homeomorphisms and
-- `Subalgebra A B` for affine subalgebras. The Stacks tag evidence is consistent: item tag
-- `0H3L` agrees with the source URL ending in `/tag/0H3L`.

/-- Lemma 29.55.3: if a ring map `A → B` induces a dominant morphism
`Spec(B) → Spec(A)`, then there is an `A`-subalgebra `B' ⊆ B` such that
`Spec(B') → Spec(A)` is a universal homeomorphism inducing isomorphisms on residue fields, and
every factorization `A → C → B` with the same two properties has image contained in `B'`. -/
@[stacks 0H3L]
theorem exists_universalHomeomorphism_residueFieldMap_isIso_subalgebra_of_isDominant_specMap
    (hAB : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    ∃ B' : Subalgebra A B, IsWeakNormalizationSubalgebra A B B' := sorry

end

end AlgebraicGeometry
