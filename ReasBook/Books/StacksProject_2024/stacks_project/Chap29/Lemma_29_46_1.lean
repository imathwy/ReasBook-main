import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `UniversallyClosed`; local Chapter 29 precedent supplies `UniversalHomeomorphism`, and
-- residue-field isomorphism clauses use `Scheme.Hom.residueFieldMap`.  The Stacks tag evidence is
-- consistent: item tag `0CN7` agrees with the source URL ending in `/tag/0CN7`.

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 29.46.1 (1): if `Spec B → Spec A` is a universal homeomorphism, then for every
`A`-subalgebra `B' ⊆ B`, the induced morphism `Spec B' → Spec A` is a universal homeomorphism. -/
@[stacks 0CN7]
theorem universalHomeomorphism_specMap_of_subalgebra
    (B' : Subalgebra A B)
    (hf : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B'))) := sorry

/-- Lemma 29.46.1 (2): if `Spec B → Spec A` is a universal homeomorphism inducing isomorphisms
on residue fields, then the same is true for `Spec B' → Spec A` for every `A`-subalgebra
`B' ⊆ B`. -/
@[stacks 0CN7]
theorem universalHomeomorphism_and_residueFieldMap_isIso_specMap_of_subalgebra
    (B' : Subalgebra A B)
    (hf : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hκ :
      ∀ x : Spec (CommRingCat.of B),
        IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x)) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
      ∀ x : Spec (CommRingCat.of B'),
        IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B'))).residueFieldMap x) := sorry

/-- Lemma 29.46.1 (3): if `Spec B → Spec A` is universally closed, then for every
`A`-subalgebra `B' ⊆ B`, the induced morphism `Spec B' → Spec A` is universally closed. -/
@[stacks 0CN7]
theorem universallyClosed_specMap_of_subalgebra
    (B' : Subalgebra A B)
    (hf : UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B'))) := sorry

/-- Lemma 29.46.1 (4): if `Spec B → Spec A` is universally closed and universally injective,
then the same is true for `Spec B' → Spec A` for every `A`-subalgebra `B' ⊆ B`. -/
@[stacks 0CN7]
theorem universallyClosed_and_universallyInjective_specMap_of_subalgebra
    (B' : Subalgebra A B)
    (hclosed : UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hinj : UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversallyClosed (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
      UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap A B'))) := sorry

end

end AlgebraicGeometry
