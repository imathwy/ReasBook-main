import StacksProject_2024.Chap10.Lemma_10_127_4
import StacksProject_2024.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

-- Semantic recall: `lean_leansearch` surfaced mathlib's filtered colimit API for
-- `CommRingCat` and finite-presentation owners. Local precedent supplies
-- `selectedAlgebrasOverTargetCocone` for canonical colimit presentations over a target algebra,
-- and `UniversalHomeomorphism` for source-facing affine universal homeomorphisms. The Stacks tag
-- evidence is consistent: item tag `0EUJ` agrees with the source URL ending in `/tag/0EUJ`.

/-- Lemma 29.46.11 (1): if `A → B` induces a universal homeomorphism on spectra, then the
canonical family of finitely presented `A`-algebras over `B` whose spectra are universally
homeomorphic over `Spec A` is filtered and has colimit `B`. -/
@[stacks 0EUJ]
theorem universalHomeomorphism_specMap_isFilteredColimit_finitePresentation
    (hAB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    let P : ObjectProperty (Over (CommAlgCat.of A B)) := fun C ↦
      Algebra.FinitePresentation A C.left ∧
        UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C.left)))
    IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P)) := sorry

/-- Lemma 29.46.11 (2): if `A → B` induces isomorphisms on residue fields and a universal
homeomorphism on spectra, then the canonical family of finitely presented `A`-algebras over `B`
with the same two properties is filtered and has colimit `B`. -/
@[stacks 0EUJ]
theorem universalHomeomorphism_residueFieldMap_isIso_specMap_isFilteredColimit_finitePresentation
    (hAB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hκ : ∀ x : Spec (CommRingCat.of B),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x)) :
    let P : ObjectProperty (Over (CommAlgCat.of A B)) := fun C ↦
      Algebra.FinitePresentation A C.left ∧
        (let f : Spec (CommRingCat.of C.left) ⟶ Spec (CommRingCat.of A) :=
          Spec.map (CommRingCat.ofHom (algebraMap A C.left))
        UniversalHomeomorphism f ∧
          ∀ x : Spec (CommRingCat.of C.left), IsIso (f.residueFieldMap x))
    IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P)) := sorry

end

end AlgebraicGeometry
