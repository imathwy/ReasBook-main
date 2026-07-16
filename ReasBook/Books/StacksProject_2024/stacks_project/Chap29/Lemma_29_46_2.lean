import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u v

namespace AlgebraicGeometry

section

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable {A : Type u} [CommRing A]

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `UniversallyClosed`, filtered colimits in `CommRingCat`, and the local
-- `UniversalHomeomorphism` owner. Nearby Chapter 29 precedent expresses the residue-field
-- isomorphism condition as `IsIso (f.residueFieldMap x)`. The Stacks tag evidence is consistent:
-- item tag `0CN8` agrees with the source URL ending in `/tag/0CN8`.

/-- Lemma 29.46.2 (1): if each affine morphism
`Spec(B_lambda) -> Spec(A)` in a filtered system of `A`-algebras is a universal homeomorphism,
then the induced morphism from the spectrum of the filtered colimit algebra is a universal
homeomorphism. -/
@[stacks 0CN8]
theorem universalHomeomorphism_colimitSpecMap_of_forall
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversalHomeomorphism stageMap) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversalHomeomorphism finalMap := sorry

/-- Lemma 29.46.2 (2): if each affine morphism in a filtered system of `A`-algebras is a
universal homeomorphism inducing isomorphisms on residue fields, then the induced morphism from
the spectrum of the filtered colimit algebra has the same property. -/
@[stacks 0CN8]
theorem universalHomeomorphism_residueFieldMap_isIso_colimitSpecMap_of_forall
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversalHomeomorphism stageMap ∧
        ∀ x : Spec (of (F.obj j)), IsIso (stageMap.residueFieldMap x)) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversalHomeomorphism finalMap ∧
      ∀ x : Spec (of (colimit F : CommAlgCat.{u} A)), IsIso (finalMap.residueFieldMap x) := sorry

/-- Lemma 29.46.2 (3): if each affine morphism
`Spec(B_lambda) -> Spec(A)` in a filtered system of `A`-algebras is universally closed, then the
induced morphism from the spectrum of the filtered colimit algebra is universally closed. -/
@[stacks 0CN8]
theorem universallyClosed_colimitSpecMap_of_forall
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversallyClosed stageMap) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversallyClosed finalMap := sorry

/-- Lemma 29.46.2 (4): if each affine morphism in a filtered system of `A`-algebras is
universally closed and universally injective, then the induced morphism from the spectrum of the
filtered colimit algebra has the same two properties. -/
@[stacks 0CN8]
theorem universallyClosed_universallyInjective_colimitSpecMap_of_forall
    (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]
    (hF : ∀ j,
      let stageMap : Spec (of (F.obj j)) ⟶ Spec (of A) :=
        Spec.map (ofHom (algebraMap A (F.obj j)))
      UniversallyClosed stageMap ∧ UniversallyInjective stageMap) :
    let finalMap : Spec (of (colimit F : CommAlgCat.{u} A)) ⟶ Spec (of A) :=
      Spec.map (ofHom (algebraMap A (colimit F : CommAlgCat.{u} A)))
    UniversallyClosed finalMap ∧ UniversallyInjective finalMap := sorry

end

end AlgebraicGeometry
