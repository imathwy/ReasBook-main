import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.Chap24.Definition_24_25_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace DifferentialGradedModule

section

/- Semantic search note: `lean_leansearch` was unavailable in this runner, so the owner/API choice
was checked against Chapter 24's `IsGradedInjective` owner and the Chapter 13 K-injective lifting
pattern. The source-facing statement keeps graded injectivity as the main hypothesis, while the
canonical companion theorem below exposes the same result directly from injectivity of the
underlying graded object. The graded-monomorphism condition on `b` remains an explicit theorem
hypothesis, since it is a source-facing property of the chosen map rather than ambient structure on
the objects. -/

variable {GrModA : Type u} [Category.{v} GrModA] [Abelian GrModA]
variable (forgetToGraded : CochainComplex GrModA ℤ ⥤ GrModA)
variable {M M' I : CochainComplex GrModA ℤ}
variable (a : M ⟶ I) (b : M ⟶ M')

/-- Companion API for Lemma 24.25.9: if the underlying graded object of `I` is injective, then a
morphism from an acyclic complex into a K-injective target extends across any map whose underlying
graded morphism is monic. -/
theorem exists_lift_of_acyclic_to_kInjective_of_injective
    (hM : M.Acyclic) (hb : Mono (forgetToGraded.map b))
    [I.IsKInjective] [Injective (forgetToGraded.obj I)] :
    ∃ a' : M' ⟶ I, b ≫ a' = a := sorry

/-- Lemma 24.25.9: in a differential graded module category presented as cochain complexes in an
abelian category of graded modules, if `I` is K-injective and graded injective, then every
morphism `a : M ⟶ I` from an acyclic object extends across any morphism `b : M ⟶ M'` whose
underlying graded morphism is a monomorphism. -/
theorem exists_lift_of_acyclic_to_kInjective_of_isGradedInjective
    (hM : M.Acyclic) (hb : Mono (forgetToGraded.map b))
    [I.IsKInjective] [IsGradedInjective forgetToGraded I] :
    ∃ a' : M' ⟶ I, b ≫ a' = a :=
  exists_lift_of_acyclic_to_kInjective_of_injective
    forgetToGraded a b hM hb

end

end DifferentialGradedModule
