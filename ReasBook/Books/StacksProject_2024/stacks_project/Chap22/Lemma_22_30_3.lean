import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

-- Semantic search note: `lean_leansearch` surfaced commutative-base tensor/Hom owners such as
-- `ModuleCat.monoidalClosedHomEquiv` and `TensorProduct.AlgebraTensorModule.lift.equiv`, but those
-- do not model the present noncommutative bimodule-relative tensor/internal-Hom situation or the
-- graded and differential graded enrichments. In the current checked workspace, the canonical
-- owner for all three source clauses is therefore the hom-set equivalence of an adjunction.

/- The canonical core owner reused in all three source clauses is `Adjunction.homEquiv`. -/
recall Adjunction.homEquiv

section Ungraded

variable {ModB ModA : Type u}
variable [Category ModB] [Category ModA]
variable (tensorWithN : ModA ⥤ ModB) (homOverBFromN : ModB ⥤ ModA)
variable (adj : tensorWithN ⊣ homOverBFromN)
variable (M : ModA) (N' : ModB)

/- Lemma 22.30.3 (1): let `R` be a ring, let `A` and `B` be `R`-algebras, let `M` be a right
`A`-module, let `N` be an `(A, B)`-bimodule, and let `N'` be a right `B`-module. Once the
relative tensor functor `M ↦ M ⊗_A N` and the internal-Hom functor `N' ↦ Hom_B(N, N')` are
available as a checked adjoint pair, the source-facing comparison
`Hom_A(M, Hom_B(N, N')) ≅ Hom_B(M ⊗_A N, N')` is exactly the symmetric form of
`Adjunction.homEquiv`. -/
#check ((adj.homEquiv M N').symm :
  (M ⟶ homOverBFromN.obj N') ≃ (tensorWithN.obj M ⟶ N'))

end Ungraded

section Graded

variable {GrModB GrModA : Type u}
variable [Category GrModB] [Category GrModA]
variable (gradedTensorWithN : GrModA ⥤ GrModB) (gradedHomOverBFromN : GrModB ⥤ GrModA)
variable (gradedAdj : gradedTensorWithN ⊣ gradedHomOverBFromN)
variable (M : GrModA) (N' : GrModB)

/- Lemma 22.30.3 (2): if `A`, `B`, `M`, `N`, and `N'` are compatibly graded, then once the
graded relative tensor functor and graded internal-Hom functor are available, the source-facing
canonical isomorphism of graded `R`-modules is again the symmetric form of the corresponding
adjunction equivalence. -/
#check ((gradedAdj.homEquiv M N').symm :
  (M ⟶ gradedHomOverBFromN.obj N') ≃ (gradedTensorWithN.obj M ⟶ N'))

end Graded

section DifferentialGraded

variable {DGModB DGModA : Type u}
variable [Category DGModB] [Category DGModA]
variable (dgTensorWithN : DGModA ⥤ DGModB) (dgHomOverBFromN : DGModB ⥤ DGModA)
variable (dgAdj : dgTensorWithN ⊣ dgHomOverBFromN)
variable (M : DGModA) (N' : DGModB)

/- Lemma 22.30.3 (3): if `A`, `B`, `M`, `N`, and `N'` are compatibly differential graded, then
once the differential graded relative tensor functor and differential graded internal-Hom functor
are available, the source-facing canonical isomorphism of complexes of `R`-modules is the
symmetric form of the same adjunction equivalence. -/
#check ((dgAdj.homEquiv M N').symm :
  (M ⟶ dgHomOverBFromN.obj N') ≃ (dgTensorWithN.obj M ⟶ N'))

end DifferentialGraded
