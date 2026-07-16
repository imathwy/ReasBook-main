import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksProject_2024.stacks_project.Chap22.Remark_22_37_5
import StacksProject_2024.stacks_project.Chap22.RLinearTriangulatedEquivalence

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uAA uBB vAA vBB

section

variable {R : Type uR} [CommRing R]
variable {DAA : Type uAA} {DBB : Type uBB}
variable [Category.{vAA} DAA] [Category.{vBB} DBB]
variable [HasZeroObject DAA] [HasZeroObject DBB]
variable [Preadditive DAA] [Preadditive DBB]
variable [Linear R DAA] [Linear R DBB]
variable [HasShift DAA ℤ] [HasShift DBB ℤ]
variable [∀ n : ℤ, (shiftFunctor DAA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DBB n).Additive]
variable [Pretriangulated DAA] [Pretriangulated DBB]

/-- The additive Hochschild cohomology comparison map induced by the bimodule-derived
equivalence in Remark 22.37.10. Its underlying function is the canonical map
`derivedTensorWithN_selfExtMap`. -/
def hochschildCohomologyMapOfBimoduleDerivedEquivalence
    (bimoduleTransport : CategoryTheory.RLinearTriangulatedEquivalence R DAA DBB)
    (Adiag : DAA) (Bdiag : DBB)
    (hUnit : bimoduleTransport.functor.obj Adiag ≅ Bdiag)
    (i : ℤ) :
    (Adiag ⟶ Adiag⟦i⟧) →+ (Bdiag ⟶ Bdiag⟦i⟧) where
  toFun := derivedTensorWithN_selfExtMap bimoduleTransport.functor Adiag Bdiag hUnit i
  map_zero' := by
    rw [derivedTensorWithN_selfExtMap_apply]
    rw [show bimoduleTransport.functor.map (0 : Adiag ⟶ Adiag⟦i⟧) = 0 by
      simpa using
        (bimoduleTransport.functor.mapAddHom : (Adiag ⟶ Adiag⟦i⟧) →+ _).map_zero]
    simp
  map_add' f g := by
    rw [derivedTensorWithN_selfExtMap_apply, derivedTensorWithN_selfExtMap_apply,
      derivedTensorWithN_selfExtMap_apply]
    rw [show bimoduleTransport.functor.map (f + g) =
        bimoduleTransport.functor.map f + bimoduleTransport.functor.map g by
      simpa using
        (bimoduleTransport.functor.mapAddHom : (Adiag ⟶ Adiag⟦i⟧) →+ _).map_add f g]
    simp [Preadditive.comp_add, Preadditive.add_comp]

/-- The additive Hochschild cohomology map from Remark 22.37.10 is the canonical comparison
`derivedTensorWithN_selfExtMap`. -/
@[simp]
theorem hochschildCohomologyMapOfBimoduleDerivedEquivalence_apply
    (bimoduleTransport : CategoryTheory.RLinearTriangulatedEquivalence R DAA DBB)
    (Adiag : DAA) (Bdiag : DBB)
    (hUnit : bimoduleTransport.functor.obj Adiag ≅ Bdiag)
    (i : ℤ) (f : Adiag ⟶ Adiag⟦i⟧) :
    hochschildCohomologyMapOfBimoduleDerivedEquivalence
        bimoduleTransport Adiag Bdiag hUnit i f =
      derivedTensorWithN_selfExtMap bimoduleTransport.functor Adiag Bdiag hUnit i f :=
  rfl

/-- Remark 22.37.10: suppose the displayed functor
`M ↦ Ω' ⊗[A]ᴸ M ⊗[A]ᴸ Ω` between the derived categories of differential graded bimodules is an
`R`-linear equivalence of triangulated categories, sends the diagonal `(A, A)`-bimodule `A` to
the diagonal `(B, B)`-bimodule `B`. Then in every degree the canonical shift comparison of the
equivalence gives a bijection on Hochschild cohomology groups
`Hom(A, A[i]) → Hom(B, B[i])`, namely the canonical map
`derivedTensorWithN_selfExtMap` induced by the bimodule-derived equivalence. -/
@[stacks 09ST]
theorem hochschildCohomologyMapOfBimoduleDerivedEquivalence_bijective
    (bimoduleTransport : CategoryTheory.RLinearTriangulatedEquivalence R DAA DBB)
    (Adiag : DAA) (Bdiag : DBB)
    (hUnit : bimoduleTransport.functor.obj Adiag ≅ Bdiag)
    (i : ℤ) :
    Function.Bijective
      (derivedTensorWithN_selfExtMap bimoduleTransport.functor Adiag Bdiag hUnit i) := by
  simpa [CategoryTheory.RLinearTriangulatedEquivalence.functor] using
    (selfExt_bijective_of_rLinearTriangulatedEquivalence
      bimoduleTransport.toEquivalence Adiag Bdiag hUnit i)

end
