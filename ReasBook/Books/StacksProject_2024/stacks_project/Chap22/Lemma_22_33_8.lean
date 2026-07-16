import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import StacksProject_2024.stacks_project.Chap22.DGModuleModel
import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory
open scoped CategoryTheory

noncomputable section

universe uR uR' uA uA' uDA uDA' uDR uDR'
universe vDA vDA' vDR vDR'

section

variable {R : Type uR} {R' : Type uR'} [CommRing R] [CommRing R']
variable {ModdgA : Type uA} {ModdgAprime : Type uA'}
variable [DifferentialGradedCategory R ModdgA]
variable [DifferentialGradedCategory R' ModdgAprime]
variable {DA : Type uDA} {DAprime : Type uDA'} {DR : Type uDR} {DRprime : Type uDR'}
variable [Category.{vDA} DA] [Category.{vDA'} DAprime]
variable [Category.{vDR} DR] [Category.{vDR'} DRprime]

variable (QisA : MorphismProperty (K R ModdgA))
variable (QisAprime : MorphismProperty (K R' ModdgAprime))
variable (QA : K R ModdgA ⥤ DA) [QA.IsLocalization QisA]
variable (QAprime : K R' ModdgAprime ⥤ DAprime) [QAprime.IsLocalization QisAprime]
variable (AasRComplex : CochainComplex (ModuleCat R) ℤ)
variable (tensorWithBaseChangeAlgebraOnK baseChangeOnK :
  K R ModdgA ⥤ K R' ModdgAprime)

-- Semantic recall hits: `Functor.totalLeftDerived`, `Functor.totalRightDerived`, and the
-- Chapter 22 owner `DifferentialGradedCategory.K`. Local search found no checked concrete owner
-- for the DG algebra base change `A ⊗_R R'`, so this item keeps the two source functors explicit:
-- `tensorWithBaseChangeAlgebraOnK` models `M ↦ M ⊗_A A'`, while `baseChangeOnK` models
-- `M ↦ M ⊗_R R'`.

variable [(tensorWithBaseChangeAlgebraOnK ⋙ QAprime).HasLeftDerivedFunctor QisA]

-- The source-facing comparison family for Lemma `22.33.8`: under the K-flatness hypothesis on
-- `A`, the derived tensor functor is exhibited as a right derived functor of homotopy-category
-- base change by a natural transformation from the underived base-change functor
-- `baseChangeOnK ⋙ QAprime` to the derived tensor functor on `D(A', d)`.
variable (tensorBaseChangeComparison :
  AasRComplex.IsKFlat →
    ((baseChangeOnK ⋙ QAprime) ⟶
      (QA ⋙ (tensorWithBaseChangeAlgebraOnK ⋙ QAprime).totalLeftDerived QA QisA)))

/-- Lemma 22.33.8 (1): if the differential graded algebra `A` is K-flat as a complex of
`R`-modules, then the derived tensor functor `- ⊗_A^L A'` is identified with the right derived
functor of the homotopy-category base-change functor `M ↦ M ⊗_R R'`. The functor
`tensorWithBaseChangeAlgebraOnK` is the underived tensor-by-`A'` functor from Lemma `22.33.2`,
and `baseChangeOnK` is the displayed base-change functor on `K(A, d)`. The right-derived-functor
structure is carried by `tensorBaseChangeComparison`. -/
@[stacks 0BYZ]
instance derivedTensorWithBaseChangeAlgebra_isRightDerivedFunctor
    (hA : AasRComplex.IsKFlat) :
    Functor.IsRightDerivedFunctor
      ((tensorWithBaseChangeAlgebraOnK ⋙ QAprime).totalLeftDerived QA QisA)
      (tensorBaseChangeComparison hA)
      QisA := by
  sorry

variable (restrictionA : DA ⥤ DR)
variable (restrictionAprime : DAprime ⥤ DRprime)
variable (derivedBaseChangeOnR : DR ⥤ DRprime)
variable (restrictionComparison :
  AasRComplex.IsKFlat →
    (((tensorWithBaseChangeAlgebraOnK ⋙ QAprime).totalLeftDerived QA QisA ⋙ restrictionAprime) ⟶
      (restrictionA ⋙ derivedBaseChangeOnR)))

/-- Lemma 22.33.8 (2): under the same K-flatness hypothesis on `A`, the square obtained by
restricting scalars from `D(A, d)` and `D(A', d)` to the derived categories of `R` and `R'`
commutes with the derived base-change functor `- ⊗_R^L R'`. -/
@[stacks 0BYZ]
theorem derivedTensorWithBaseChangeAlgebra_restriction_commutes
    (hA : AasRComplex.IsKFlat) :
    IsIso (restrictionComparison hA) := by
  sorry

set_option synthInstance.checkSynthOrder false in
instance derivedTensorWithBaseChangeAlgebra_restriction_commutes_inst
    (hA : AasRComplex.IsKFlat) :
    IsIso (restrictionComparison hA) :=
  derivedTensorWithBaseChangeAlgebra_restriction_commutes
    QisA QA QAprime AasRComplex tensorWithBaseChangeAlgebraOnK
    restrictionA restrictionAprime derivedBaseChangeOnR restrictionComparison hA

variable (underlyingRComplexOnK : K R ModdgA ⥤ ModuleCat.KDGMod R)

/-- Lemma 22.33.8 (3): if a differential graded `A`-module `M` is K-flat as a complex of
`R`-modules, then its ordinary base change `M ⊗_R R'` represents the derived tensor
`M ⊗_A^L A'` in `D(A', d)`. Here `underlyingRComplexOnK` is the Chapter 22 underlying-complex
bridge from `K(A, d)` to `K(R)`, so the K-flatness hypothesis is the canonical owner
`(underlyingRComplexOnK.obj M).IsKFlat`. -/
@[stacks 0BYZ]
theorem kFlatBaseChange_represents_derivedTensorWithBaseChangeAlgebra
    (hA : AasRComplex.IsKFlat)
    (M : K R ModdgA) (hM : (underlyingRComplexOnK.obj M).IsKFlat) :
    IsIso (((tensorBaseChangeComparison hA).app M)) := by
  sorry

set_option synthInstance.checkSynthOrder false in
instance kFlatBaseChange_represents_derivedTensorWithBaseChangeAlgebra_inst
    (hA : AasRComplex.IsKFlat)
    (M : K R ModdgA) (hM : (underlyingRComplexOnK.obj M).IsKFlat) :
    IsIso (((tensorBaseChangeComparison hA).app M)) :=
  kFlatBaseChange_represents_derivedTensorWithBaseChangeAlgebra
    QisA QA QAprime AasRComplex tensorWithBaseChangeAlgebraOnK baseChangeOnK
    tensorBaseChangeComparison underlyingRComplexOnK hA M hM

end
