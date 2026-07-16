import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import StacksProject_2024.stacks_project.Chap22.«22_34_0_1»
import StacksProject_2024.stacks_project.Chap22.Lemma_22_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe uR vA vB vC vDA vDB vDC uA uB uC uDA uDB uDC

namespace CategoryTheory

section

variable {R : Type uR} [CommRing R]
variable {KA : Type uA} {KB : Type uB} {KC : Type uC}
variable {DA : Type uDA} {DB : Type uDB} {DC : Type uDC}
variable [Category.{vA} KA] [Category.{vB} KB] [Category.{vC} KC]
variable [Category.{vDA} DA] [Category.{vDB} DB] [Category.{vDC} DC]
variable (QisA : MorphismProperty KA) (QisB : MorphismProperty KB)
variable (QisC : MorphismProperty KC)
variable [QisB.ContainsIdentities]
variable (QC : KC ⥤ DC) [QC.IsLocalization QisC]
variable (tensorN : KA ⥤ KB) (tensorNN' : KA ⥤ KC)
variable (freeRightTensor : KB ⥤ KC) (freeLeftB : KB)
variable [freeRightTensor.HasPointwiseLeftDerivedFunctorAt QisB freeLeftB]
variable (CAsRComplex : CochainComplex (ModuleCat R) ℤ)

-- Semantic recall: `22.34.0.1` identifies the displayed tensor comparison with
-- `leftDerivedValueProjection`, `22.34.2` bridges invertibility of that displayed map to the
-- canonical derived tensor-composition comparison. In the current abstract Chapter `22` API the
-- concrete free right `(B, C)`-bimodule `B ⊗_R C` is not yet an owner, so the source-specific
-- bridge from K-flatness of `C` to invertibility of the displayed comparison is kept explicit as
-- `tensorAlgebraComparisonIsIso`.

/-- Lemma 22.34.3 (1): if the right tensor factor `C` is K-flat as a complex of
`R`-modules, then the displayed comparison `22.34.1.1` is an isomorphism. In the current
Chapter 22 API this displayed map is represented by
`leftDerivedValueProjection QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)`,
where `freeRightTensor` models tensoring with the free right `(B, C)`-bimodule `B ⊗_R C`. -/
@[stacks 09S4]
theorem tensorAlgebraComparison_isIso_of_rightKFlat
    (tensorAlgebraComparisonIsIso :
      (hC : CAsRComplex.IsKFlat) →
        IsIso
          (leftDerivedValueProjection
            QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)))
    (hC : CAsRComplex.IsKFlat) :
    IsIso
      (leftDerivedValueProjection QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)) :=
by
  exact tensorAlgebraComparisonIsIso hC

set_option synthInstance.checkSynthOrder false in
instance instTensorAlgebraComparisonIsIsoOfRightKFlat
    (tensorAlgebraComparisonIsIso :
      (hC : CAsRComplex.IsKFlat) →
        IsIso
          (leftDerivedValueProjection
            QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)))
    (hC : CAsRComplex.IsKFlat) :
    IsIso
      (leftDerivedValueProjection QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)) :=
  tensorAlgebraComparison_isIso_of_rightKFlat
    QisB freeRightTensor freeLeftB CAsRComplex tensorAlgebraComparisonIsIso hC

/-- Lemma 22.34.3 (2): under the same K-flatness hypothesis on `C`, the derived tensor
composition conclusion of Lemma `22.34.2` is valid for the tensor functors attached to
`N`, the free right `(B, C)`-bimodule `B ⊗_R C`, and `N'' = N ⊗_B (B ⊗_R C)`. -/
@[stacks 09S4]
theorem derivedTensorCompositionIsoOfRightKFlat
    (tensorAlgebraComparisonIsIso :
      (hC : CAsRComplex.IsKFlat) →
        IsIso
          (leftDerivedValueProjection
            QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)))
    (hC : CAsRComplex.IsKFlat)
    [(tensorN ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
    [(freeRightTensor ⋙ QC).HasLeftDerivedFunctor QisB]
    [(tensorNN' ⋙ QC).HasLeftDerivedFunctor QisA]
    (tensorAssoc : tensorN ⋙ freeRightTensor ≅ tensorNN') :
    IsIso
      (derivedTensorCompositionComparison
        QisA QisB QC tensorN freeRightTensor tensorNN' tensorAssoc) :=
by
  letI :
      IsIso
        (leftDerivedValueProjection
          QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)) :=
    tensorAlgebraComparison_isIso_of_rightKFlat
      QisB freeRightTensor freeLeftB CAsRComplex tensorAlgebraComparisonIsIso hC
  infer_instance

end

end CategoryTheory
