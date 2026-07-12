import StacksProject_2024.Chap13.Definition_13_14_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe vB vC uB uC

namespace CategoryTheory

section

variable {KB : Type uB} {KC : Type uC}
variable [Category.{vB} KB] [Category.{vC} KC]
variable (QisB : MorphismProperty KB) [QisB.ContainsIdentities]
variable (freeRightTensor : KB ⥤ KC) (freeLeftB : KB)
variable [freeRightTensor.HasPointwiseLeftDerivedFunctorAt QisB freeLeftB]

/- 22.34.1.1: the displayed map
`(A ⊗[R] B)_B ⊗^{\mathbf L}_B {}_B(B ⊗[R] C)_C ⟶ (A ⊗[R] B ⊗[R] C)_C`
is the Chapter `22` identity-denominator projection for the underived tensor functor represented
by the free right `(B, C)`-bimodule. In the current abstract Chapter `22` API, where the concrete
DG-bimodule owners are modeled by `freeRightTensor` and `freeLeftB`, this item is therefore the
specialization of `leftDerivedValueProjection` at the identity denominator on `freeLeftB`. -/
#check leftDerivedValueProjection QisB freeRightTensor (𝟙 freeLeftB) (QisB.id_mem freeLeftB)

end

end CategoryTheory
