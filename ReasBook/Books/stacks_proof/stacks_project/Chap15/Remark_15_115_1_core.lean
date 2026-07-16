import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_112_1

-- Core owner declarations extracted from Remark 15.115.1.

open scoped TensorProduct

universe u v w x y

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance l1CommRing : CommRing L1 :=
  Ideal.Quotient.commRing _

/-- The canonical `A`-algebra map `K₁ → L₁` induced by the right tensor-factor embedding
`K₁ → L ⊗[K] K₁` and passage to the reduced quotient. -/
private abbrev rightTensorFactorToReducedTensorBaseChange : K1 →ₐ[A] L1 :=
  (Ideal.Quotient.mkₐ A _).comp
    ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1).restrictScalars A)

/-- The canonical map `A₁ → L₁` induced by the right tensor-factor embedding
`K₁ → L ⊗[K] K₁` and passage to the reduced quotient. -/
private abbrev integralClosureToReducedTensorBaseChange : A1 →ₐ[A] L1 :=
  (integralClosure A L1).val.comp
    rightTensorFactorToReducedTensorBaseChange.mapIntegralClosure

/-- Elements of `A₁` map into the integral closure `B₁` inside the reduced base change `L₁`. -/
private theorem integralClosureToReducedTensorBaseChange_mem_integralClosure (x : A1) :
    integralClosureToReducedTensorBaseChange x ∈ B1 := by
  let y : integralClosure A L1 := rightTensorFactorToReducedTensorBaseChange.mapIntegralClosure x
  have hyA : IsIntegral A (y : L1) := y.2
  have hyB : IsIntegral B (y : L1) := IsIntegral.tower_top hyA
  simpa [integralClosureToReducedTensorBaseChange, y] using hyB

/-- The canonical map `A₁ → B₁` induced by reduced tensor-product base change. -/
def reducedTensorBaseChangeIntegralClosureMap : A1 →ₐ[A] B1 :=
  AlgHom.codRestrict
    integralClosureToReducedTensorBaseChange
    ((integralClosure B L1).restrictScalars A)
    integralClosureToReducedTensorBaseChange_mem_integralClosure

/-- The reduced tensor-product integral closure carries its canonical `A₁`-algebra structure
through `reducedTensorBaseChangeIntegralClosureMap`. -/
instance : Algebra A1 B1 :=
  reducedTensorBaseChangeIntegralClosureMap.toRingHom.toAlgebra

end
