import Mathlib

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra

universe u

section

variable {k R Ω : Type u} [Field k] [CommRing R] [Algebra k R]
variable [Field Ω] [Algebra k Ω] [Algebra (SeparableClosure k) Ω]
variable [IsScalarTower k (SeparableClosure k) Ω]

/-- Helper for Lemma 10.48.2: the iterated base change through `SeparableClosure k` is the usual
`Ω`-base change, via the standard `commRight + congr + cancelBaseChange + comm` comparison. -/
noncomputable def baseChange_separableClosure_tensor_equiv :
    let _ : Algebra (SeparableClosure k) (R ⊗[k] SeparableClosure k) :=
      Algebra.TensorProduct.rightAlgebra
    ((R ⊗[k] SeparableClosure k) ⊗[SeparableClosure k] Ω) ≃+* R ⊗[k] Ω :=
  letI : Algebra (SeparableClosure k) (R ⊗[k] SeparableClosure k) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra (SeparableClosure k) (SeparableClosure k ⊗[k] R) :=
    Algebra.TensorProduct.leftAlgebra
  -- Proof comment: freeze the left-factor `SeparableClosure k`-algebra on
  -- both tensor orders, then reuse the source proof's standard tensor-order comparison.
  let e12 :=
    (Algebra.TensorProduct.comm (SeparableClosure k) (R ⊗[k] SeparableClosure k) Ω).trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : Ω ≃ₐ[SeparableClosure k] Ω)
        (Algebra.TensorProduct.commRight k (SeparableClosure k) R).symm)
  let e3 := (Algebra.TensorProduct.cancelBaseChange k (SeparableClosure k) Ω Ω R).toRingEquiv
  let e4 := (Algebra.TensorProduct.comm k R Ω).symm.toRingEquiv
  (e12.toRingEquiv.trans e3).trans e4

end

end Algebra
