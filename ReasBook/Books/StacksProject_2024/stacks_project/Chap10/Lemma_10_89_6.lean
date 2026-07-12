import Mathlib
import StacksProject_2024.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M] [MittagLeffler R M]
variable {F : Type w} [AddCommGroup F] [Module R F]

-- Proof sketch: let `I` be the set of submodules `F' ≤ F` such that `x` lies in the range of
-- `F'.subtype.rTensor M`. Apply the tensor-product injectivity criterion from Proposition
-- `10.89.5` to the family of quotients `F ⧸ F'` indexed by `I`, so that `x` maps to zero in the
-- product of the quotient tensors and hence in the tensor with the product. Flatness identifies
-- the kernel of the induced map with the tensor of the intersection `sInf I`, giving the smallest
-- supporting submodule. A finite expression of `x` as a sum of pure tensors then shows this
-- smallest submodule is finitely generated, hence finite.
/-- Lemma 10.89.6: for a flat Mittag-Leffler module `M`, every tensor `x : F ⊗[R] M` is supported
by a smallest submodule `F' ≤ F`, and this smallest supporting submodule is finite. In Lean, the
support condition is expressed by `x ∈ LinearMap.range (F'.subtype.rTensor M)`. -/
theorem exists_smallest_finite_submodule_of_mem_tensorProduct
    (x : F ⊗[R] M) :
    ∃ F' : Submodule R F,
      IsLeast { F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M) } F' ∧
        Module.Finite R F' := sorry

end

end Module
