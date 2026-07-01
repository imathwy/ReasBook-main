import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/- Domain triage: this item lies in the linear algebra of threefold tensor products.
The `core/canonical` owner abstraction is the associator `TensorProduct.assoc R M N P`.
The `PiTensorProduct` declarations `tmulEquivDep` and `subsingletonEquiv` from Lemma `10.12.4`
provide one realization of the same comparison, but in this file they belong only to the
`bridge/view` layer and should not appear as a parallel public owner API. -/
recall TensorProduct.assoc

/- Lemma 10.12.5 on pure tensors: the canonical associator sends
`((m ⊗[R] n) ⊗[R] p)` to `m ⊗[R] (n ⊗[R] p)`. -/
recall TensorProduct.assoc_tmul

end
