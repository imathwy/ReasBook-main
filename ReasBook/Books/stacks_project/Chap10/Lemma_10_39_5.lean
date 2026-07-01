import Mathlib.RingTheory.Flat.Tensor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 10.39.5, clause `(1)`: the flatness condition on the `R`-module `M` is the canonical
owner predicate `Module.Flat R M`. -/
recall Module.Flat

/- Lemma 10.39.5, clause `(2)`: flatness is exactly preservation of injective linear maps under
right tensoring. -/
recall Module.Flat.iff_rTensor_preserves_injective_linearMap

/- Lemma 10.39.5, clause `(3)`: flatness is equivalent to injectivity of `I.subtype.rTensor M`
for every ideal `I`; via `TensorProduct.lid`, this is the Stacks map `I ⊗[R] M → M`. -/
recall Module.Flat.iff_rTensor_injective'

/- Lemma 10.39.5, clause `(4)`: it suffices to test injectivity of the canonical map
`I ⊗[R] M → M` on finitely generated ideals `I`. -/
recall Module.Flat.iff_lift_lsmul_comp_subtype_injective

end
