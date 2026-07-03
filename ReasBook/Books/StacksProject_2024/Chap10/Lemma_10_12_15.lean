import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommSemiring R]
variable {S : Submonoid R}
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 10.12.15 is a `bridge/view` item in the localization/base-change domain. The primitive
owner abstraction is `IsLocalizedModule.isBaseChange`, and the canonical derived comparison is
`LocalizedModule.equivTensorProduct`. The Stacks statement uses its symmetric orientation. -/

/- Lemma 10.12.15: the localized module `S⁻¹M` is canonically isomorphic to
`S⁻¹R ⊗[R] M`. This is the symmetric orientation of the owner equivalence
`LocalizedModule.equivTensorProduct`. -/
#check (LocalizedModule.equivTensorProduct S M).symm

/- The symmetric form of the canonical isomorphism sends `(a / s) ⊗ m` to `a • (m / s)`. -/
recall LocalizedModule.equivTensorProduct_symm_apply_tmul

end
