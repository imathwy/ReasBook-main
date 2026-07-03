import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (A : Type u) [CommSemiring A] (S : Submonoid A)
variable (M : Type v) [AddCommMonoid M] [Module A M]

/- Definition 10.9.6: for a commutative semiring `A`, a submonoid `S`, and an `A`-module `M`,
the localized module `S⁻¹M` is the canonical owner object `LocalizedModule S M`. -/
recall LocalizedModule

/- Companion recall: the canonical localization map `M → S⁻¹M` is the linear map
`LocalizedModule.mkLinearMap S M`. -/
recall LocalizedModule.mkLinearMap

/- Companion recall: the canonical owner instance expressing that `LocalizedModule S M` is the
localization of `M` with respect to `S` is `localizedModuleIsLocalizedModule`. -/
recall localizedModuleIsLocalizedModule

/- The canonical localization map sends `m` to the fraction `m / 1`. -/
recall LocalizedModule.mkLinearMap_apply

end
