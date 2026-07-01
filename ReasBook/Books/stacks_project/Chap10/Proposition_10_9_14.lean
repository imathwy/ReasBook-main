import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]
variable (S : Submonoid A) (I : Ideal A)

local notation "Sbar" => Algebra.algebraMapSubmonoid (A ⧸ I) S
local notation "IS" => Ideal.map (algebraMap A (Localization S)) I

/- Proposition 10.9.14: the quotient of `Localization S` by the localized ideal
`IS` is canonically isomorphic to the localization of `A ⧸ I` at the image `Sbar` of `S`.
This is exactly the specialization of the owner equivalence `Localization.algEquiv` to the
quotient ring `Localization S ⧸ IS`. -/
#check
  (Localization.algEquiv Sbar (Localization S ⧸ IS) :
    Localization Sbar ≃ₐ[A ⧸ I] Localization S ⧸ IS)

end
