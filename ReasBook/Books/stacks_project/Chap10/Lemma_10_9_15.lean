import Mathlib.Algebra.Module.LocalizedModule.Submodule

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

open Submodule

/- Lemma 10.9.15: for the canonical localization map `M → S⁻¹M`, every submodule of `S⁻¹M`
is the localization of its inverse image in `M`. This is exactly the `l_u_eq` theorem of the
owner Galois insertion `localized'gi` for submodule localization. -/
#check (localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).l_u_eq

end
