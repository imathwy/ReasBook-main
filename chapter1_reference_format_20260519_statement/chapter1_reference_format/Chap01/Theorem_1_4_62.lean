import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.4.62: the map `ℂ → ℂˣ`, `z ↦ e^z`, is the canonical group homomorphism obtained
from `Complex.expMonoidHom` by viewing its values as units. The additive group structure on `ℂ`
is represented in Lean by the multiplicative wrapper `Multiplicative ℂ`. -/
recall Complex.expMonoidHom : Multiplicative ℂ →* ℂ
#check (Complex.expMonoidHom.toHomUnits : Multiplicative ℂ →* ℂˣ)
