import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Function

universe u

section

variable {ι : Type u} [Fintype ι]

/- Corollary 1.1.103 (1): for a finite family of pairwise coprime moduli, the Chinese remainder
theorem is the canonical ring equivalence `ZMod.prodEquivPi`. -/
recall ZMod.prodEquivPi (n : ι → ℕ) (hcop : Pairwise (Nat.Coprime on n)) :
    ZMod (∏ i, n i) ≃+* Π i, ZMod (n i)

/- Corollary 1.1.103 (2): the Chinese remainder ring equivalence induces the corresponding
multiplicative-group equivalence on units via `Units.mapEquiv`, and the units of a finite product
identify canonically with the product of the unit groups via `MulEquiv.piUnits`. -/
variable (n : ι → ℕ) (hcop : Pairwise (Nat.Coprime on n))

#check
  (((Units.mapEquiv (ZMod.prodEquivPi n hcop).toMulEquiv).trans MulEquiv.piUnits) :
    (ZMod (∏ i, n i))ˣ ≃* Π i, (ZMod (n i))ˣ)

end
