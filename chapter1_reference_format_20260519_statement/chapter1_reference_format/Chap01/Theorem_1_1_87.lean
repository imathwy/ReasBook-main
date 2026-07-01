import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {G : Type u} [Group G]

/- Theorem 1.1.87: for a finite group `G`, the order of any element `g` divides the order of `G`,
namely `Nat.card G`. -/
recall orderOf_dvd_natCard (g : G) : orderOf g ∣ Nat.card G

/- In particular, raising an element of a finite group to the order of the group gives the
identity. -/
recall pow_card_eq_one' (g : G) : g ^ Nat.card G = 1
