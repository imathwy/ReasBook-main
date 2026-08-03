module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

universe u

/- Proposition 60.2. Any group of order two is isomorphic to the multiplicative
group underlying `ZMod 2`. -/
#check fun {G : Type u} [Group G] (hG : Nat.card G = 2) ↦
  (mulEquivOfPrimeCardEq hG (Nat.card_zmod 2) : G ≃* Multiplicative (ZMod 2))
