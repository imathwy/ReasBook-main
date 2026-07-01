import Mathlib

noncomputable section

universe u

namespace Representation

section PowerAction

variable {G : Type u} [Group G] [NeZero (Monoid.exponent G)]

/-- The natural-number representative attached to an exponent unit
`t ∈ (ℤ / exp(G)ℤ)ˣ`. -/
abbrev galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) : ℕ :=
  (t : ZMod (Monoid.exponent G)).val

/-- The ambient `(ℤ / exp(G)ℤ)ˣ` power action on `G`. -/
instance galoisPowerPow : Pow G (ZMod (Monoid.exponent G))ˣ where
  pow s t := s ^ galoisPowerExponentUnit t

omit [NeZero (Monoid.exponent G)] in
-- Proof sketch: unfold the ambient `Pow` instance on exponent units.
/-- Rewriting lemma for the ambient exponent-unit power action. -/
@[simp] theorem pow_unit_eq_pow_nat (s : G) (t : (ZMod (Monoid.exponent G))ˣ) :
    (s ^ t : G) = s ^ galoisPowerExponentUnit t := rfl

variable {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ}

/-- Serre's `Γ_K`-power action on group elements, written with the ordinary exponent notation. -/
instance gammaSubgroupPow : Pow G ΓK where
  pow s t := s ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)

omit [NeZero (Monoid.exponent G)] in
-- Proof sketch: unfold the `Pow` instance on `ΓK`.
/-- Rewriting lemma for Serre's `Γ_K`-power action in terms of the underlying natural-number
exponent. -/
@[simp] theorem pow_subgroup_eq_pow_nat (s : G) (t : ΓK) :
    (s ^ t : G) = s ^ galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ) := rfl

end PowerAction

end Representation
