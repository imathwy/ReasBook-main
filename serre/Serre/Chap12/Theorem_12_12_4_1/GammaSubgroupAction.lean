import Mathlib

noncomputable section

universe u v

namespace Representation

open IsCyclotomicExtension.Rat

section GammaSubgroup

variable {L : Type v} [Field L] [NumberField L]

/-- Serre's subgroup `Γ_K ⊆ (ℤ / nℤ)ˣ` attached to an intermediate field `K ⊆ L` inside the
cyclotomic realization `L / ℚ`. -/
abbrev gammaSubgroup (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ L]
    (K : IntermediateField ℚ L) : Subgroup (ZMod n)ˣ :=
  (galEquivZMod n L).mapSubgroup K.fixingSubgroup

end GammaSubgroup

section CyclotomicUnitAction

variable {L : Type v} [Field L] [Algebra ℚ L]
variable {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ L]

/-- The canonical cyclotomic Galois action of `(ℤ / nℤ)ˣ` on an `n`-th cyclotomic field. -/
instance cyclotomicUnitMulSemiringAction : MulSemiringAction (ZMod n)ˣ L :=
  MulSemiringAction.compHom L
    ((IsCyclotomicExtension.autEquivPow L
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n))).symm.toMonoidHom)

end CyclotomicUnitAction

section ExponentGammaSubgroup

variable (G : Type u) [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

scoped[Representation] notation:max "Γ[" K "](" G ")" =>
  gammaSubgroup (Monoid.exponent G) K

scoped[Representation] notation:max "Γ_ℚ(" G ")" =>
  (ZMod (Monoid.exponent G))ˣ

end ExponentGammaSubgroup

end Representation
