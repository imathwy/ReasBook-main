import stacks_project.Chap15.Definition_15_124_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfValuationRings

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [CommRing B] [IsDomain B] [ValuationRing B]
variable [Algebra A B] [h : IsExtensionOfValuationRings A B]

local notation "K[" A "]" => FractionRing A

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

-- Proof sketch: compare the induced map `A → B` on valuation rings with the reduction modulo their
-- maximal ideals. The usual linear-independence argument over the residue field shows that any
-- residue-field basis lifts to a `K`-linearly independent family in `L`, forcing finiteness.
/-- The residue field extension of a finite fraction-field extension of valuation rings is
finite-dimensional. -/
theorem finiteDimensional_residueField_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    FiniteDimensional (ResidueField A) (ResidueField B) := sorry

attribute [local instance]
  finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

-- Proof sketch: pick units of `B` whose residue classes are linearly independent over
-- `ResidueField A` and pick nonzero elements whose values represent distinct cosets in the quotient
-- `Γ_B / Γ_A`. The textbook minimal-valuation argument shows that all products `bᵢ cⱼ` are
-- `K`-linearly independent in `L`, giving the stated inequality.
/-- Lemma 15.124.2: if `A ⊆ B` is an extension of valuation rings with fraction fields `K ⊆ L`
and `L / K` is finite, then the value-group index times the residue-field degree is bounded by the
fraction-field degree. -/
theorem ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    ramificationIndex A B * residueDegree A B ≤
      Module.finrank K[A] K[B] := sorry

end
