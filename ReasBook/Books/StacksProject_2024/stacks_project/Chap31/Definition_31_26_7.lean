import StacksProject_2024.stacks_project.Chap31.Definition_31_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall note: Chapter 31 already exposes the canonical Weil-divisor owner `Div(X)` in
-- `Definition_31_26_2` and the principal-divisor coefficient owner
-- `Scheme.principalWeilDivisorCoeff` in `Definition_31_26_5`. Definition 31.26.7 therefore adds
-- only the subgroup of principal divisors and the resulting quotient `Cl(X)`.

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
variable [Scheme.PrimeDivisorDiscreteValuationRings X]

local notation "principalCoeff" =>
  Scheme.principalWeilDivisorCoeff X (Scheme.primeDivisorDiscreteValuationRing X)

/-- A Weil divisor on `X` is principal when its coefficients are those of a function-field unit. -/
def IsPrincipalWeilDivisor (D : Div(X)) : Prop :=
  ∃ f : X.functionFieldˣ, ∀ Z : PrimeDivisor X, D.coeff Z = principalCoeff f Z

/-- The subgroup of `Div(X)` consisting of principal Weil divisors. -/
def principalWeilDivisors : AddSubgroup (Div(X)) where
  carrier := IsPrincipalWeilDivisor X
  zero_mem' := by
    sorry
  add_mem' hD hE := by
    sorry
  neg_mem' hD := by
    sorry

notation "Prin(" X ")" => principalWeilDivisors X

/-- A Weil divisor lies in `Prin(X)` exactly when its coefficients come from a
function-field unit via the principal-divisor coefficient formula. -/
theorem mem_principalWeilDivisors_coeff_iff (D : Div(X)) :
    D ∈ Prin(X) ↔
      ∃ f : X.functionFieldˣ, ∀ Z : PrimeDivisor X, D.coeff Z = principalCoeff f Z :=
  Iff.rfl

/-- The principal Weil divisor attached to a function-field unit lies in `Prin(X)`. -/
theorem principalWeilDivisor_mem_principalWeilDivisors (f : X.functionFieldˣ) :
    Scheme.principalWeilDivisor X f ∈ Prin(X) := by
  exact ⟨f, fun _ ↦ rfl⟩

/-- Definition 31.26.7: for a locally Noetherian integral scheme `X`, the Weil divisor class
group `Cl(X)` is the quotient of `Div(X)` by the subgroup of principal Weil divisors. -/
abbrev WeilDivisorClassGroup : Type (u + 1) :=
  Div(X) ⧸ Prin(X)

notation "Cl(" X ")" => WeilDivisorClassGroup X

/-- The canonical quotient homomorphism from Weil divisors to the divisor class group. -/
abbrev weilDivisorClassGroupMk : Div(X) →+ Cl(X) :=
  QuotientAddGroup.mk' (Prin(X))

/-- The quotient map `Div(X) → Cl(X)` is surjective. -/
theorem weilDivisorClassGroupMk_surjective :
    Function.Surjective (weilDivisorClassGroupMk X) := by
  simpa using (QuotientAddGroup.mk'_surjective (Prin(X)))

end

end AlgebraicGeometry
