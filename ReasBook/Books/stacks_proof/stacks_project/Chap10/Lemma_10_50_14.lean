import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Valuation

noncomputable section

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

local notation "K[" A "]" => FractionRing A
local notation "Γ₀[" A "]" => ValuationRing.ValueGroup A (K[A])
local notation "Γ[" A "]" => (Γ₀[A])ˣ
local notation "v[" A "]" => ValuationRing.valuation A (FractionRing A)
local notation "va[" A "]" => Valuation.toAddValuation (v[A])
local notation "ι[" A "]" => algebraMap A (FractionRing A)

private theorem valuationRingValuation_ne_zero (a : { a : A // a ≠ 0 }) :
    v[A] (ι[A] (a : A)) ≠ 0 := by
  rw [Valuation.ne_zero_iff]
  exact (map_ne_zero_iff ι[A] (IsFractionRing.injective A K[A])).2 a.2

/-- The textbook valuation `v : A - \{0\} → Γ` attached to a valuation ring `A`, where
`Γ = (ValuationRing.ValueGroup A (FractionRing A))ˣ` is the source-facing value group from
Definition 10.50.13. This is the restriction of the canonical owner valuation
`ValuationRing.valuation A (FractionRing A)` to nonzero elements of `A`, with the zero value
excluded by passing to units. -/
def valuationRingNonzeroValuation (a : { a : A // a ≠ 0 }) : Γ[A] :=
  Units.mk0 (v[A] (ι[A] (a : A))) (valuationRingValuation_ne_zero A a)

@[simp] theorem valuationRingNonzeroValuation_coe (a : { a : A // a ≠ 0 }) :
    ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) = v[A] (ι[A] (a : A)) := by
  simp [valuationRingNonzeroValuation]

@[simp] theorem valuationRingNonzeroValuation_le_one (a : { a : A // a ≠ 0 }) :
    ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) ≤ 1 := by
  rw [valuationRingNonzeroValuation_coe]
  exact (ValuationRing.mem_integer_iff A K[A] (ι[A] (a : A))).2 ⟨(a : A), rfl⟩

@[simp] theorem valuationRingNonzeroValuation_toAdd (a : { a : A // a ≠ 0 }) :
    OrderDual.toDual (Additive.ofMul (((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]))) =
      va[A] (ι[A] (a : A)) := by
  simp [Valuation.toAddValuation_apply, valuationRingNonzeroValuation_coe]

/-- The source-facing cone condition in additive normalization: nonzero elements of a valuation
ring have nonnegative value. This is the textbook codomain restriction
`v : A \ {0} → Γ_{\ge 0}` expressed through the owner additive valuation. -/
theorem valuationRingNonzeroValuation_toAdd_nonneg (a : { a : A // a ≠ 0 }) :
    0 ≤ va[A] (ι[A] (a : A)) := by
  rw [← valuationRingNonzeroValuation_toAdd]
  simpa using valuationRingNonzeroValuation_le_one A a

-- Proof sketch: identify `A` with the integer ring of its associated valuation and transport the
-- standard criterion that valuation `1` is equivalent to being a unit.
/-- Lemma 10.50.14 (1): for a nonzero element of `A`, the associated valuation is `1` exactly when
it is a unit. -/
@[stacks 00IF]
theorem valuationRingNonzeroValuation_eq_one_iff_isUnit (a : { a : A // a ≠ 0 }) :
    valuationRingNonzeroValuation A a = 1 ↔ IsUnit (a : A) := by
  let x : (ValuationRing.valuation A K[A]).integer := ValuationRing.equivInteger A K[A] (a : A)
  have hx : v[A] (algebraMap (ValuationRing.valuation A K[A]).integer K[A] x) = 1 ↔ IsUnit x :=
    ((Valuation.integer.integers (v[A])).isUnit_iff_valuation_eq_one).symm
  have hx' : ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) = 1 ↔ IsUnit (a : A) := by
    simpa [x, ValuationRing.coe_equivInteger_apply, valuationRingNonzeroValuation_coe] using hx
  constructor
  · intro h
    have hcoe : ((valuationRingNonzeroValuation A a : Γ[A]) : Γ₀[A]) = 1 := by
      rw [h]
      simp
    exact hx'.1 hcoe
  · intro h
    apply Units.ext
    exact hx'.2 h

/-- Lemma 10.50.14 (2): the associated valuation is multiplicative on products of nonzero
elements. -/
@[stacks 00IF]
theorem valuationRingNonzeroValuation_mul (a b : { a : A // a ≠ 0 }) :
    valuationRingNonzeroValuation A ⟨(a : A) * (b : A), mul_ne_zero a.2 b.2⟩ =
      valuationRingNonzeroValuation A a * valuationRingNonzeroValuation A b := by
  apply Units.ext
  simp [valuationRingNonzeroValuation_coe]

/-- Lemma 10.50.14 (3): for nonzero `a`, `b`, and `a + b`, the associated valuation satisfies the
ultrametric inequality in multiplicative normalization. -/
@[stacks 00IF]
theorem valuationRingNonzeroValuation_add_le_max
    (a b : { a : A // a ≠ 0 }) (hab : (a : A) + (b : A) ≠ 0) :
    valuationRingNonzeroValuation A ⟨(a : A) + (b : A), hab⟩ ≤
      max (valuationRingNonzeroValuation A a) (valuationRingNonzeroValuation A b) := by
  rw [← Units.val_le_val]
  simp [valuationRingNonzeroValuation_coe]

end
