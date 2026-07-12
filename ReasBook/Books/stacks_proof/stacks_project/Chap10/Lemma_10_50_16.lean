import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Valuation

section

variable {K : Type u} [Field K]
variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

local instance : DecidableEq K := Classical.decEq K

/-- The nonarchimedean condition on a unit-group homomorphism, written in additive notation on
nonzero sums. -/
class IsNonarchimedeanUnitHom (v : Kˣ →* Multiplicative Γ) : Prop where
  map_add_ge_min :
    ∀ ⦃a b : K⦄, ∀ ha : a ≠ 0, ∀ hb : b ≠ 0, ∀ hab : a + b ≠ 0,
      min (Multiplicative.toAdd (v (Units.mk0 a ha)))
          (Multiplicative.toAdd (v (Units.mk0 b hb))) ≤
        Multiplicative.toAdd (v (Units.mk0 (a + b) hab))

-- The additive view of the owner map `v.rangeRestrict`.
private abbrev rangeRestrictToAdd (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    v.range.toAddSubgroup' :=
  v.rangeRestrict x

/-- The extension of a unit-group homomorphism to all of `K`, now landing in the exact image
group `Im(v)` and sending `0` to `⊤`. -/
private def unitHomValue (v : Kˣ →* Multiplicative Γ) (x : K) :
    WithTop (v.range.toAddSubgroup') :=
  if hx : x = 0 then ⊤ else
    (rangeRestrictToAdd v (Units.mk0 x hx) : WithTop (v.range.toAddSubgroup'))

-- Proof sketch: unfold `unitHomValue`; the `if` branch for `x = 0` is immediate.
omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem unitHomValue_zero (v : Kˣ →* Multiplicative Γ) :
    unitHomValue v 0 = ⊤ := by
  -- The zero branch of `unitHomValue` is definitionally `⊤`.
  simp [unitHomValue]

-- Proof sketch: unfold `unitHomValue` at `1`, note that `1 ≠ 0` in a field, and use that a group
-- homomorphism sends `1` to `1`, which corresponds to additive value `0`.
omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem unitHomValue_one (v : Kˣ →* Multiplicative Γ) :
    unitHomValue v 1 = 0 := by
  -- Move to the nonzero branch and identify the restricted value of `1` with the zero element.
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  unfold unitHomValue
  split_ifs with h
  · exact (h1 h).elim
  · have hzero : rangeRestrictToAdd v (Units.mk0 1 h) = 0 := by
      apply Subtype.ext
      change Multiplicative.toAdd (v (Units.mk0 1 h)) = 0
      rw [Units.mk0_one, map_one]
      rfl
    simpa using hzero

-- Proof sketch: split into the zero and nonzero cases for `a` and `b`; when both are nonzero,
-- rewrite through `Units.mk0` and use multiplicativity of the original homomorphism.
private theorem unitHomValue_mul (v : Kˣ →* Multiplicative Γ) :
    ∀ a b : K, unitHomValue v (a * b) = unitHomValue v a + unitHomValue v b := by
  intro a b
  -- The zero branches collapse immediately from the definition.
  by_cases ha : a = 0
  · simp [unitHomValue, ha]
  by_cases hb : b = 0
  · simp [unitHomValue, hb]
  -- In the nonzero branch, `Units.mk0_mul` matches the source multiplicativity exactly.
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hMul :
      unitHomValue v (a * b) =
        (rangeRestrictToAdd v (Units.mk0 (a * b) hab) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hab]
  have hA :
      unitHomValue v a =
        (rangeRestrictToAdd v (Units.mk0 a ha) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, ha]
  have hB :
      unitHomValue v b =
        (rangeRestrictToAdd v (Units.mk0 b hb) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hb]
  rw [hMul, hA, hB, ← WithTop.coe_add, WithTop.coe_eq_coe]
  -- The restricted value of a product is the sum of the restricted values in additive notation.
  apply Subtype.ext
  change
    Multiplicative.toAdd (v (Units.mk0 (a * b) hab)) =
      ↑(rangeRestrictToAdd v (Units.mk0 a ha) + rangeRestrictToAdd v (Units.mk0 b hb))
  rw [Units.mk0_mul _ _ hab, map_mul]
  rfl

-- Proof sketch: if one summand is zero, the claim reduces to the corresponding branch of
-- `unitHomValue`; otherwise apply the given minimum inequality on nonzero elements and coerce the
-- resulting inequality into `WithTop (v.range.toAddSubgroup')`.
omit [IsOrderedAddMonoid Γ] in
private theorem unitHomValue_add (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v) :
    ∀ a b : K, min (unitHomValue v a) (unitHomValue v b) ≤ unitHomValue v (a + b) := by
  intro a b
  -- If the sum vanishes, the target is `⊤` and the inequality is automatic.
  by_cases hab : a + b = 0
  · rw [hab, unitHomValue_zero]
    exact le_top
  by_cases ha : a = 0
  · subst a
    simp [unitHomValue]
  by_cases hb : b = 0
  · subst b
    simp [unitHomValue]
  -- In the fully nonzero branch, transport the given inequality into `WithTop`.
  have hA :
      unitHomValue v a =
        (rangeRestrictToAdd v (Units.mk0 a ha) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, ha]
  have hB :
      unitHomValue v b =
        (rangeRestrictToAdd v (Units.mk0 b hb) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hb]
  have hAB :
      unitHomValue v (a + b) =
        (rangeRestrictToAdd v (Units.mk0 (a + b) hab) : WithTop (v.range.toAddSubgroup')) := by
    simp [unitHomValue, hab]
  rw [hA, hB, hAB, ← WithTop.coe_min, WithTop.coe_le_coe]
  -- After removing the `WithTop` coercions, this is exactly the given nonarchimedean inequality.
  change
    min (Multiplicative.toAdd (v (Units.mk0 a ha))) (Multiplicative.toAdd (v (Units.mk0 b hb))) ≤
      Multiplicative.toAdd (v (Units.mk0 (a + b) hab))
  simpa [rangeRestrictToAdd] using hv.map_add_ge_min (a := a) (b := b) ha hb hab

end

section

variable {K : Type u} [Field K]
variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The canonical additive valuation attached to a nonarchimedean unit-group homomorphism, valued
in the exact image group `Im(v)`. -/
def addValuationOfUnitHom (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v) :
    AddValuation K (WithTop (v.range.toAddSubgroup')) :=
  AddValuation.of (unitHomValue v) (unitHomValue_zero v) (unitHomValue_one v)
    (unitHomValue_add v hv) (unitHomValue_mul v)

/-- The source-facing valuation subring `A` attached to `v`. -/
def valuationSubringOfUnitHom (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v) :
    ValuationSubring K :=
  (addValuationOfUnitHom v hv).toValuation.valuationSubring

variable (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanUnitHom v)

/-- On nonzero elements, `addValuationOfUnitHom v` is exactly the original unit-group
homomorphism, with codomain restricted to the exact image subgroup. -/
@[simp] theorem addValuationOfUnitHom_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    addValuationOfUnitHom v hv x =
      (rangeRestrictToAdd v (Units.mk0 x hx) : WithTop (v.range.toAddSubgroup')) := by
  simp [addValuationOfUnitHom, unitHomValue, hx]

/-- On units, `addValuationOfUnitHom v` lands in the exact image subgroup `Im(v)`. -/
@[simp] theorem addValuationOfUnitHom_apply_unit (x : Kˣ) :
    addValuationOfUnitHom v hv x = (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) := by
  simp [addValuationOfUnitHom, unitHomValue, x.ne_zero]

/-- Lemma 10.50.16 (Tag 00IG): the induced additive valuation has exact value group `Im(v)`;
equivalently, every element of `Im(v)` is the value of some unit of `K`. -/
@[stacks 00IG]
theorem addValuationOfUnitHom_surjective_on_valueGroup (γ : v.range.toAddSubgroup') :
    ∃ x : Kˣ, addValuationOfUnitHom v hv x = (γ : WithTop (v.range.toAddSubgroup')) := by
  rcases v.rangeRestrict_surjective γ with ⟨x, rfl⟩
  exact ⟨x, addValuationOfUnitHom_apply_unit v hv x⟩

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem rangeRestrict_eq_zero_iff (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    ((rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) = 0) ↔
      Multiplicative.toAdd (v x) = 0 := by
  constructor
  · intro hx
    have hx' : rangeRestrictToAdd v x = 0 := by
      simpa using hx
    exact congrArg Subtype.val hx'
  · intro hx
    have hx' : rangeRestrictToAdd v x = 0 := by
      ext
      exact hx
    simpa using hx'

omit [IsOrderedAddMonoid Γ] in
private theorem rangeRestrict_nonneg_iff (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    0 ≤ (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) ↔
      0 ≤ Multiplicative.toAdd (v x) := by
  change
    (((0 : v.range.toAddSubgroup') : WithTop (v.range.toAddSubgroup')) ≤
        (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup'))) ↔
      0 ≤ Multiplicative.toAdd (v x)
  rw [WithTop.coe_le_coe]
  rfl

omit [IsOrderedAddMonoid Γ] in
private theorem rangeRestrict_pos_iff (v : Kˣ →* Multiplicative Γ) (x : Kˣ) :
    0 < (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup')) ↔
      0 < Multiplicative.toAdd (v x) := by
  change
    (((0 : v.range.toAddSubgroup') : WithTop (v.range.toAddSubgroup')) <
        (rangeRestrictToAdd v x : WithTop (v.range.toAddSubgroup'))) ↔
      0 < Multiplicative.toAdd (v x)
  rw [WithTop.coe_lt_coe]
  rfl

/-- Lemma 10.50.16 (Tag 00IG): the valuation subring attached to `v` is exactly the set of elements whose
induced additive value in `Im(v)` is nonnegative. This is the canonical library-facing form of the
source description `A = {x ∈ K | x = 0 or v(x) ≥ 0}`. -/
@[stacks 00IG]
theorem mem_valuationSubringOfUnitHom_iff (x : K) :
    x ∈ valuationSubringOfUnitHom v hv ↔ 0 ≤ addValuationOfUnitHom v hv x := by
  rw [valuationSubringOfUnitHom, Valuation.mem_valuationSubring_iff]
  simpa [AddValuation.toValuation_apply] using
    (Multiplicative.ofAdd_le :
      Multiplicative.ofAdd (OrderDual.toDual (addValuationOfUnitHom v hv x)) ≤ 1 ↔
        OrderDual.toDual (addValuationOfUnitHom v hv x) ≤ 0)

/-- On nonzero elements, membership in the valuation subring is exactly nonnegativity of the
original homomorphism `v`. -/
theorem mem_valuationSubringOfUnitHom_iff_of_ne_zero {x : K} (hx : x ≠ 0) :
    x ∈ valuationSubringOfUnitHom v hv ↔ 0 ≤ Multiplicative.toAdd (v (Units.mk0 x hx)) := by
  rw [mem_valuationSubringOfUnitHom_iff, addValuationOfUnitHom_apply_of_ne_zero v hv hx]
  exact rangeRestrict_nonneg_iff v (Units.mk0 x hx)

/-- Lemma 10.50.16 (Tag 00IG): the source-facing description of `A`, written directly in terms of
the original unit-group homomorphism `v`. The universal quantifier only supplies the implicit proof
that a nonzero element of `K` defines a unit. -/
@[stacks 00IG]
theorem mem_valuationSubringOfUnitHom_iff_eq_zero_or_nonneg (x : K) :
    x ∈ valuationSubringOfUnitHom v hv ↔
      x = 0 ∨ ∀ hx : x ≠ 0, 0 ≤ Multiplicative.toAdd (v (Units.mk0 x hx)) := by
  constructor
  · intro hxA
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr fun hx' ↦ (mem_valuationSubringOfUnitHom_iff_of_ne_zero v hv hx').mp hxA
  · rintro (rfl | hx)
    · rw [mem_valuationSubringOfUnitHom_iff]
      simp
    · by_cases hx0 : x = 0
      · rw [hx0, mem_valuationSubringOfUnitHom_iff]
        simp
      · exact (mem_valuationSubringOfUnitHom_iff_of_ne_zero v hv hx0).mpr (hx hx0)

/-- Lemma 10.50.16 (Tag 00IG): elements of the maximal ideal are exactly those with strictly
positive extended value. -/
@[stacks 00IG]
theorem mem_maximalIdeal_valuationSubringOfUnitHom_iff {a : valuationSubringOfUnitHom v hv} :
    a ∈ IsLocalRing.maximalIdeal (valuationSubringOfUnitHom v hv) ↔
      0 < addValuationOfUnitHom v hv a := by
  simpa [valuationSubringOfUnitHom, AddValuation.toValuation_apply] using
    (((addValuationOfUnitHom v hv).toValuation).mem_maximalIdeal_iff :
      a ∈ IsLocalRing.maximalIdeal (((addValuationOfUnitHom v hv).toValuation).valuationSubring) ↔
        ((addValuationOfUnitHom v hv).toValuation) a < 1)

/-- On nonzero elements of the valuation subring, maximal-ideal membership is exactly positivity
of the original homomorphism `v`. -/
theorem mem_maximalIdeal_valuationSubringOfUnitHom_iff_of_ne_zero
    {a : valuationSubringOfUnitHom v hv} (ha : (a : K) ≠ 0) :
    a ∈ IsLocalRing.maximalIdeal (valuationSubringOfUnitHom v hv) ↔
      0 < Multiplicative.toAdd (v (Units.mk0 (a : K) ha)) := by
  rw [mem_maximalIdeal_valuationSubringOfUnitHom_iff, addValuationOfUnitHom_apply_of_ne_zero v hv ha]
  exact rangeRestrict_pos_iff v (Units.mk0 (a : K) ha)

/-- Lemma 10.50.16 (Tag 00IG): the source-facing description of the maximal ideal, written
directly in terms of the original unit-group homomorphism `v`. -/
@[stacks 00IG]
theorem mem_maximalIdeal_valuationSubringOfUnitHom_iff_eq_zero_or_pos
    {a : valuationSubringOfUnitHom v hv} :
    a ∈ IsLocalRing.maximalIdeal (valuationSubringOfUnitHom v hv) ↔
      (a : K) = 0 ∨ ∀ ha : (a : K) ≠ 0, 0 < Multiplicative.toAdd (v (Units.mk0 (a : K) ha)) := by
  constructor
  · intro ha
    by_cases h0 : (a : K) = 0
    · exact Or.inl h0
    · exact Or.inr fun ha' ↦
        (mem_maximalIdeal_valuationSubringOfUnitHom_iff_of_ne_zero v hv ha').mp ha
  · intro ha'
    rcases ha' with h0 | ha
    · have : a = 0 := Subtype.ext h0
      cases this
      simp
    · by_cases h0 : (a : K) = 0
      · have : a = 0 := Subtype.ext h0
        cases this
        simp
      · exact (mem_maximalIdeal_valuationSubringOfUnitHom_iff_of_ne_zero v hv h0).mpr (ha h0)

/-- Lemma 10.50.16 (Tag 00IG): units in the valuation subring are exactly the nonzero elements
with value `0`. -/
@[stacks 00IG]
theorem mem_unitGroup_valuationSubringOfUnitHom_iff (x : Kˣ) :
    x ∈ (valuationSubringOfUnitHom v hv).unitGroup ↔ Multiplicative.toAdd (v x) = 0 := by
  rw [show x ∈ (valuationSubringOfUnitHom v hv).unitGroup ↔ addValuationOfUnitHom v hv x = 0 by
    simpa [valuationSubringOfUnitHom, AddValuation.toValuation_apply] using
      Valuation.mem_unitGroup_iff K ((addValuationOfUnitHom v hv).toValuation) x]
  rw [addValuationOfUnitHom_apply_unit v hv x]
  simpa [Units.mk0_val] using rangeRestrict_eq_zero_iff v x

end
