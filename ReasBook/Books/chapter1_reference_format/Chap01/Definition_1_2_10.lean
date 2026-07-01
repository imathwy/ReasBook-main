import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped NNReal

universe u v

section SourceFacing

variable (K : Type u) [Field K]

/- Definition 1.2.10: A norm on a field `K` is an absolute value `K → ℝ≥0`; a norm is
nonarchimedean when it satisfies the strong triangle inequality, and a normed field is a field
equipped with such a norm. -/
#check AbsoluteValue K ℝ≥0

/- The nonarchimedean condition is the canonical predicate `IsNonarchimedean`. -/
recall IsNonarchimedean {R : Type v} [LinearOrder R] {α : Type u} [Add α] (f : α → R) : Prop

/-- An absolute value on a field is nonarchimedean exactly when it satisfies
the strong triangle inequality. -/
theorem AbsoluteValue.isNonarchimedean_iff (v : AbsoluteValue K ℝ≥0) :
    IsNonarchimedean v ↔ ∀ x y : K, v (x + y) ≤ max (v x) (v y) :=
  Iff.rfl

end SourceFacing

section NormedFieldBridge

variable (K : Type u) [NormedField K]

/- The downstream owner for a field equipped with a norm is `NormedField`; its bundled absolute
value is `NormedField.toAbsoluteValue`. -/
#check (NormedField K)

recall NormedField.toAbsoluteValue (R : Type u) [NormedField R] : AbsoluteValue R ℝ

/-- The absolute value attached to a normed field is evaluation of the ambient norm. -/
theorem NormedField.toAbsoluteValue_apply (x : K) :
    NormedField.toAbsoluteValue K x = ‖x‖ :=
  rfl

end NormedFieldBridge

section AbsoluteValueBridge

variable {K : Type u} [Semiring K]

namespace AbsoluteValue

/-- The source-facing `ℝ≥0`-valued norm viewed as the real-valued absolute value required by
`AbsoluteValue.toNormedField`. -/
abbrev toReal (v : AbsoluteValue K ℝ≥0) : AbsoluteValue K ℝ where
  toFun x := (v x : ℝ)
  map_mul' x y := by
    simp [map_mul]
  nonneg' x := by
    exact_mod_cast v.nonneg x
  eq_zero' x := by
    simp
  add_le' x y := by
    exact_mod_cast v.add_le x y

/-- Evaluating `toReal` is just the canonical coercion `ℝ≥0 → ℝ`. -/
@[simp] theorem toReal_apply (v : AbsoluteValue K ℝ≥0) (x : K) :
    v.toReal x = v x :=
  rfl

end AbsoluteValue

end AbsoluteValueBridge

section ToNormedFieldBridge

variable {K : Type u} [Field K]

/- The downstream `NormedField` owner is obtained from the textbook `ℝ≥0`-valued norm by first
passing to the real-valued absolute value `AbsoluteValue.toReal`, then applying the canonical
mathlib construction `AbsoluteValue.toNormedField`. -/
recall AbsoluteValue.toNormedField {K : Type u} [Field K] (v : AbsoluteValue K ℝ) : NormedField K

/-- Converting an `ℝ≥0`-valued absolute value to `ℝ`, then to a normed field, recovers that
real-valued absolute value pointwise. -/
@[simp] theorem AbsoluteValue.toReal_toNormedField_toAbsoluteValue_apply
    (v : AbsoluteValue K ℝ≥0) (x : K) :
    letI := v.toReal.toNormedField
    NormedField.toAbsoluteValue K x = v.toReal x :=
  rfl

/-- The `NormedField` absolute value induced from an `ℝ≥0`-valued norm agrees with `toReal`
as a function. -/
theorem AbsoluteValue.toReal_toNormedField_toAbsoluteValue
    (v : AbsoluteValue K ℝ≥0) :
    letI := v.toReal.toNormedField
    (NormedField.toAbsoluteValue K : K → ℝ) = v.toReal := by
  funext x
  exact AbsoluteValue.toReal_toNormedField_toAbsoluteValue_apply v x

end ToNormedFieldBridge
