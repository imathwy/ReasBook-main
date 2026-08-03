universe u v

/-- A family is `0/1`-valued when each coordinate is equal to `0` or `1`. -/
def is_zero_one_family {ι : Type u} {α : Type v} [Zero α] [One α] (x : ι → α) : Prop :=
  ∀ i, x i = 0 ∨ x i = 1

/-- Membership in `is_zero_one_family x` is exactly the coordinatewise `0/1` condition. -/
theorem is_zero_one_family_iff {ι : Type u} {α : Type v} [Zero α] [One α] {x : ι → α} :
    is_zero_one_family x ↔ ∀ i, x i = 0 ∨ x i = 1 :=
  Iff.rfl

namespace is_zero_one_family

/-- A `0/1`-valued family takes only the values `0` and `1`. -/
theorem apply {ι : Type u} {α : Type v} [Zero α] [One α] {x : ι → α}
    (hx : is_zero_one_family x) (i : ι) :
    x i = 0 ∨ x i = 1 :=
  hx i

end is_zero_one_family
