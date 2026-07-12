import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [MulOneClass R]

/- Definition 10.9.1 (Tag 00CN) is recalled canonically by `Submonoid R`: a multiplicative subset
of `R` is exactly a subset containing `1` and closed under multiplication. -/
recall Submonoid

/- Primitive data of the owner structure are its carrier together with `one_mem'` and `mul_mem'`.
Downstream API should use the canonical coercion to `Set R` and the derived theorems below. -/
#check (SetLike.coe : Submonoid R → Set R)

/- Companion recall: the textbook condition `1 ∈ S` is the canonical theorem `Submonoid.one_mem`. -/
recall Submonoid.one_mem

/- Companion recall: the textbook closure condition is the canonical theorem `Submonoid.mul_mem`. -/
recall Submonoid.mul_mem

end
