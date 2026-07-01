import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Products

/- Remark 1.1.98: the pointwise ring operations on Cartesian products extend without change from
the earlier constructions to arbitrary rings. The owner declaration is `Pi.ring`; finite products
are the corresponding `Fintype`-indexed special case. -/
variable {ι : Type u} (A : ι → Type v) [∀ i, Ring (A i)]

#check (Pi.ring : Ring ((i : ι) → A i))

end Products

section BinaryProduct

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/- The Cartesian product of two rings is the binary specialization, with owner declaration
`Prod.instRing`. -/
#check (Prod.instRing : Ring (R × S))

end BinaryProduct
