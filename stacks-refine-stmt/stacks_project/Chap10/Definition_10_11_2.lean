import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section ModuleRelations

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [Fintype ι]

/- Definition 10.11.2: for a finite family `x : ι → M`, a relation is a coefficient family
`f : ι → R` whose associated linear combination of the `x i` is zero. The owner construction is
the canonical linear map `Fintype.linearCombination`. -/
recall Fintype.linearCombination

variable (x : ι → M) (f : ι → R)

/-- A coefficient family is a relation exactly when its explicit finite sum vanishes. -/
@[simp] theorem linearCombination_eq_zero_iff_sum_eq_zero :
    Fintype.linearCombination R x f = 0 ↔ ∑ i, f i • x i = 0 := by
  rw [Fintype.linearCombination_apply]

end ModuleRelations
