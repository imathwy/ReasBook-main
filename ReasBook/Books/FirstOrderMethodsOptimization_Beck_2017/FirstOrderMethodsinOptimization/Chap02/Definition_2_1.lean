import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}

/-- Definition 2.1: The effective domain of an extended real-valued function `f : E → EReal` is
the set of points where `f` takes a finite value, equivalently where `f x < ∞`. -/
def effective_domain (f : E → EReal) : Set E := {x | f x < ⊤}

-- Proof sketch: Unfold `effective_domain`; membership in the defining set is exactly the
-- inequality `f x < ⊤`.
/-- A point belongs to the effective domain exactly when the function value is strictly less than
`∞`. -/
@[simp] lemma mem_effective_domain {f : E → EReal} {x : E} :
    x ∈ effective_domain f ↔ f x < ⊤ :=
  Iff.rfl

end
