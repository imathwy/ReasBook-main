import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Definition 2.6: an extended-real-valued function is convex when its real epigraph
is a convex subset of `E × ℝ`. -/
def is_convex_function (f : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- The predicate `is_convex_function` is equivalent to convexity of the real epigraph
`{(x, r) | f x ≤ r}`. -/
@[simp]
lemma is_convex_function_iff_convex_real_epigraph (f : E → EReal) :
    is_convex_function f ↔ Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
  Iff.rfl

end
