import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {K : Type u} [Field K]

/- Definition 1.2.12: two absolute values on a field are equivalent when they induce the same
topology; mathlib's canonical relation for this notion is `AbsoluteValue.IsEquiv`. -/
recall AbsoluteValue.IsEquiv {R : Type u} [Semiring R] {S : Type v} [Semiring S] [PartialOrder S]
  (v₁ v₂ : AbsoluteValue R S) : Prop

/- For real-valued absolute values, equivalence is exactly equality of the induced topology:
the canonical ring equivalence between the corresponding `WithAbs` topological fields is a
homeomorphism. -/
recall AbsoluteValue.isEquiv_iff_isHomeomorph (v₁ v₂ : AbsoluteValue K ℝ) :
  v₁.IsEquiv v₂ ↔ IsHomeomorph (WithAbs.congr v₁ v₂ (.refl K))
