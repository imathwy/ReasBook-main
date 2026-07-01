import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {K : Type u} [Field K]

/- Theorem 1.4.44: every field admits an algebraic closure; in mathlib, the canonical witness is
`AlgebraicClosure K`, and the corresponding instance gives `IsAlgClosure K (AlgebraicClosure K)`.
-/
#check (inferInstance : IsAlgClosure K (AlgebraicClosure K))

end
