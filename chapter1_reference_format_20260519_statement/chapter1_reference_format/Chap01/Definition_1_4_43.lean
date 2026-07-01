import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/- Definition 1.4.43: for a field `K`, an algebraic closure is an extension field `L` that is
algebraically closed and algebraic over `K`; mathlib's canonical notion for this is
`IsAlgClosure K L`. -/
#check IsAlgClosure K L

end
