import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

namespace Polynomial

section

variable (P : K[X]) (a : L)

/- Definition 1.3.33: an element `a` of an extension field `L / K` is a root (zero) of a
polynomial `P ∈ K[X]` when the base change of `P` to `L[X]` has `a` as a root. -/
#check (P.map (algebraMap K L)).IsRoot a

end

/-- An element of an extension field is a root of `P` exactly when the polynomial evaluates to
zero at that element after scalar extension. -/
theorem isRoot_map_iff_aeval_eq_zero (P : K[X]) (a : L) :
    (P.map (algebraMap K L)).IsRoot a ↔ P.aeval a = 0 := by
  simp [Polynomial.IsRoot.def]

end Polynomial
