import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

universe u

section

variable {K : Type u} [Field K]

/- Theorem 1.4.37: for a nonzero polynomial `P`, the quotient `K[X] / (P)`, formalized by
`AdjoinRoot P`, carries the canonical power basis `1, x, x^2, ..., x^(P.natDegree - 1)`, where
`x` is the class of `X` in the quotient. The owner abstraction is `AdjoinRoot.powerBasis`; the
pointwise description of its basis vectors is the derived API `PowerBasis.basis_eq_pow`. -/
recall AdjoinRoot.powerBasis (P : K[X]) (hP : P ≠ 0) : PowerBasis K (AdjoinRoot P)

/- The basis vectors of the canonical owner are exactly the powers of `AdjoinRoot.root P`. -/
#check
  (show ∀ (P : K[X]) (hP : P ≠ 0) (i : Fin P.natDegree),
      (AdjoinRoot.powerBasis hP).basis i = AdjoinRoot.root P ^ (i : ℕ) from
    fun _ hP i ↦ (AdjoinRoot.powerBasis hP).basis_eq_pow i)

/- The source-facing quotient-dimension statement keeps the textbook hypothesis `P ≠ 0`. The
stronger theorem `finrank_quotient_span_eq_natDegree` is used only behind this faithful interface,
since its `P = 0` case is a Lean-specific `Module.finrank` artifact rather than textbook content. -/
#check
  (show ∀ (P : K[X]) (_ : P ≠ 0),
      Module.finrank K (K[X] ⧸ Ideal.span {P}) = P.natDegree from
    fun _ _ ↦ finrank_quotient_span_eq_natDegree)

end
