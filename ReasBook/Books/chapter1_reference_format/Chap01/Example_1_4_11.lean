import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Module

universe u

noncomputable section

variable {K : Type u} [Field K]
variable (n : ℕ)

/- Example 1.4.11 (1): the coordinate space `K^n`, formalized as `Fin n → K`, has the canonical
standard basis `e₁, …, eₙ`, namely `Pi.basisFun K (Fin n)`. -/
#check (Pi.basisFun K (Fin n) : Basis (Fin n) K (Fin n → K))

/- Example 1.4.11 (2): the polynomial ring `K[X]` is an infinite-dimensional `K`-vector space, so
it is not finite-dimensional over `K`. -/
#check (show ¬ FiniteDimensional K K[X] from Polynomial.not_finite)

/- Example 1.4.11 (3): the monomials `1, X, X^2, ...` form the canonical basis of the
`K`-vector space `K[X]`. -/
#check (Polynomial.basisMonomials K : Basis ℕ K K[X])

/- Example 1.4.11 (4): if `f ∈ K[X]` has positive degree and `x` is the image of `X` in the
quotient `K[X] / (f)`, then `1, x, ..., x^(deg f - 1)` is the canonical power basis of that
quotient, formalized directly by `AdjoinRoot.powerBasis`. -/
#check
  (show (f : K[X]) → 0 < f.natDegree → PowerBasis K (AdjoinRoot f) from
    fun f hdeg ↦
      AdjoinRoot.powerBasis <| by
        intro hf
        simp [hf] at hdeg)

variable {f : K[X]} (hf : f ≠ 0)

/- The basis vectors of `AdjoinRoot.powerBasis hf` are the powers of `AdjoinRoot.root f`; this is
the existing derived API `PowerBasis.basis_eq_pow` for the canonical owner. -/
#check (AdjoinRoot.powerBasis hf).basis_eq_pow

end
