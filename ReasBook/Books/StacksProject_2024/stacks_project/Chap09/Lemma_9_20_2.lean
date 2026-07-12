import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField
open Module

universe u v

namespace Algebra

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Lemma 9.20.2:
- `source-facing`: the characteristic polynomial of multiplication by `α` on a finite extension
  `L/K`
- `core/canonical`: `Algebra.lmul K L α` is the primitive endomorphism, and
  `IntermediateField.adjoin.finrank` owns the simple-extension degree
- `bridge/view`: `Matrix.charpoly_leftMulMatrix` computes the simple-extension `charpoly`, while
  `Module.finrank_mul_finrank` supplies the textbook exponent

Primitive data is the pair `(Algebra.lmul K L α, minpoly K α)`. The degree formula below is
derived API, so the displayed exponent should be proved directly from the existing owner theorems
instead of being treated as an independent local wheel.
-/

/-- Lemma 9.20.2: for a finite field extension `L/K`, the characteristic polynomial of the
`K`-linear endomorphism of `L` given by multiplication by `α` is the minimal polynomial of `α`
over `K` raised to the power `[L : K(α)]`. This is the canonical Lean form of the textbook
statement that the characteristic polynomial is `P ^ e` with
`e * deg(P) = [L : K]`. -/
-- Proof sketch: choose a `K(α)`-basis of `L`, use the induced `K`-basis from `Basis.smulTower`,
-- identify the resulting matrix of `Algebra.lmul K L α` with a block diagonal matrix whose blocks
-- are the simple-extension left-multiplication matrix, and then combine
-- `Matrix.charpoly_leftMulMatrix` with the tower-law exponent
-- `finrank K⟮α⟯ L * (minpoly K α).natDegree = finrank K L`.
theorem charpoly_lmul_eq_minpoly_pow_finrank_adjoin (α : L) :
    (lmul K L α).charpoly = (minpoly K α) ^ finrank K⟮α⟯ L := sorry

end Algebra
