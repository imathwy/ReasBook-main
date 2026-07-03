import Nesterov.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace
open scoped Matrix.Norms.Frobenius

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 6.33 lies in the chapter's ambient matrix trace-power / Frobenius differential
domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the established
  Frobenius owner on `𝕊^n`;
- mathlib `Matrix.trace`, the canonical ambient owner of `X ↦ Trace (X^k)`;
- `RealSymmetricMatrixSpace.powerTrace` and `powerTrace_eq_frobeniusInner_one` in
  `Definition_6_42`, the source-facing symmetric-matrix owner and bridge to the canonical ambient
  trace expression.

Best owner abstraction:
- source-facing: the differentiability and derivative formulas for `π_k(X) = trace (X^k)` on the
  intrinsic symmetric-matrix carrier `𝕊^n`, written `π[k] X`;
- core/canonical: `fun X : Mat ↦ Matrix.trace (X ^ k)`;
- bridge/view: restriction of the ambient owner to `𝕊^n`, together with the Chapter 5 Frobenius
  owner `⟪·, ·⟫_F` and the ambient Frobenius sum for the second derivative.

Primitive data:
- `k : ℕ`
- `X H : 𝕊^n`

Derived API:
- the source-facing owner `π[k] X`
- the canonical symmetric-matrix power `X ^ k`
- the ambient trace pairing only for the second-derivative bridge expansion
- the derivative theorems below

This refinement keeps the theorem surface of this file on the source-facing symmetric-matrix
quantity `π[k] X` from `Definition_6_42`, while using the canonical ambient trace expression as the
core owner. -/

-- Proof sketch: `X ↦ Trace (X^k)` is a polynomial function in the matrix entries, hence smooth;
-- in particular it is twice Fréchet differentiable.
/-- Proposition 6.33: on the symmetric-matrix space `𝕊^n`, the trace-power map
`X ↦ Trace (X^k)` is twice Fréchet differentiable; the companion theorems below recover the
textbook Frobenius first- and second-derivative formulas for `π_k(X) = Trace (X^k)`. -/
theorem powerTrace_contDiff
    (k : ℕ) :
    ContDiff ℝ 2 (π[k] : SymmMat → ℝ) := sorry

-- Proof sketch: differentiate `t ↦ Trace ((X + tH)^k)` by the matrix product rule, use cyclicity
-- of the trace to collapse the resulting sum to `k Trace (H X^(k-1))`, and rewrite that trace as
-- the Frobenius pairing with `X^(k-1)`.
/-- On `𝕊^n`, the Fréchet derivative of `X ↦ Trace (X^k)` in the direction `H` is
`k ⟪X^(k-1), H⟫_F`. -/
theorem powerTrace_fderiv_eq_frobenius
    (k : ℕ) (X H : SymmMat) :
    fderiv ℝ (π[k] : SymmMat → ℝ) X H =
      (k : ℝ) * ⟪X ^ (k - 1), H⟫_F := sorry

-- Proof sketch: differentiate the first-derivative formula once more, expand the derivative of
-- each matrix power, reindex the double sum, and use symmetry plus cyclicity of the trace to
-- rewrite the quadratic form as the stated ambient trace-pairing sum.
/-- On `𝕊^n`, the second directional derivative of `X ↦ Trace (X^k)` is the ambient
trace/Frobenius sum `k ∑_{p=0}^{k-2} trace ((X^p H X^(k-2-p))ᵀ H)`. -/
theorem powerTrace_iteratedFDeriv_two_eq_frobenius_sum
    (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] =
      (k : ℝ) *
        (Finset.range (k - 1)).sum fun p ↦
          Matrix.trace
            (((((X ^ p : SymmMat) : Mat) * (H : Mat) *
                ((X ^ (k - 2 - p) : SymmMat) : Mat))ᵀ) * (H : Mat)) := sorry

end
