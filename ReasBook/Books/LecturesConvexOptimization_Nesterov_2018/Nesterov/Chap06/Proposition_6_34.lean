import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_42

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Proposition 6.34 lies in the chapter's symmetric-matrix trace-power / Hessian domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, in `Definition_6_42`, the
  source-facing trace-power owner on `𝕊^n`;
- mathlib `iteratedFDeriv`, the canonical Hessian quadratic-form owner for scalar-valued maps.

Best owner abstraction:
- source-facing: Proposition 6.34 as a Hessian estimate for the half-scaled even trace power on
  `𝕊^n`;
- core/canonical: `π[2 * (p : ℕ)] : SymmMat → ℝ` together with `iteratedFDeriv ℝ 2`;
- bridge/view: the coercion from `𝕊^n` to ambient matrices, under which `π[2 * (p : ℕ)] X =
  Trace (X^(2p))`.

Primitive data:
- `p : ℕ+`
- `X H : SymmMat`

Derived API:
- the half-scaled even trace-power map `X ↦ (1 / 2) π[2 * (p : ℕ)] X`;
- the Hessian quadratic form `iteratedFDeriv ℝ 2 ... X ![H, H]`.

This refinement deletes the duplicate raw-matrix functional and its ad hoc normed-space instances.
The proposition now lives directly on the chapter owner `𝕊^n` and uses the existing source-facing
trace-power owner `π[k]` instead of rebuilding `X ↦ Trace (X^k)` locally.
-/

-- Proof sketch: specialize the ambient Hessian expansion for the trace-power owner `π[2p]` to the
-- half-scaled map `X ↦ (1 / 2) π[2p] X`, then estimate the resulting quadratic form by
-- `(2p - 1) π[2p] H`.
/-- Proposition 6.34: for real symmetric matrices `X` and `H`, the Hessian quadratic form of the
half-scaled even trace-power map
`X ↦ (1 / 2) π[2p] X = (1 / 2) Trace (X^(2p))`,
represented by the second Fréchet derivative on the repeated direction pair `![H, H]`, is bounded
above by `(2p - 1) π[2p] H = (2p - 1) Trace (H^(2p))`. -/
theorem half_powerTrace_iteratedFDeriv_two_le
    (p : ℕ+) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ (1 / 2 : ℝ) * π[2 * (p : ℕ)] Y) X ![H, H] ≤
      (2 * (p : ℕ) - 1 : ℝ) * π[2 * (p : ℕ)] H := sorry
