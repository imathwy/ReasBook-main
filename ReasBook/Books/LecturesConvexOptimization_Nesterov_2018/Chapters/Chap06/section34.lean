import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_34 (from Chap06) -/
noncomputable section

/- Definition 6.34 lies in Chapter 6's scalar smoothing-parameter domain.

Mandatory domain-style sampling before drafting:
- `switching_parameters` in `Chap06/Definition_6_35`, which keeps the source-facing Chapter 6
  scalar update data as an explicit owner rather than packaging it into a new framework;
- `excessive_gap_alpha` and `alternating_excessive_gap_step_size` in `Chap06/Definition_6_36`,
  which likewise expose the chapter's scalar parameter formulas directly;
- `scaled_smoothing_parameter_product_eq` in `Chap06/Proposition_6_28`, the downstream scalar
  identity that consumes exactly the formulas introduced here.

Best owner abstraction:
- source-facing: the ordered pair `(μ₁, μ₂)` of smoothness parameters;
- core/canonical: an explicit pair-valued scalar definition;
- bridge/view: the projection theorems recovering the displayed formulas for `μ₁` and `μ₂`.

Primitive data:
- the positive-source scalars `D₁`, `D₂`, `λ₁`, `λ₂`, and `‖A‖_{1,2}`;
- the displayed formulas for `μ₁` and `μ₂`.

Derived API:
- the first and second projection identities for the pair-valued owner.

The source formulas depend only on the scalar quantity `‖A‖_{1,2}`, not on the operator `A`
itself. Exposing the operator and ambient normed spaces here would therefore add public API noise
without changing the mathematical content of this definition.
-/

/-- Definition 6.34 [Chapter6_2.json:73]: the smoothness parameters are the pair
`(μ₁, μ₂)` defined by
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`. -/
def smoothness_parameters
    (D1 D2 opNorm12 lambda1 lambda2 : ℝ) : ℝ × ℝ :=
  ( lambda1 * opNorm12 * Real.sqrt (D2 / D1)
  , lambda2 * opNorm12 * Real.sqrt (D1 / D2) )

-- Proof sketch: unfold `smoothness_parameters`; the first projection of the defining pair is
-- exactly the displayed formula for `μ₁`.
/-- The first projection of `smoothness_parameters` is the parameter
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)`. -/
theorem smoothness_parameters_fst
    (D1 D2 opNorm12 lambda1 lambda2 : ℝ) :
    (smoothness_parameters D1 D2 opNorm12 lambda1 lambda2).1 =
      lambda1 * opNorm12 * Real.sqrt (D2 / D1) :=
  sorry

-- Proof sketch: unfold `smoothness_parameters`; the second projection of the defining pair is
-- exactly the displayed formula for `μ₂`.
/-- The second projection of `smoothness_parameters` is the parameter
`μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`. -/
theorem smoothness_parameters_snd
    (D1 D2 opNorm12 lambda1 lambda2 : ℝ) :
    (smoothness_parameters D1 D2 opNorm12 lambda1 lambda2).2 =
      lambda2 * opNorm12 * Real.sqrt (D1 / D2) :=
  sorry

end

/-! ### Proposition_6_34 (from Chap06) -/
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
