import Mathlib
import Nesterov.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Proposition 7.11 lies in Chapter 7's positive-definite matrix-path / log-determinant potential
domain.

Sampled owner-style declarations:
- `logDetBarrierAmbient` and `logDetBarrier` in `Chap05/Definition_5_4_4_5`, the chapter owners
  for the ambient `-log det` formula and its intrinsic positive-definite barrier;
- `logDetBarrier_lineDeriv_eq_frobeniusInner` and its second-directional companion in
  `Chap05/Lemma_5_4_4_1`, the canonical derivative owners for the same matrix potential;
- `Matrix.PosDef`, the canonical matrix-level positivity owner used to justify the logarithmic
  domain.

Best owner abstraction:
- source-facing: the scalar path potential `V(α) = log (det G(0) / det G(α))`;
- core/canonical: the Chapter 5 ambient owner `logDetBarrierAmbient n`;
- bridge/view: the determinant-ratio formula and the trace identities obtained by differentiating
  along the scalar path.

Primitive data:
- the matrix path `G : ℝ → Mat`;
- the parameter family `τ : Fin n → ℝ`;
- positivity of `G α` near `α = 0`;
- differentiability of `G` and of its scalar derivative at `0`.

Derived API:
- the source-facing ratio potential;
- the Chapter 5 bridge expressing that potential as a difference of ambient `-log det` terms on
  the positive-definite locus;
- the first- and second-derivative identities at `α = 0`.

This refinement keeps the source-facing scalar potential, but removes the duplicate derivative
witness data `G₁`, `G₂` from the public theorem surface: the canonical derivatives are
`deriv G 0` and `deriv (deriv G) 0`, while the Chapter 5 barrier owner remains the core
matrix-level abstraction behind the formulas.
-/

/-- The logarithmic determinant-ratio potential
`V(α) = log (det G(0) / det G(α))` attached to a matrix path `G`. -/
def logDetRatioPotential
    (G : ℝ → Mat) (α : ℝ) : ℝ :=
  Real.log (Matrix.det (G 0) / Matrix.det (G α))

/-- Expanding `logDetRatioPotential G α` gives the determinant-ratio formula
`log (det G(0) / det G(α))`. -/
theorem logDetRatioPotential_def
    (G : ℝ → Mat) (α : ℝ) :
    logDetRatioPotential G α =
      Real.log (Matrix.det (G 0) / Matrix.det (G α)) := rfl

/- On the positive-definite locus, the source-facing determinant-ratio potential is the difference
of the Chapter 5 ambient barrier values at `G α` and `G 0`. -/
theorem logDetRatioPotential_eq_sub_logDetBarrierAmbient
    (G : ℝ → Mat) {α : ℝ} (hG0 : (G 0).PosDef) (hGα : (G α).PosDef) :
    logDetRatioPotential G α =
      logDetBarrierAmbient n
          (⟨G α, by
            rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hGα.isHermitian⟩ : SymmMat) -
        logDetBarrierAmbient n
          (⟨G 0, by
            rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hG0.isHermitian⟩ : SymmMat) := by
  rw [logDetRatioPotential, logDetBarrierAmbient_apply, logDetBarrierAmbient_apply,
    Real.log_div hG0.det_pos.ne' hGα.det_pos.ne']
  ring_nf

section

variable (G : ℝ → Mat) (τ : Fin n → ℝ)
variable (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
variable (hG₁ : DifferentiableAt ℝ G 0)
variable (hG₂ : DifferentiableAt ℝ (deriv G) 0)
variable (htrace₁ : Matrix.trace ((G 0)⁻¹ * deriv G 0) = ∑ i : Fin n, (τ i - 1))
variable
  (htrace₂ :
    Matrix.trace
        ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
      -∑ i : Fin n, (τ i - 1) ^ (2 : ℕ))

-- Proof sketch: differentiate `V(α) = log (det G(0) / det G(α))` using Jacobi's formula for
-- `det`, the derivative of matrix inversion, and the cyclicity of the trace; then substitute the
-- two assumed trace identities at `α = 0`.
/-- Proposition 7.11: if a matrix path `G` is twice differentiable at `0`, stays positive
definite near `0`, and its first and second trace identities are encoded by the parameters
`τ₁, …, τₙ`, then the determinant-ratio potential
`V(α) = log (det G(0) / det G(α))` satisfies the stated formulas for `V'(0)` and `V''(0)`. -/
theorem logDetRatioPotential_derivatives_at_zero
    :
    deriv (logDetRatioPotential G) 0 = (n : ℝ) - ∑ i : Fin n, τ i ∧
      iteratedDeriv 2 (logDetRatioPotential G) 0 =
        ∑ i : Fin n, (τ i - 1) ^ (2 : ℕ) := by
  sorry

-- Proof sketch: apply `logDetRatioPotential_derivatives_at_zero` to obtain the first derivative
-- identity, then rewrite the sum `∑ i, τ i` using the given identification with
-- `(\|g\|_D^*)^2`.
/-- If the sum of the parameters `τ₁, …, τₙ` is identified with `(\|g\|_D^*)^2`, then the first
derivative of the determinant-ratio potential is `n - (\|g\|_D^*)^2`. -/
theorem logDetRatioPotential_deriv_at_zero_of_dualNormSq
    (dualNormSq : ℝ) (hdualNormSq : dualNormSq = ∑ i : Fin n, τ i) :
    deriv (logDetRatioPotential G) 0 = (n : ℝ) - dualNormSq := by
  simpa [hdualNormSq] using
    (logDetRatioPotential_derivatives_at_zero G τ hpos hG₁ hG₂ htrace₁ htrace₂).1

end

end
