import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_10
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_6_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Theorem 5.4.6.5 lies in the chapter's composed directional-differentiation domain.

Sampled owner declarations:
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for scalar second
  directional derivatives;
* `vectorSecondDirectionalDerivative` from `Definition_5_4_6_2`, the chapter owner for
  `D²ξ(x)[d, d]`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical Hessian owner;
* `compositionPotential` from `Definition_5_4_6_6`, the source-facing owner for
  `ψ(x, z) = Φ(ξ(x), z)`.

Source/core/bridge triage:
* source-facing: the decomposition `Δ₂ = σ₁ + σ₂` for `ψ(x, z) = Φ(ξ(x), z)`;
* core/canonical: `secondDirectionalDerivative`, `vectorSecondDirectionalDerivative`, and
  `hessian`;
* bridge/view: the fixed-`z` slice `fun x' ↦ compositionPotential Φ ξ (x', z)` together with the
  canonical lifted pair `(fderiv ℝ ξ x d, 0)`.

Primitive data:
* `Φ`, `ξ`, `x`, `z`, `d`.

Derived API:
* the Hessian term `compositionPotentialSigmaOne`;
* the mixed term `compositionPotentialSigmaTwo`.

The previous raw `iteratedFDeriv` duplicate for `Δ₂` is deleted in favor of the chapter owner
`secondDirectionalDerivative`, and the mixed term now reuses
`vectorSecondDirectionalDerivative` instead of repeating its defining formula. -/

section SigmaOne

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable [NormedAddCommGroup E₃]
variable [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/-- The Hessian quadratic term `σ₁ = ⟪∇² Φ(ξ(x), z) l, l⟫` in the decomposition of `Δ₂`. -/
abbrev compositionPotentialSigmaOne
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) : ℝ :=
  let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0)
  inner ℝ l (hessian Φ (ξ x, z) l)

-- Proof sketch: unfold `compositionPotentialSigmaOne`.
/-- Expanding `compositionPotentialSigmaOne Φ ξ x z d` gives the Hessian quadratic form of `Φ`
at `(ξ(x), z)` in the lifted direction `l = (Dξ(x)[d], 0)`. -/
theorem compositionPotentialSigmaOne_def
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) :
    compositionPotentialSigmaOne Φ ξ x z d =
      inner ℝ (fderiv ℝ ξ x d, (0 : E₃))
        (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃))) :=
  rfl

end SigmaOne

section SigmaTwo

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- The mixed term `σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫` in the decomposition of `Δ₂`. -/
abbrev compositionPotentialSigmaTwo
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) : ℝ :=
  inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
    (vectorSecondDirectionalDerivative ξ x d)

-- Proof sketch: unfold `compositionPotentialSigmaTwo`.
/-- Expanding `compositionPotentialSigmaTwo Φ ξ x z d` gives the pairing of the `y`-gradient of
`Φ` with the second directional derivative `D²ξ(x)[d, d]`. -/
theorem compositionPotentialSigmaTwo_def
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) :
    compositionPotentialSigmaTwo Φ ξ x z d =
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorSecondDirectionalDerivative ξ x d) :=
  rfl

end SigmaTwo

section MainTheorem

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
variable [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

-- Proof sketch: differentiate the fixed-`z` slice `x' ↦ compositionPotential Φ ξ (x', z)` along
-- the repeated direction `d`. The chain rule produces the Hessian quadratic term in the lifted
-- direction `l = (Dξ(x)[d], 0)`, and differentiating `l` contributes the pairing of the
-- `y`-gradient of `Φ` with `D²ξ(x)[d, d]`; the `z`-component contributes nothing because it is
-- constantly zero.
/-- Theorem 5.4.6.5: for `ψ(x, z) = Φ(ξ(x), z)`, if
`Δ₂ = D² (fun x' ↦ compositionPotential Φ ξ (x', z))(x)[d, d]`,
`σ₁ = ⟪∇² Φ(ξ(x), z) l, l⟫` with `l = (Dξ(x)[d], 0)`,
and `σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫`,
then the decomposition `(5.4.24)` reads `Δ₂ = σ₁ + σ₂`. -/
theorem compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 2 ξ x)
    (hψ : ContDiffAt ℝ 2 (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x) :
    secondDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
      compositionPotentialSigmaOne Φ ξ x z d +
        compositionPotentialSigmaTwo Φ ξ x z d := sorry

end MainTheorem

end
