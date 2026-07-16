import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_6_7
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_4_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.7 lies in the chapter's composed third-order directional-differentiation domain.

Sampled owner declarations:
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for scalar repeated
  third directional derivatives;
* `vectorThirdDirectionalDerivative` from `Definition_5_4_6_2`, the chapter owner for
  `D³ξ(x)[d, d, d]`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical owner for the mixed second-order term;
* `compositionPotential` from `Definition_5_4_6_6` together with
  `compositionSecondLiftedDirectionDerivative` from `Definition_5_4_6_7`, the subsection's
  source-facing composition owners.

Source/core/bridge triage:
* source-facing: the decomposition `(5.4.25)` for the third directional derivative of
  `ψ(x, z) = Φ(ξ(x), z)`;
* core/canonical: `thirdDirectionalDerivative`, `hessian`, and
  `vectorThirdDirectionalDerivative`;
* bridge/view: the canonical lifted pair `(fderiv ℝ ξ x d, 0)` and
  `compositionSecondLiftedDirectionDerivative`.

Primitive data:
* `Φ`, `ξ`, `x`, `z`, `d`.

Derived API:
* the third directional derivative of the fixed-`z` composition;
* the lifted direction `l = (Dξ(x)[d], 0)`;
* the derivative `l' = Dl(x)[d]`;
* the gradient pairing with `D³ξ(x)[d, d, d]`.

The theorem surface should therefore use the existing owner vocabulary for all three summands:
`thirdDirectionalDerivative Φ (ξ x, z) l`, the mixed Hessian pairing with the lifted derivative
`compositionSecondLiftedDirectionDerivative ξ x d`, and the final pairing with
`vectorThirdDirectionalDerivative ξ x d`, instead of exposing parallel raw `iteratedFDeriv` and
raw `fderiv` spellings. -/

-- Proof sketch: differentiate the second-derivative decomposition from
-- `compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo` once more along the
-- repeated direction `d`. The chain rule gives the third derivative of `Φ` in the lifted
-- direction `l = (Dξ(x)[d], 0)`, differentiating the Hessian quadratic form contributes the
-- coefficient `3` in front of the mixed Hessian pairing with `l' = (D²ξ(x)[d, d], 0)`, and the
-- remaining term is the pairing of the `y`-gradient of `Φ` with `D³ξ(x)[d, d, d]`.
/-- Theorem 5.4.6.7: the third directional derivative `Δ₃ = D³ψ(x, z)[d, d, d]` of
`ψ(x, z) = Φ(ξ(x), z)` is the sum of the third derivative of `Φ` in the lifted direction
`l = (Dξ(x)[d], 0)`, three times the mixed Hessian pairing with
`l' = (D²ξ(x)[d, d], 0)`, and the pairing of `∇ᵧ Φ(ξ(x), z)` with `D³ξ(x)[d, d, d]`. -/
theorem compositionPotential_thirdDirectionalDerivative_eq
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x)
    (hΦ : ContDiffAt ℝ 3 Φ (ξ x, z)) :
    let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0);
    thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
      thirdDirectionalDerivative Φ (ξ x, z) l +
        (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
          (compositionSecondLiftedDirectionDerivative ξ x d) +
        inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
          (vectorThirdDirectionalDerivative ξ x d) := sorry

end
