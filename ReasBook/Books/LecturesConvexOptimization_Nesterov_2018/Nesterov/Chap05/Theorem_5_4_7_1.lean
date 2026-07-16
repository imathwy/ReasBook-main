import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_10
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PowerConeGeometricMean

/- Theorem 5.4.7.1 lies in the Chapter 5 power-cone / directional-derivative domain.

Sampled owner declarations:
* `powerConeGeometricMean` from `Definition_5_4_7_1`, the source-facing owner for the weighted
  geometric mean `ξ(x) = (x^(1))^α (x^(2))^(1 - α)`;
* mathlib `lineDeriv`, the canonical first directional-derivative owner;
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for
  `D²f(x)[h,h]`;
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for
  `D³f(x)[h,h,h]`.

Source/core/bridge triage:
* source-facing: the explicit directional-derivative formulas for the weighted geometric mean;
* core/canonical: `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`
  applied to `powerConeGeometricMean α`;
* bridge/view: no extra wrapper beyond those direct owner specializations.

Primitive data:
* the exponent `α`;
* the base point `x` and direction `h`;
* positivity of the two coordinates of `x`.

Derived API:
* the explicit first-, second-, and third-directional-derivative identities below.

The file therefore keeps the source-facing formulas but states them directly on the canonical
directional-derivative owners already fixed earlier in the chapter, rather than introducing a
parallel local slice-level API.
-/

section

variable {α : ℝ} {x h : ℝ × ℝ}

local notation "ξ" => ξ[α]

-- Proof sketch: differentiate the directional slice
-- `t ↦ ξ (x + t • h)` at `t = 0`, use the positive coordinate assumptions to identify the
-- derivatives of the two `Real.rpow` factors, and factor out `ξ x`.
/-- Theorem 5.4.7.1 (1): the first directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`Dξ(x)[h] = [α (h^(1) / x^(1)) + (1 - α) (h^(2) / x^(2))] ξ(x)`. -/
theorem powerConeGeometricMean_firstDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    lineDeriv ℝ ξ x h =
      (α * (h.1 / x.1) + (1 - α) * (h.2 / x.2)) * ξ x := sorry

-- Proof sketch: differentiate the first-derivative identity once more along the same direction
-- `h`; the derivative of `h.1 / x.1` contributes `-(h.1 / x.1)^2` and similarly for the second
-- coordinate, after which the algebra simplifies to
-- `-α (1 - α) ((h.1 / x.1) - (h.2 / x.2))^2 ξ(x)`.
/-- Theorem 5.4.7.1 (2): the second directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`D²ξ(x)[h,h] = -α (1 - α) ((h^(1) / x^(1)) - (h^(2) / x^(2)))² ξ(x)`. -/
theorem powerConeGeometricMean_secondDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    secondDirectionalDerivative ξ x h =
      (-α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ)) * ξ x := sorry

-- Proof sketch: differentiate the second-derivative identity from part `(2)` along `h`, use the
-- first-derivative formula from part `(1)` to rewrite the derivative of `ξ`, and factor out the
-- common term `D²ξ(x)[h,h]`.
/-- Theorem 5.4.7.1 (3): the third directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`D³ξ(x)[h,h,h] =
  -D²ξ(x)[h,h] ((2 - α) (h^(1) / x^(1)) + (1 + α) (h^(2) / x^(2)))`. -/
theorem powerConeGeometricMean_thirdDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    thirdDirectionalDerivative ξ x h =
      -secondDirectionalDerivative ξ x h *
        ((2 - α) * (h.1 / x.1) + (1 + α) * (h.2 / x.2)) := sorry

end
