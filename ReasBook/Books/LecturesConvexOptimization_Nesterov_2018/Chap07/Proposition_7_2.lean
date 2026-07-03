import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.2 lies in the Euclidean direct-structure first-order complexity domain.

Sampled owner-style declarations:
- mathlib `EuclideanSpace ℝ (Fin n)` for the ambient model `ℝⁿ`;
- mathlib `NNReal` for the nonnegative constants `γ₁(F)` and `R`;
- mathlib `Real.sqrt` for the factor `√(N (N + 1))`;
- the chapter-style lower-level scheme surface `ℕ+ → NNReal → Eₙ → Eₙ`, matching the notation
  `S_N(R)`.

Best owner abstraction:
- source-facing: the textbook output guarantee for the method `S_N(R)` on every start point
  within Euclidean distance `R` of a chosen optimal point `x*`;
- core/canonical: a scheme `S` taking an iteration count, a radius parameter, and a start point;
- bridge/view: the positive parameters `γ₁(F)` and `R` are recorded as `NNReal` data.

Primitive data:
- the objective `f`;
- the method surface `S`;
- the coefficient `γ₁(F)`, the radius `R`, the iteration count `N`, the reference point `xStar`,
  and the start point `x₀`.

Derived API:
- the displayed complexity bound
  `f (S_N(R)) - f(x*) ≤ 2 γ₁(F) R / √(N (N + 1))`.

Source/core/bridge triage:
- source-facing: Proposition 7.2 itself;
- core/canonical: the scheme `S : ℕ+ → NNReal → Eₙ → Eₙ`;
- bridge/view: coercing the `NNReal` parameters to `ℝ` in the final bound.

As in nearby Chapter 7 item files, the proposition is stated directly on the method surface
`S_N(R)` and keeps only the data that appears in the displayed estimate. The convexity/minimizer
prose is part of the surrounding chapter setup for constructing this method, rather than separate
wrapper data in this item file.
-/

-- Proof sketch: instantiate the Chapter 6 direct-structure estimate for the method `S_N(R)` with
-- the homogeneous-model constants `‖A‖ = γ₁(F)`, `D₁ = R² / 2`, `D₂ = 1 / 2`, and `M = 0`, then
-- simplify the resulting coefficient.
/-- Proposition 7.2 [Chapter7_1.json:26]: for the Chapter 7 direct-structure method `S_N(R)`,
every start point `x₀` within Euclidean distance `R` of `x*` has objective gap at most
`2 γ₁(F) R / √(N (N + 1))` after `N` steps. -/
theorem direct_structure_method_output_sub_optimalValue_le
    (f : Eₙ → ℝ) (S : ℕ+ → NNReal → Eₙ → Eₙ) (γ₁ : NNReal) (N : ℕ+) (R : NNReal)
    (xStar : Eₙ) {x₀ : Eₙ} (hx₀ : ‖x₀ - xStar‖ ≤ (R : ℝ)) :
    f (S N R x₀) - f xStar ≤
      (2 * (γ₁ : ℝ) * (R : ℝ)) /
        Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := sorry

end
