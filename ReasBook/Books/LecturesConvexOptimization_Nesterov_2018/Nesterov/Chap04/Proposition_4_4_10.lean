import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_7
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Text_4_2_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 4.4.10 lies in the Newton / quadratic-entry domain.

Sampled owner declarations:
* `NewtonSystem.Method` in `Chap01/Algorithm_1_7_1`, the orbit owner for Newton iterates;
* `HasQuadraticConvergenceFrom` in `Text_4_2_24`, the chapter owner for quadratic tail
  convergence from a given index;
* `StrongConvexOn.eq_of_isMinOn` in `Chap03/Corollary_3_2_3`, the canonical uniqueness owner for
  a strongly convex minimizer;
* `HasLipschitzContinuousHessian`, written on theorem surfaces as `φ ∈ C22[L]`, in
  `Definition_4_2_7`, the chapter owner for the Hessian-Lipschitz hypothesis.

Best owner abstraction:
* source-facing: the scalar characteristic quantity `ξ = L ‖x₀ - x*‖ / σ` and the first
  quadratic-convergence index bound from the textbook proposition;
* core/canonical: `NewtonSystem.Method (∇ φ) x0`, `StrongConvexOn Set.univ σ φ`, `φ ∈ C22[L]`,
  and `HasQuadraticConvergenceFrom method xStar k`;
* bridge/view: `NewtonSystem.Method.zero_eq`, recovering the source initial point from the orbit.

Primitive data:
* the objective `φ`, the strong-convexity modulus `σ`, the Hessian-Lipschitz constant `L`, the
  minimizer `xStar`, the source initial point `x0`, and the Newton orbit `method`.

Derived API:
* the least quadratic-convergence index package
  `IsLeast {k : ℕ | HasQuadraticConvergenceFrom method xStar k} N1`.
-/

/-- The characteristic quantity `ξ = L ‖x₀ - x*‖ / σ` attached to the modified Newton
convergence estimate. -/
def modifiedNewtonCharacteristicQuantity
    (σ : ℝ) (L : NNReal) (x0 xStar : E) : ℝ :=
  (L : ℝ) * ‖x0 - xStar‖ / σ

-- Proof sketch: unfold `modifiedNewtonCharacteristicQuantity`.
/-- Expanding `modifiedNewtonCharacteristicQuantity σ L x₀ x*` gives the textbook formula
`ξ = L ‖x₀ - x*‖ / σ`. -/
@[simp] theorem modifiedNewtonCharacteristicQuantity_def
    (σ : ℝ) (L : NNReal) (x0 xStar : E) :
    modifiedNewtonCharacteristicQuantity σ L x0 xStar =
      (L : ℝ) * ‖x0 - xStar‖ / σ :=
  rfl

section

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: use the canonical owner hypotheses `StrongConvexOn Set.univ σ φ` and `φ ∈ C22[L]`
-- to control the global phase of the modified Newton orbit by the characteristic quantity
-- `ξ = L ‖x₀ - x*‖ / σ`. Strong convexity supplies uniqueness of the minimizer from `hxStar`.
-- The first phase ends when the orbit enters the local quadratic-convergence regime, and the
-- textbook estimate yields the bound `N₁ ≤ 6.25 * sqrt ξ` whenever `ξ ≥ 1`.
/-- If the modified-Newton characteristic quantity `ξ = L ‖x₀ - x*‖ / σ` is strictly smaller
than `1`, then the Newton orbit already starts in the local quadratic-convergence regime, so it
converges quadratically to `x*` from index `0`. -/
theorem modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : NewtonSystem.Method (∇ φ) x0)
    (hxi : modifiedNewtonCharacteristicQuantity σ L x0 xStar < 1) :
    HasQuadraticConvergenceFrom method xStar 0 := by
  sorry

/-- Proposition 4.4.10: with characteristic quantity
`ξ = L ‖x₀ - x*‖ / σ`, if `φ` is `σ`-strongly convex on `Set.univ`, belongs to `C22[L]`, `x*`
minimizes `φ` on `Set.univ`, `x` is the associated modified Newton iteration started at `x₀`, and
`N₁` is the least iterate index from which the orbit converges quadratically to `x*`, then the
assumption `1 ≤ ξ` implies `N₁ ≤ 6.25 * sqrt ξ`. Under `φ ∈ C22[L]`, this is the canonical-owner
reformulation of the textbook Hessian lower-bound and Hessian-Lipschitz hypotheses. -/
theorem modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity
    {φ : E → ℝ} {σ : ℝ} {L : NNReal} {x0 xStar : E}
    (hσ : 0 < σ)
    (hφ_strong : StrongConvexOn Set.univ σ φ)
    (hφ_hessian : φ ∈ C22[L])
    (hxStar : IsMinOn φ Set.univ xStar)
    (method : NewtonSystem.Method (∇ φ) x0)
    (hxi : 1 ≤ modifiedNewtonCharacteristicQuantity σ L x0 xStar)
    {N1 : ℕ}
    (hN1 : IsLeast {k : ℕ | HasQuadraticConvergenceFrom method xStar k} N1) :
    (N1 : ℝ) ≤
      (25 / 4 : ℝ) * Real.sqrt (modifiedNewtonCharacteristicQuantity σ L x0 xStar) := sorry

end
