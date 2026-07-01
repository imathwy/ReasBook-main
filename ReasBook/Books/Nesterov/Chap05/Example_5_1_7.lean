import Mathlib
import Nesterov.Chap05.Definition_5_0_24
import Nesterov.Chap05.Example_5_1_2
import Nesterov.Chap05.Example_5_1_3
import Nesterov.Chap05.Theorem_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement
open NewtonDecrement

noncomputable section

/- Example 5.1.7 lies in the scalar self-concordance / Newton-decrement domain.

Sampled owner-style declarations:
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the Chapter 5 owner for standard
  self-concordance;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for domain-level
  positive-definite Hessians;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  affine-quadratic perturbation input, specialized here to zero quadratic part;
* `negLog_isStandardSelfConcordantOn` from `Example_5_1_3`, the canonical `-log` owner on
  `(0, ∞)`;
* `NewtonDecrement.ofPosDefMem` together with the notation `λ[f; x | hx]` from
  `Definition_5_0_24`, the canonical positive-definite-Hessian domain bridge and its
  source-facing theorem surface for Newton decrements.

Source/core/bridge triage:
* source-facing: the scalar barrier `x ↦ ε x - log x`;
* core/canonical: `IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ))` and
  `newtonDecrement`;
* bridge/view: the explicit derivative formulas and the closed-form Newton-decrement evaluation.

Primitive data:
* the scalar perturbation parameter `ε`.

Derived API:
* the evaluation formula for `affinePerturbedLogBarrier`;
* the first- and second-derivative formulas on `(0, ∞)`;
* the standard self-concordance statement on `(0, ∞)`;
* positive definiteness of the scalar Hessian on `(0, ∞)`;
* Hessian nondegeneracy on `(0, ∞)`, derived from that owner;
* the explicit Newton-decrement formula `λ[affinePerturbedLogBarrier ε; x | hx] = |1 - ε x|`.

The source-facing barrier itself is not duplicated upstream, so it remains the owner in this file.
The Newton decrement is already owned by `newtonDecrement`, and this file uses the Chapter 5
source-facing notation `λ[f; x | hx]` on the theorem surface instead of restating the
self-concordance constant in a parallel local decrement view.
-/

/-- The affine perturbation `x ↦ ε x - log x` of the logarithmic barrier on `(0, ∞)`. -/
def affinePerturbedLogBarrier (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ε * x - Real.log x

/-- Evaluating `affinePerturbedLogBarrier ε` recovers the textbook formula `ε x - log x`. -/
-- Proof sketch: unfold `affinePerturbedLogBarrier`.
@[simp]
theorem affinePerturbedLogBarrier_apply (ε x : ℝ) :
    affinePerturbedLogBarrier ε x = ε * x - Real.log x :=
  rfl

-- Proof sketch: differentiate the affine term `x ↦ ε x` and the logarithmic term separately on
-- `(0, ∞)`, then combine the resulting scalar formulas.
/-- The first derivative of `x ↦ ε x - log x` on `(0, ∞)` is `ε - 1 / x`. -/
theorem deriv_affinePerturbedLogBarrier_on_Ioi (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    deriv (affinePerturbedLogBarrier ε) x = ε - 1 / x := sorry

-- Proof sketch: differentiate `deriv_affinePerturbedLogBarrier_on_Ioi` once more on `(0, ∞)` and
-- simplify the rational expression.
/-- The second derivative of `x ↦ ε x - log x` on `(0, ∞)` is `1 / x^2`. -/
theorem secondDeriv_affinePerturbedLogBarrier_on_Ioi (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    iteratedDeriv 2 (affinePerturbedLogBarrier ε) x = 1 / x ^ 2 := sorry

-- Proof sketch: write `affinePerturbedLogBarrier ε` as the sum of the affine function
-- `x ↦ ε x` and the standard self-concordant barrier `x ↦ -log x`; the affine term has vanishing
-- Hessian and third derivative, so the Chapter 5 additive owner preserves the
-- self-concordance constant `1`.
/-- Example 5.1.7: for every real parameter `ε`, the affine perturbation
`x ↦ ε x - log x` is standard self-concordant on `(0, ∞)`. -/
theorem affinePerturbedLogBarrier_isStandardSelfConcordantOn (ε : ℝ) :
    IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ)) (affinePerturbedLogBarrier ε) := by
  have hadd :
      IsSelfConcordantOnWith (Set.Ioi (0 : ℝ)) 1
        (quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) + fun x ↦ -Real.log x) := by
    simpa [Set.univ_inter] using
      (quadraticAffineObjective_isSelfConcordantOnWith_zero
        0 ε (0 : ℝ →L[ℝ] ℝ) ContinuousLinearMap.isPositive_zero).add
        negLog_isStandardSelfConcordantOn
  have hbarrier :
      affinePerturbedLogBarrier ε =
        quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) + fun x ↦ -Real.log x := by
    funext x
    change
      ε * x - Real.log x =
        quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) x + -Real.log x
    rw [sub_eq_add_neg]
    have hq :
        quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) x = inner ℝ ε x := by
      exact (congrArg (fun f : ℝ → ℝ ↦ f x) (quadraticAffineObjective_zero_operator 0 ε)).trans
        (zero_add (inner ℝ ε x))
    have hinner : inner ℝ ε x = x * ε := RCLike.inner_apply ε x
    calc
      ε * x + -Real.log x = x * ε + -Real.log x := by ring
      _ = inner ℝ ε x + -Real.log x := by rw [hinner.symm]
      _ = quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) x + -Real.log x := by rw [hq]
  simpa [IsStandardSelfConcordantOn, hbarrier] using hadd

attribute [instance] affinePerturbedLogBarrier_isStandardSelfConcordantOn

-- Proof sketch: on `(0, ∞)`, the scalar Hessian is `1 / x^2`, so every nonzero direction `u`
-- satisfies `⟪u, hessian f x u⟫ = (1 / x^2) * u^2 > 0`.
/-- On `(0, ∞)`, the Hessian of `x ↦ ε x - log x` is positive definite. -/
theorem affinePerturbedLogBarrier_hasPositiveDefiniteHessianOn
    (ε : ℝ) :
    HasPositiveDefiniteHessianOn (Set.Ioi (0 : ℝ)) (affinePerturbedLogBarrier ε) := by
  sorry

attribute [instance] affinePerturbedLogBarrier_hasPositiveDefiniteHessianOn

-- Proof sketch: substitute the first- and second-derivative formulas on `(0, ∞)` and simplify
-- using `x > 0`, so `sqrt (1 / x^2) = 1 / x`, and identify the scalar formula with the canonical
-- Chapter 5 positive-definite-Hessian Newton-decrement bridge.
/-- On `(0, ∞)`, the canonical Newton decrement of `x ↦ ε x - log x` is `|1 - ε x|`. -/
theorem affinePerturbedLogBarrierNewtonDecrement_eq_abs_one_sub_mul
    (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    λ[affinePerturbedLogBarrier ε; x | hx] = |1 - ε * x| := sorry

-- Proof sketch: specialize
-- `affinePerturbedLogBarrierNewtonDecrement_eq_abs_one_sub_mul` to `ε = 0` and simplify.
/-- For `ε = 0`, the canonical Newton decrement of the logarithmic barrier is identically `1` on
`(0, ∞)`. -/
theorem affinePerturbedLogBarrierNewtonDecrement_zero_eq_one
    (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    λ[affinePerturbedLogBarrier 0; x | hx] = 1 := sorry

-- Proof sketch: evaluate the objective along a sequence `x_k → ∞` inside `(0, ∞)`; the
-- logarithmic term grows without bound, so the barrier values on the domain image tend to `-∞`.
/-- The pure logarithmic barrier `x ↦ -log x` is unbounded below on its natural domain `(0, ∞)`. -/
theorem affinePerturbedLogBarrier_zero_not_bddBelow :
    ¬ BddBelow (affinePerturbedLogBarrier 0 '' Set.Ioi (0 : ℝ)) := sorry

-- Proof sketch: the derivative vanishes exactly at `x = 1 / ε`, and the second derivative is
-- positive on `(0, ∞)`, so strict convexity identifies that stationary point as the global
-- minimizer over the domain.
/-- If `ε > 0`, then the global minimizer of `x ↦ ε x - log x` on `(0, ∞)` is `1 / ε`. -/
theorem isMinOn_affinePerturbedLogBarrier_inv
    {ε : ℝ} (hε : 0 < ε) :
    IsMinOn (affinePerturbedLogBarrier ε) (Set.Ioi (0 : ℝ)) (1 / ε) := sorry

end
