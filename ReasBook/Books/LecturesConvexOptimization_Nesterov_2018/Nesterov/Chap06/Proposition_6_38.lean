import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_4_16
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Proposition_6_35
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_48

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open RealSymmetricMatrixSpace
open scoped Gradient Matrix.Norms.L2Operator RealSymmetricMatrixSpace

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (n : ℕ)

local instance : CompleteSpace (𝕊^n) :=
  RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

/- Proposition 6.38 lies in the chapter's smoothed semidefinite / affine-precomposition domain.

Sampled owner-style declarations:
- `smoothedSemidefiniteObjective` in `Chap06/Definition_6_48`, the chapter owner for the affine
  pullback `y ↦ f_μ(C + A y)`;
- `hessianQuadraticForm_comp_affine` in `Chap05/Lemma_5_1_1`, the affine-precomposition bridge
  for Hessian quadratic forms;
- `entropySmoothing_contDiff_and_hessianQuadraticForm_le` in `Chap06/Proposition_6_35`, the
  source-specific spectral smoothing bound on `𝕊^n`;
- `hessian` in `Chap01/Definition_1_4_16` and
  `lipschitzGradient_of_norm_hessian_le` in `Chap01/Lemma_1_5_4`, the canonical second-order
  owner and whole-space gradient-Lipschitz bridge;
- mathlib `LipschitzOnWith`, the canonical owner for a set-restricted Lipschitz bound on the
  ordinary ambient gradient field.

Best owner abstraction:
- source-facing: Proposition 6.38's `Q`-restricted reading for the semidefinite owner
  `smoothedSemidefiniteObjective n μ C A` and its ordinary gradient `∇ φ_μ`;
- core/canonical: the intrinsic Hessian operator `hessian f x`, together with the whole-space
  ambient-gradient owner `LipschitzWith L (∇ f)`;
- bridge/view: the affine-precomposition transfer from Proposition 6.35 to
  `smoothedSemidefiniteObjective n μ C A`, followed by restriction to a set `Q`.

Primitive data:
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the semidefinite data `C : 𝕊^n` and `A : E →L[ℝ] 𝕊^n`;
- the global `C²` regularity and Hessian quadratic-form bound inherited from Proposition 6.35
  through the affine pullback `y ↦ C + A y`;
- a feasible set `Q : Set E` only for the textbook restriction corollaries.

Derived API:
- the global Hessian quadratic-form and operator-norm bounds for
  `smoothedSemidefiniteObjective n μ C A`;
- the global ambient-gradient Lipschitz bound for the same owner;
- the `Q`-restricted Proposition 6.38 readings and the canonical-`μ` specializations as thin
  corollaries of those global owners.

Source/core/bridge triage:
- source-facing: Proposition 6.38's `Q`-restricted reading of the ordinary ambient gradient and
  Hessian quadratic-form bounds;
- core/canonical: the global owners `hessian f x` and `LipschitzWith L (∇ f)` for the globally
  defined Chapter 6 objective;
- bridge/view: the affine-precomposition Hessian transfer from Proposition 6.35, followed by
  restriction of global bounds to a set `Q`.

Because `smoothedSemidefiniteObjective n μ C A` is globally defined on `E`, the mathematically
essential public surface is the whole-space Hessian and ambient-gradient control. The textbook
`Q`-restricted formulation is retained only as a thin restriction corollary.
-/

/-- Supporting semidefinite bridge for Proposition 6.38: the Chapter 6 owner
`smoothedSemidefiniteObjective n μ C A` is `C²`, and its Hessian quadratic form is bounded by
`μ⁻¹ ‖A‖² ‖h‖²`. -/
theorem smoothedSemidefiniteObjective_contDiff_and_hessianQuadraticForm_le
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    ContDiff ℝ 2 (smoothedSemidefiniteObjective n μ C A) ∧
      ∀ y h : E,
        inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) ≤
          ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := sorry

/-- Derived canonical bridge for Proposition 6.38: the Hessian operator of
`smoothedSemidefiniteObjective n μ C A` has global norm bound `μ⁻¹ ‖A‖²`. -/
theorem smoothedSemidefiniteObjective_norm_hessian_le
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y : E) :
    ‖hessian (smoothedSemidefiniteObjective n μ C A) y‖ ≤
      ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) := sorry

/-- Proposition 6.38, owner form: the Hessian quadratic form of the smoothed semidefinite
objective is globally bounded by `μ⁻¹ ‖A‖²`. -/
theorem smoothedSemidefiniteObjective_hessianQuadraticForm_le
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y h : E) :
    inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) ≤
      ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  exact (smoothedSemidefiniteObjective_contDiff_and_hessianQuadraticForm_le n μ C A).2 y h

/-- Proposition 6.38, textbook restriction form: on any set `Q`, the same Hessian quadratic-form
bound holds at each point of `Q`. -/
theorem smoothedSemidefiniteObjective_hessianQuadraticForm_le_on
    (Q : Set E) (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)
    {y : E} (_hy : y ∈ Q) (h : E) :
    inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) ≤
      ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  simpa using smoothedSemidefiniteObjective_hessianQuadraticForm_le n μ C A y h

/-- Companion to Proposition 6.38: the ambient gradient of the globally defined smoothed
semidefinite objective is Lipschitz with constant `μ⁻¹ ‖A‖²` on all of `E`. -/
theorem smoothedSemidefiniteObjective_gradient_lipschitz
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    LipschitzWith
      (Real.toNNReal ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)))
      (∇ (smoothedSemidefiniteObjective n μ C A)) := sorry

/-- Proposition 6.38: on any set `Q`, the ordinary ambient gradient of the smoothed semidefinite
objective is Lipschitz with the same constant `μ⁻¹ ‖A‖²`. -/
theorem smoothedSemidefiniteObjective_gradient_lipschitzOn
    (Q : Set E) (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    LipschitzOnWith
      (Real.toNNReal ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)))
      (∇ (smoothedSemidefiniteObjective n μ C A)) Q := by
  exact (smoothedSemidefiniteObjective_gradient_lipschitz n μ C A).lipschitzOnWith

/-- With the canonical parameter `ε / (2 log n)`, Proposition 6.38 gives the same global Hessian
quadratic-form bound with constant `((2 log n) / ε) ‖A‖²`. -/
theorem smoothedSemidefiniteObjective_hessianQuadraticForm_le_with_canonical_mu
    {ε : ℝ} (hε : 0 < ε) (hlogn : 0 < Real.log (n : ℝ))
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y h : E) :
    inner ℝ h
        (hessian
          (smoothedSemidefiniteObjective
            n ⟨ε / (2 * Real.log (n : ℝ)), by positivity⟩ C A) y h) ≤
      (((2 * Real.log (n : ℝ)) / ε) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := sorry

/-- With the canonical parameter `ε / (2 log n)`, the whole-space companion to Proposition 6.38
has ambient gradient Lipschitz constant `((2 log n) / ε) ‖A‖²`. -/
theorem smoothedSemidefiniteObjective_gradient_lipschitz_with_canonical_mu
    {ε : ℝ} (hε : 0 < ε) (hlogn : 0 < Real.log (n : ℝ))
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    LipschitzWith
      (Real.toNNReal (((2 * Real.log (n : ℝ)) / ε) * ‖A‖ ^ (2 : ℕ)))
      (∇ (smoothedSemidefiniteObjective
        n ⟨ε / (2 * Real.log (n : ℝ)), by positivity⟩ C A)) := sorry

/-- With the canonical parameter `ε / (2 log n)`, Proposition 6.38's textbook restriction keeps
the same Hessian quadratic-form bound on any set `Q`. -/
theorem smoothedSemidefiniteObjective_hessianQuadraticForm_le_on_with_canonical_mu
    (Q : Set E) {ε : ℝ} (hε : 0 < ε) (hlogn : 0 < Real.log (n : ℝ))
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) {y : E} (_hy : y ∈ Q) (h : E) :
    inner ℝ h
        (hessian
          (smoothedSemidefiniteObjective
            n ⟨ε / (2 * Real.log (n : ℝ)), by positivity⟩ C A) y h) ≤
      (((2 * Real.log (n : ℝ)) / ε) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  simpa using
    smoothedSemidefiniteObjective_hessianQuadraticForm_le_with_canonical_mu
      n hε hlogn C A y h

/-- With the canonical parameter `ε / (2 log n)`, Proposition 6.38's textbook restriction keeps
the same ambient-gradient Lipschitz constant on any set `Q`. -/
theorem smoothedSemidefiniteObjective_gradient_lipschitzOn_with_canonical_mu
    (Q : Set E) {ε : ℝ} (hε : 0 < ε) (hlogn : 0 < Real.log (n : ℝ))
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    LipschitzOnWith
      (Real.toNNReal (((2 * Real.log (n : ℝ)) / ε) * ‖A‖ ^ (2 : ℕ)))
      (∇ (smoothedSemidefiniteObjective
        n ⟨ε / (2 * Real.log (n : ℝ)), by positivity⟩ C A)) Q := by
  exact
    (smoothedSemidefiniteObjective_gradient_lipschitz_with_canonical_mu
      n hε hlogn C A).lipschitzOnWith

end
