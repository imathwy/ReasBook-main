import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_10 (from Chap06) -/
universe u

/- Definition 6.10 lies in the prox-function / strong-convexity domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`, the canonical owner for strong convexity on a feasible set;
- chapter `IsProxFunction` in `Definition_6_31`, which later packages continuity together with the
  same unit-strong-convexity hypothesis;
- mathlib `IsGreatest`, the canonical order-theoretic owner for the textbook maximum datum
  `max_{x ∈ Q₁} d₁(x)`;
- the generic supremum companion `h.csSup_eq` attached to an `IsGreatest` witness.

Best owner abstraction:
- source-facing: the unit-strong-convexity surface `StrongConvexOn Q₁ 1 d₁` together with the
  maximum-attainment surface `IsGreatest (d₁ '' Q₁) D₁`;
- core/canonical: `StrongConvexOn` and `IsGreatest`;
- bridge/view: the pointwise bound extracted from `IsGreatest`, and the generic supremum
  companion `hD₁.csSup_eq`.

Primitive data:
- a feasible set `Q₁`;
- a prox term `d₁`;
- a bound value `D₁`.

Derived API:
- the prox-function clause, reused directly from `StrongConvexOn Q₁ 1 d₁`;
- the order-theoretic maximum surface `IsGreatest (d₁ '' Q₁) D₁`;
- the induced pointwise bound `d₁ x ≤ D₁` for `x ∈ Q₁` and the companion supremum identity.

Source/core/bridge triage:
- source-facing: `StrongConvexOn Q₁ 1 d₁` and `IsGreatest (d₁ '' Q₁) D₁`;
- core/canonical: `StrongConvexOn` and `IsGreatest`;
- bridge/view: `image_le_of_isGreatest` and `hD₁.csSup_eq`.

Definition 6.10 therefore does not introduce a second owner for prox-functions or prox-bounds:
the strong-convexity clause is already owned by `StrongConvexOn`, and the `D₁` datum is already
captured canonically by `IsGreatest` on the image set.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q₁ : Set E} {d₁ : E → ℝ}

/- Definition 6.10: for a real normed space, a prox-function on `Q₁` is exactly the unit-strongly
convex owner `StrongConvexOn Q₁ 1 d₁`. -/
#check (StrongConvexOn Q₁ 1 d₁ : Prop)

end

section

variable {E : Type u}
variable {Q₁ : Set E} {d₁ : E → ℝ} {D₁ : ℝ}

/- The textbook constant `D₁` is the maximum of `d₁` on `Q₁`; in Lean this is the canonical
order-theoretic surface `IsGreatest (d₁ '' Q₁) D₁`. -/
#check IsGreatest (d₁ '' Q₁) D₁

section

variable (hD₁ : IsGreatest (d₁ '' Q₁) D₁)

/- The supremum reformulation is the generic order-theoretic companion `hD₁.csSup_eq`, not a
second source-facing owner. -/
#check hD₁.csSup_eq

end

/-- If `D₁` is the greatest value of `d₁` on `Q₁`, then every feasible point satisfies the
textbook bound `d₁ x ≤ D₁`. -/
theorem image_le_of_isGreatest (hD₁ : IsGreatest (d₁ '' Q₁) D₁) {x : E} (hx : x ∈ Q₁) :
    d₁ x ≤ D₁ :=
  hD₁.2 (Set.mem_image_of_mem d₁ hx)

end

/-! ### Lemma_6_10 (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/- Lemma 6.10 lies in Chapter 6's zero-smoothing dual-objective / Danskin-gradient domain.

Relevant owner-style declarations sampled before repair:
- `smoothedDualObjectiveMinimand` and `smoothedDualObjective` in `Chap06/Proposition_6_25`, the
  canonical Chapter 6 owners for the zero-smoothing primal slice and dual value;
- `argmin[Q₁]` in `Chap01/Definition_1_3_3`, the canonical feasible minimizer owner used
  throughout the project;
- `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical bridge from the
  `EReal`-valued dual owner to its finite real part;
- `hatf ∈ 𝒮^0_σ(Q₁)` in `Chap03/Definition_3_47`, the source-facing strong-convexity owner.

Source/core/bridge triage:
- source-facing: the bundled concavity-and-gradient statement of Lemma 6.10;
- core/canonical: `smoothedDualObjective A Q₁ hatf hatφ 0 0` together with the pointwise argmin
  owner `x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`;
- bridge/view: the explicit Hilbert-space gradient formula below.

The previous file depended on a broken recall chain through `Definition_6_33`. The repaired file
states Lemma 6.10 directly on the actual available chapter owners, without introducing a parallel
wrapper API.
-/

section

variable [CompleteSpace E₂]

-- Proof sketch: use the strong-convexity owner
-- `0 < σ ∧ StrongConvexOn Q₁ σ hatf` to obtain uniqueness of the
-- pointwise argmin in each zero-smoothing primal slice. Then apply the Chapter 6 Danskin-style
-- gradient statement for `smoothedDualObjective A Q₁ hatf hatφ 0 0` together with convexity of
-- `hatφ` to conclude concavity of the finite real part and the displayed gradient formula.
/-- Lemma 6.10: if `0 < σ` and `hatf` is `σ`-strongly convex on `Q₁`, if `x₀ u` is a feasible
minimizer of the zero-smoothing primal slice for every `u`, and if `\hat φ` is differentiable and
convex, then the finite real part of the canonical zero-smoothing dual objective is concave and
has gradient `-\nabla \hat φ(u) + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))`. -/
theorem dualObjective_concave_and_hasGradientAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hσ : 0 < σ)
    (hhatf : StrongConvexOn Q₁ σ hatf)
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ)
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    ConcaveOn ℝ Set.univ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) ∧
      ∀ u : E₂,
        HasGradientAt
          (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
          (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))) u := sorry

end

end

/-! ### Proposition_6_10 (from Chap06) -/
noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-
Proposition 6.10 lies in the constrained smoothing / within-set differentiability domain.

Sampled owner-style declarations:
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the chapter owner for the smoothed
  explicit-model objective on a feasible set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the ambient owner reused by
  `explicitModelSmoothedProblem`;
- mathlib `HasFDerivWithinAt.add`, the canonical within-set derivative sum rule;
- mathlib `LipschitzOnWith`, the canonical set-restricted Lipschitz owner.

Best owner abstraction:
- source-facing: `explicitModelSmoothedProblem Q₁ hatF fμ`;
- core/canonical: `HasFDerivWithinAt` and `LipschitzOnWith`;
- bridge/view: the evaluation lemma `explicitModelSmoothedProblem_apply`.

Primitive data:
- the feasible set `Q₁`;
- the base term `hatF` and smoothing term `fμ`;
- chosen derivative fields `gradHatF` and `gradFμ`;
- the derivative and Lipschitz hypotheses for those fields.

Derived API:
- the within-set derivative of the smoothed objective, obtained by the additive derivative rule;
- the Lipschitz bound for the summed derivative field, obtained by the triangle inequality.

This proposition is source-facing but not a new owner. The earlier local pointwise-sum wrapper
duplicated the existing Chapter 6 owner `explicitModelSmoothedProblem`, so the theorem now talks
directly about that owner and derives the sum view only through the existing evaluation lemma.
-/

/-- Proposition 6.10: if `\hat f` has `M`-Lipschitz gradient on `Q₁` and `f_μ` has gradient
Lipschitz constant `Real.toNNReal ((1 / μ) * ‖A‖^2)` on `Q₁`, then the objective of the
explicit-model smoothed problem from Definition 6.9 has derivative selection `gradHatF + gradFμ`
on `Q₁`, hence is differentiable there, and this derivative selection is Lipschitz on `Q₁` with
constant `M + Real.toNNReal ((1 / μ) * ‖A‖^2)`. -/
theorem explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn
    {Q₁ : Set E} {hatF fμ : E → ℝ} {gradHatF gradFμ : E → StrongDual ℝ E}
    (A : E →L[ℝ] F) {μ : ℝ} {M : NNReal}
    (hhatF : ∀ x ∈ Q₁, HasFDerivWithinAt hatF (gradHatF x) Q₁ x)
    (hhatF_lipschitz : LipschitzOnWith M gradHatF Q₁)
    (hfμ : ∀ x ∈ Q₁, HasFDerivWithinAt fμ (gradFμ x) Q₁ x)
    (hfμ_lipschitz :
      LipschitzOnWith (Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) gradFμ Q₁) :
    (∀ x ∈ Q₁,
      HasFDerivWithinAt
        (explicitModelSmoothedProblem Q₁ hatF fμ)
        (gradHatF x + gradFμ x) Q₁ x) ∧
    LipschitzOnWith
      (M + Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ)))
      (fun x ↦ gradHatF x + gradFμ x) Q₁ := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa [explicitModelSmoothedProblem] using (hhatF x hx).add (hfμ x hx)
  · intro x hx y hy
    calc
      edist (gradHatF x + gradFμ x) (gradHatF y + gradFμ y) ≤
          edist (gradHatF x) (gradHatF y) + edist (gradFμ x) (gradFμ y) :=
        edist_add_add_le _ _ _ _
      _ ≤
          (M + Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) * edist x y := by
        simpa [add_mul] using
          add_le_add (hhatF_lipschitz hx hy) (hfμ_lipschitz hx hy)

end

/-! ### Theorem_6_10 (from Chap06) -/
open RealSymmetricMatrixSpace
open scoped BigOperators
open scoped MatrixOrder
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Theorem 6.10 lies in the chapter's real-symmetric spectral-power-series / Hessian domain.

Sampled owner-style declarations:
- Chapter 6 `AnalyticSymmetricSpectralFunction` in `Definition_6_43`, the source-facing owner for
  analytic symmetric spectral functions with positive radius and coefficient sign condition
  `0 ≤ a_k` for `k ≥ 2`;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the chapter owner for the ordered eigenvalue
  vector of a real symmetric matrix on `𝕊^n`;
- mathlib `CFC.abs`, together with `CFC.abs_nonneg` and Hermitian eigenvalues, as the canonical
  absolute-value owner for real symmetric matrices;
- mathlib `iteratedFDeriv` and `iteratedDeriv`, the canonical Hessian quadratic-form owner and
  one-variable second-derivative owner for scalar-valued maps;
- `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing` in `Theorem_6_9`, the chapter
  trace-power Hessian estimate used termwise in the power-series proof route.

Best owner abstraction:
- source-facing: the Hessian quadratic-form inequality for the spectral sum
  `X ↦ ∑ i, f (λᵢ(X))` attached to an analytic symmetric spectral function `Φ`;
- core/canonical: `AnalyticSymmetricSpectralFunction`, `𝕊^n`, `eigenvalues`, `CFC.abs`,
  `iteratedFDeriv`, and `iteratedDeriv`;
- bridge/view: the power-series expansion into trace-power owners together with Theorem 6.9's
  termwise spectral bound.

Primitive data:
- an owner `Φ : AnalyticSymmetricSpectralFunction`, whose primitive fields are the coefficients,
  positive convergence radius, and the source-essential sign condition `0 ≤ coeff k` for `k ≥ 2`;
- a symmetric matrix `X : SymmMat` and a symmetric direction `H : SymmMat`;
- the spectral-domain hypothesis `hX : X ∈ Φ.dom`.

Derived API:
- the source-facing spectral owner `Φ.matrixFun`;
- the right-hand eigenvalue-square bound through the eigenvalues of `CFC.abs X` and
  `CFC.abs H`.

Source/core/bridge triage:
- source-facing: Theorem 6.10's Hessian bound for the spectral sum itself;
- core/canonical: the chapter `𝕊^n`, `eigenvalues`, and absolute-value owners together with
  `iteratedFDeriv`;
- bridge/view: the trace-power series decomposition used only in the proof strategy.

The previous version also dropped the source-essential coefficient sign condition in degrees
`k ≥ 2`, which makes the claimed inequality false already in the scalar case. This refinement
therefore moves the theorem to the existing owner `AnalyticSymmetricSpectralFunction`, whose
primitive data already includes that sign condition, and deletes the parallel raw coefficient /
radius interface.
-/

namespace AnalyticSymmetricSpectralFunction

-- Proof sketch: expand the spectral function induced by `Φ` as the convergent trace-power series
-- `∑ k, Φ.coeff k * π[k] X`, differentiate termwise on a neighborhood inside the spectral domain,
-- apply the Chapter 6 power-trace Hessian estimate term-by-term, use `Φ.coeff_nonneg` for
-- summability of the termwise bounds, and then resum to identify the coefficient sum with the
-- `iteratedDeriv 2 (FormalMultilinearSeries.ofScalarsSum Φ.coeff)` at the eigenvalues of
-- `CFC.abs X`.
/-- Theorem 6.10: if `Φ` is an analytic symmetric spectral function, then for every symmetric
matrix `X` in its spectral domain and every symmetric direction `H`, the Hessian quadratic form of
the induced spectral function `Φ.matrixFun`
is bounded above by
`∑ i, iteratedDeriv 2 (FormalMultilinearSeries.ofScalarsSum Φ.coeff) (λᵢ(CFC.abs X)) *
  (λᵢ(CFC.abs H))^2`. -/
theorem hessianQuadraticForm_le_absEigenvalueSquareSum
    (Φ : AnalyticSymmetricSpectralFunction) (X : SymmMat) (hX : X ∈ Φ.dom) (H : SymmMat) :
    (iteratedFDeriv ℝ 2 Φ.matrixFun X) ![H, H] ≤
      ∑ i : Fin n,
        iteratedDeriv 2 (FormalMultilinearSeries.ofScalarsSum Φ.coeff)
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i)) *
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (2 : ℕ)) := sorry

end AnalyticSymmetricSpectralFunction
