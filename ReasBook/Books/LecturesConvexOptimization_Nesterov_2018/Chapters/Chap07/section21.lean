import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_21 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators

variable {p n : ℕ}

local notation "Eₚ" => EuclideanSpace ℝ (Fin p)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.21 lies in Chapter 7's linear-matrix Gram-operator domain.

Sampled owner-style declarations:
- `LinearMap.adjoint`, the canonical adjoint owner for finite-dimensional inner-product spaces;
- `LinearMap.adjoint_inner_right`, the owner-level evaluation rule for `L†`;
- `Matrix.gram` and `Matrix.gram_apply`, the canonical Gram-matrix owner and its entry formula;
- `LinearMap.toMatrixOrthonormal`, the standard-basis matrix presentation of an endomorphism;
- `Matrix.toEuclideanLin`, the bridge from square matrices to Euclidean endomorphisms.

Best owner abstraction:
- source-facing: the operator on `ℝᵖ` attached to the coefficient map `L(x) = ∑ᵢ xᵢ Aᵢ`;
- core/canonical: the intrinsic Gram operator `L†L`;
- bridge/view: the Frobenius Gram matrix `Matrix.gram ℝ coeffMatrices` and its realization as the
  standard-basis matrix of `L†L`.

Primitive data:
- a family `coeffMatrices : Fin p → Mₙ` of real square matrices.

Derived API:
- the coefficient-sum linear map `linearMatrixCombination`;
- the Gram operator `linearMatrixGramOperator = L†L`;
- the canonical Gram matrix `Matrix.gram ℝ coeffMatrices`;
- the bridge identifying the standard-basis matrix of `linearMatrixGramOperator` with
  `Matrix.gram ℝ coeffMatrices`.

Source/core/bridge triage:
- source-facing: Definition 7.21's operator `G`;
- core/canonical: `(linearMatrixCombination coeffMatrices).adjoint ∘ₗ
  linearMatrixCombination coeffMatrices`;
- bridge/view: the Frobenius-entry formula for `Matrix.gram ℝ coeffMatrices`, the standard-basis
  matrix formula for `G`, and the equality `G = Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices)`.

This refinement keeps the source-facing coefficient map and centers the public owner on the
intrinsic operator `L†L`. The matrix presentation `Matrix.gram ℝ coeffMatrices` is retained only
as the canonical bridge/view theorem. -/

private instance ambientMatrixNormedAddCommGroup : NormedAddCommGroup Mₙ :=
  toMatrixNormedAddCommGroup (1 : Mₙ) PosDef.one

private instance ambientMatrixInnerProductSpace : InnerProductSpace ℝ Mₙ :=
  toMatrixInnerProductSpace (1 : Mₙ) PosDef.one.posSemidef

/-- The linear map `x ↦ ∑ᵢ xᵢ Aᵢ` associated with a family of real square matrices. -/
def linearMatrixCombination (coeffMatrices : Fin p → Mₙ) : Eₚ →ₗ[ℝ] Mₙ where
  toFun x := ∑ i : Fin p, x i • coeffMatrices i
  map_add' x y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp [Finset.smul_sum, smul_smul]

/-- Evaluating `linearMatrixCombination` gives the coefficient-weighted matrix sum
`∑ᵢ xᵢ Aᵢ`. -/
theorem linearMatrixCombination_apply
    (coeffMatrices : Fin p → Mₙ) (x : Eₚ) :
    linearMatrixCombination coeffMatrices x = ∑ i : Fin p, x i • coeffMatrices i := rfl

/-- Definition 7.21 (2): the operator `G : ℝᵖ → ℝᵖ` attached to the matrix family
`A₁, …, Aₚ` is the intrinsic Gram operator `L†L` for
`L(x) = ∑ᵢ xᵢ Aᵢ`, where `L†` is taken with respect to the Frobenius pairing on matrix entries.
Its standard-basis matrix is identified below with the Frobenius Gram matrix
`Matrix.gram ℝ coeffMatrices`. -/
def linearMatrixGramOperator (coeffMatrices : Fin p → Mₙ) : Eₚ →ₗ[ℝ] Eₚ :=
  (linearMatrixCombination coeffMatrices).adjoint ∘ₗ linearMatrixCombination coeffMatrices

section

variable (p n)

/- The bridge/view matrix owner used by Definition 7.21 is `Matrix.gram` on the intrinsic matrix
family. -/
set_option linter.hashCommand false in
#check (Matrix.gram ℝ : (Fin p → Mₙ) → Matrix (Fin p) (Fin p) ℝ)

end

/-- Expanding `Matrix.gram ℝ coeffMatrices` gives the textbook entrywise Frobenius formula. -/
theorem matrix_gram_apply_eq_entrywise_sum
    (coeffMatrices : Fin p → Mₙ) (i j : Fin p) :
    Matrix.gram ℝ coeffMatrices i j =
      ∑ a : Fin n, ∑ b : Fin n, coeffMatrices i a b * coeffMatrices j a b := by
  rw [Matrix.gram_apply]
  change Matrix.trace (coeffMatrices j * 1 * (coeffMatrices i)ᵀ) =
    ∑ a : Fin n, ∑ b : Fin n, coeffMatrices i a b * coeffMatrices j a b
  simp [Matrix.trace, Matrix.mul_apply, mul_comm]

/-- The quadratic form of `linearMatrixGramOperator` is the Frobenius norm square of the
associated matrix combination. -/
theorem linearMatrixGramOperator_quadratic_form
    (coeffMatrices : Fin p → Mₙ) (x : Eₚ) :
    inner ℝ (linearMatrixGramOperator coeffMatrices x) x =
      ∑ i : Fin n, ∑ j : Fin n,
        ((linearMatrixCombination coeffMatrices x) i j) *
          ((linearMatrixCombination coeffMatrices x) i j) := by
  sorry

/-- The matrix of `linearMatrixGramOperator` in the standard orthonormal basis of `ℝᵖ` is the
canonical Gram matrix of the coefficient family. -/
theorem linearMatrixGramOperator_toMatrixOrthonormal
    (coeffMatrices : Fin p → Mₙ) :
    LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)
        (linearMatrixGramOperator coeffMatrices) =
      Matrix.gram ℝ coeffMatrices := by
  ext i j
  rw [LinearMap.toMatrixOrthonormal_apply_apply, linearMatrixGramOperator, LinearMap.comp_apply,
    Matrix.gram_apply]
  simpa [linearMatrixCombination] using
    (LinearMap.adjoint_inner_right (linearMatrixCombination coeffMatrices)
      ((EuclideanSpace.basisFun (Fin p) ℝ) i)
      ((linearMatrixCombination coeffMatrices) ((EuclideanSpace.basisFun (Fin p) ℝ) j)))

/-- The intrinsic Gram operator `linearMatrixGramOperator coeffMatrices = L†L` is represented by
`Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices)` in the standard orthonormal basis of
`ℝᵖ`. -/
theorem linearMatrixGramOperator_eq_toEuclideanLin_gram
    (coeffMatrices : Fin p → Mₙ) :
    linearMatrixGramOperator coeffMatrices = Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices) := by
  apply (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)).injective
  change LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)
      (linearMatrixGramOperator coeffMatrices) =
    LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p) ℝ)
      (Matrix.toEuclideanLin (Matrix.gram ℝ coeffMatrices))
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
    linearMatrixGramOperator_toMatrixOrthonormal coeffMatrices

end

/-! ### Lemma_7_21 (from Chap07) -/
universe u

/- Lemma 7.21 lies in the chapter's estimating-sequence recursion domain.

Sampled owner-style declarations:
* `IsEstimatingSequence` in `Chap02/Definition_2_21`, the chapter owner for affine upper models
  written via `AffineMap.lineMap`;
* `strongConvexEstimatingFunction_upper_bound_apply` in `Chap02/Lemma_2_8`, a stagewise
  estimating-function upper recursion theorem;
* `CubicNewtonEstimatingSequence` in `Chap04/Definition_4_2_14`, the chapter owner bundling
  `A`, `a`, and `ψ` when a full method object exists.

Source/core/bridge triage:
* source-facing: the additive recursion bound of Lemma 7.21 itself;
* core/canonical: the general estimating-sequence owner `IsEstimatingSequence`, which is nearby
  but not exact here because this lemma uses unnormalized accumulated weights `A_k` rather than an
  affine `lineMap` coefficient;
* bridge/view: none needed.

Primitive data:
* the set `Q`, transformed objective `hatF`, function family `ψ`, increments `a`, and accumulated
  weights `A`;
* the initial condition `A 0 = 0` and recursion `A (k + 1) = A k + a k`;
* the one-step upper bound for `ψ`.

Derived API:
* the global estimate `ψ k x ≤ A k * hatF x + ψ 0 x`.

Since no existing upstream owner theorem has this exact additive-recursion interface, this file
keeps the source-facing statement and only removes unnecessary `ℝ`-specificity.
-/

variable {X : Type u} {α : Type*} [Semiring α] [PartialOrder α] [IsOrderedRing α]

-- Proof sketch: argue by induction on `k`. The base case uses `A 0 = 0`. For the inductive step,
-- combine the one-step estimate `ψ (k + 1) x ≤ ψ k x + a k * hatF x` with the inductive
-- hypothesis and then rewrite the coefficient of `hatF x` using `A (k + 1) = A k + a k`.
/-- Lemma 7.21: if the estimating functions satisfy the one-step upper recursion
`ψ_{k+1}(x) ≤ ψ_k(x) + a_k \hat f(x)` on `Q`, with `A₀ = 0` and `A_{k+1} = A_k + a_k`, then
`ψ_k(x) ≤ A_k \hat f(x) + ψ_0(x)` for every `x ∈ Q`. This is the global estimating property
obtained from the nonlinear lower-support inequality used in the quasi-Newton method. -/
theorem estimating_function_le_weighted_transformed_objective_add_initial
    {Q : Set X} {hatF : X → α} {ψ : ℕ → X → α} {A a : ℕ → α}
    (hA0 : A 0 = 0)
    (hA_succ : ∀ k : ℕ, A (k + 1) = A k + a k)
    (hpsi_succ : ∀ k : ℕ, ∀ ⦃x : X⦄, x ∈ Q → ψ (k + 1) x ≤ ψ k x + a k * hatF x)
    (k : ℕ) (x : X) (hx : x ∈ Q) :
    ψ k x ≤ A k * hatF x + ψ 0 x := by
  induction k with
  | zero =>
      simp [hA0]
  | succ k ih =>
      calc
        ψ (k + 1) x ≤ ψ k x + a k * hatF x := hpsi_succ k hx
        _ ≤ (A k * hatF x + ψ 0 x) + a k * hatF x := add_le_add ih le_rfl
        _ = A k * hatF x + a k * hatF x + ψ 0 x := by ac_rfl
        _ = (A k + a k) * hatF x + ψ 0 x := by rw [← add_mul]
        _ = A (k + 1) * hatF x + ψ 0 x := by rw [hA_succ]

/-! ### Proposition_7_21 (from Chap07) -/
open EuclideanSpace (nonnegativeOrthant)
open scoped BigOperators Gradient PositiveDefMatrixNorm SmoothConvex SupportFunction

noncomputable section

variable {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 7.21 lies in Chapter 7's sign-symmetric support / weighted smooth-max domain.

Sampled owner-style declarations:
- `hessian` in `Chap01/Definition_1_4_16`, the project owner for second-order derivatives;
- `ξ[Q]` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for support
  functions;
- `positiveDefMatrixNorm` and the notations `‖x‖[D]`, `‖x‖[D,*]` in `Chap07/Definition_7_23`,
  the chapter owners for the weighted norm and its dual;
- `𝓕[L, p]¹¹` and `ConvexC1SeminormSmooth.dualNorm_gradient_sub_le` in `Chap02/Theorem_2_5`,
  the canonical smoothness owner and its gradient-Lipschitz consequence;
- `Matrix.IsDiag` in mathlib's matrix diagonal API, the canonical owner for the diagonality
  needed to pass from `h` to `|h|` in the weighted norm;
- `signSymmetricConvexHull` in `Chap07/Definition_7_35`, the source-facing owner carrying the
  needed absolute-value support data;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the source-facing smoothing owner for
  finite max-inner objectives.

Best owner abstraction:
- source-facing: Proposition 7.21's Hessian and dual-gradient estimates for
  `smoothMaxInnerApproximation a μ`;
- core/canonical: `hessian`, `smoothMaxInnerApproximation a μ`, `positiveDefMatrixNorm`, and the
  Chapter 7 box-hull owner `signSymmetricConvexHull a`;
- bridge/view: the orthant support upper bound for `ξ[signSymmetricConvexHull a]`, which is the
  correct source-facing way to control the absolute pairings `|⟪aᵢ, h⟫|` entering the Hessian.

Primitive data:
- the finite family `a : ι → E`;
- the orthant hypothesis `ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n`;
- the diagonal positive-definite matrix owner `D` together with `hDdiag : D.1.IsDiag`;
- the positive smoothing parameter `μ`.

Derived API:
- the orthant support upper bound for the sign-symmetric hull;
- the Hessian quadratic-form bound;
- the Chapter 2 smooth-convex owner theorem for `smoothMaxInnerApproximation a μ`;
- the resulting weighted dual-gradient Lipschitz estimate.

Source/core/bridge triage:
- source-facing: the Hessian and weighted dual-gradient estimates below;
- core/canonical: `hessian`, `smoothMaxInnerApproximation a μ ∈ 𝓕[L, ‖·‖[D]]¹¹`,
  `signSymmetricConvexHull a`, and the weighted norm owner `‖·‖[D]`;
- bridge/view: the orthant support assumption, kept as theorem-level data rather than a duplicate
  public wrapper.

This refinement removes the orthant-restricted finite-range support hypothesis, which was too weak
for global Hessian control. Proposition 7.21 now uses the sign-symmetric hull owner that carries
the needed absolute-value layer from the surrounding Chapter 7 development.
-/

section

variable (a : ι → E)
variable (D : {D : Mat // D.PosDef}) (μ : {μ : ℝ // 0 < μ})

/-- Proposition 7.21: if the sign-symmetric box-hull support function of a nonnegative family
`(a i)_{i ∈ ι}` is bounded on the nonnegative orthant by `2 √n ‖·‖_D` for a diagonal
positive-definite matrix `D`, then the Hessian quadratic form of the log-sum-exp smoothing
`smoothMaxInnerApproximation a μ` is bounded by
`(4 n / μ) ‖h‖_D²`. -/
-- Proof sketch: the standard log-sum-exp Hessian estimate gives
-- `⟪∇²f_μ(x) h, h⟫ ≤ μ⁻¹ (max_i |⟪aᵢ, h⟫|)^2`. For arbitrary `h`, the nonnegative vector
-- `|h|` lies in `nonnegativeOrthant n`, and because each `aᵢ` is nonnegative one has
-- `|⟪aᵢ, h⟫| ≤ (ξ[signSymmetricConvexHull a] |h|).toReal`. Apply `hBoxSupport` at `|h|` and use
-- the diagonal-norm invariance `‖|h|‖[D] = ‖h‖[D]`.
theorem smoothMaxInnerApproximation_hessian_quadratic_form_le
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D])
    (x h : E) :
    inner ℝ (hessian (smoothMaxInnerApproximation a μ) x h) h ≤
      (4 : ℝ) * n / μ.1 * ‖h‖[D] ^ 2 := sorry

-- Proof sketch: first prove the source-facing Hessian quadratic-form bound above, then combine it
-- with the `C²` regularity and convexity of `smoothMaxInnerApproximation a μ` and apply the
-- Chapter 2 owner bridge `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded`.
/-- The Chapter 2 smooth-convex owner view of Proposition 7.21 for the weighted norm `‖·‖[D]`. -/
theorem smoothMaxInnerApproximation_mem_F11_positiveDefMatrixNorm
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D]) :
    smoothMaxInnerApproximation a μ ∈
      𝓕[Real.toNNReal ((4 : ℝ) * n / μ.1), positiveDefMatrixNorm D.1 D.2]¹¹ := sorry

/-- The gradient of the log-sum-exp smoothing is Lipschitz with respect to the weighted norm
`‖·‖[D]` and its dual norm `‖·‖[D,*]`, with constant `4 n / μ`, for the same diagonal
sign-symmetric support hypothesis. -/
-- Proof sketch: apply the canonical owner theorem
-- `smoothMaxInnerApproximation_mem_F11_positiveDefMatrixNorm` and then specialize the
-- `dualNorm_gradient_sub_le` consequence of `𝓕[L, p]¹¹`.
theorem smoothMaxInnerApproximation_gradient_lipschitz_diagonalWeightedNorm
    (ha_nonneg : ∀ i, a i ∈ nonnegativeOrthant n)
    (hDdiag : D.1.IsDiag)
    (hBoxSupport :
      ∀ v : E, v ∈ nonnegativeOrthant n →
        (ξ[signSymmetricConvexHull a] v).toReal ≤ 2 * Real.sqrt n * ‖v‖[D])
    (x y : E) :
    ‖∇ (smoothMaxInnerApproximation a μ) x - ∇ (smoothMaxInnerApproximation a μ) y‖[D,*] ≤
      ((4 : ℝ) * n / μ.1) * ‖x - y‖[D] := sorry

end

end

/-! ### Theorem_7_21 (from Chap07) -/
noncomputable section

open scoped PositiveDefMatrixNorm RelativeScaleTransformNotation

variable {n : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin (n : ℕ))

/- Theorem 7.21 lies in the chapter's relative-scale / positive-definite weighted-norm /
estimating-sequence domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` and the notations `‖·‖[G]`, `‖·‖[G,*]` in `Chap07/Definition_7_23`,
  the chapter owner for the primal and dual norms induced by a positive-definite matrix;
- `positiveDefMatrixNorm_quadraticDistanceTo_apply` in `Chap07/Definition_7_46`, the weighted
  quadratic-prox owner behind the term `(1 / 2) ‖x₀ - x*‖[G₀]^2`;
- `relativeScaleTransformedObjective` and the notation `f̂` in `Chap07/Lemma_7_20`, the chapter
  owner for the transformed objective `x ↦ (1 / 2) f(x)^2`;
- `estimating_function_le_weighted_transformed_objective_add_initial` in `Chap07/Lemma_7_21`,
  the nearby additive estimating-sequence recursion theorem.

Best owner abstraction:
- source-facing: Theorem 7.21's best-point and weighted-average bounds for the relative-scale
  high-order method;
- core/canonical: `positiveDefMatrixNorm`, `f̂`, and the accumulated-weight sequence `A`;
- bridge/view: the explicit exponential lower bound on `A_{k+1}` coming from the preceding
  quasi-Newton metric analysis.

Primitive data:
- the objective `f`, the positive-definite metric `G₀`, the base point `x₀`, and the comparison
  point `x*`;
- the source-facing sequences `x_k^*`, `\tilde x_k`, and `A_k`;
- the positive dimension `n : ℕ+`, the scalar parameter `δ`, and the positive smoothness owner
  `L : NNRealˣ`.

Derived API:
- the transformed-objective bound for the best points `x_k^*`;
- the parallel transformed-objective bound for the weighted-average points `\tilde x_{k+1}`.

The previous version rebuilt theorem-local primal and dual norm owners and packaged the three
source sequences into a second wrapper structure. This refinement reuses the Chapter 7 weighted
norm owner directly and keeps the primitive sequences separate from the scalar side conditions and
one-step estimates that drive the theorem.
-/

section RelativeScaleHighOrderMethod

variable {f : E → ℝ}
variable {G0 : {G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // G.PosDef}}
variable {x0 xStar : E} {δ : ℝ} {L : NNRealˣ}
variable {A : ℕ → ℝ}

-- Proof sketch: combine the one-step estimate for `x_k^*` with the lower bound on `A_{k+1}`,
-- then substitute `R = ‖x₀ - x⋆‖_{G₀}` and simplify the reciprocal factor.
/-- Theorem 7.21: for the high-order method in relative scale, if `\hat f(x) = (1 / 2) f(x)^2`,
the quasi-Newton estimating-sequence analysis provides the standard one-step bound for the best
points `x_k^*` together with the exponential lower bound on `A_{k+1}`, then
`(1 - δ) \hat f(x_k^*) ≤ \hat f(x^*) + L^2 ‖x₀ - x^*‖_{G₀}^2 /
  (2 n (e^{δ (k + 1) / n} - 1))` for every `δ > 0`. -/
theorem relativeScaleHighOrderMethod_best_point_bound
    {xBest : ℕ → E}
    (hδ : 0 < δ)
    (hbest :
      ∀ k : ℕ,
        (1 - δ) * f̂ (xBest k) ≤
          f̂ xStar + (‖x0 - xStar‖[G0] ^ (2 : ℕ)) / (2 * A (k + 1)))
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    (1 - δ) * f̂ (xBest k) ≤
      f̂ xStar +
        (((L : ℝ) ^ (2 : ℕ)) * ‖x0 - xStar‖[G0] ^ (2 : ℕ)) /
          (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)) := sorry

-- Proof sketch: apply the same argument as for the best-point estimate, now starting from the
-- one-step inequality for the weighted-average points `\tilde x_{k+1}`.
/-- The weighted-average points satisfy the same transformed-objective estimate as the best
points, with `x_k^*` replaced by `\tilde x_{k+1}`. -/
theorem relativeScaleHighOrderMethod_weighted_average_bound
    {xTilde : ℕ → E}
    (hδ : 0 < δ)
    (hweighted :
      ∀ k : ℕ,
        (1 - δ) * f̂ (xTilde (k + 1)) ≤
          f̂ xStar + (‖x0 - xStar‖[G0] ^ (2 : ℕ)) / (2 * A (k + 1)))
    (hA_lower :
      ∀ k : ℕ,
        ((n : ℝ) / ((L : ℝ) ^ (2 : ℕ))) *
            (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) ≤
          A (k + 1))
    (k : ℕ) :
    (1 - δ) * f̂ (xTilde (k + 1)) ≤
      f̂ xStar +
        (((L : ℝ) ^ (2 : ℕ)) * ‖x0 - xStar‖[G0] ^ (2 : ℕ)) /
          (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)) := sorry

end RelativeScaleHighOrderMethod

end
