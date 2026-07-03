import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_3_1 (from Chap06) -/
/- Corollary 6.3.1 lies in the chapter's symmetric-matrix trace-power / Hessian spectral domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the source-facing trace-power
  owner on `𝕊^n`;
- Chapter 6 `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing` in `Theorem_6_9`, the
  canonical Hessian quadratic-form bound for that owner;
- mathlib `iteratedFDeriv`, `CFC.abs`, and Hermitian eigenvalues as the ambient calculus and
  spectral owners.

Best owner abstraction:
- source-facing: the Hessian quadratic-form estimate for `π_k(X) = Trace (X^k)` on the symmetric
  matrix space `𝕊^n`;
- core/canonical: `π[k]`, `iteratedFDeriv`, `CFC.abs`, and
  `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing`;
- bridge/view: any ambient-matrix reformulation with extra symmetry hypotheses.

Primitive data:
- `k : ℕ`;
- `X H : 𝕊^n`.

Derived API:
- the source-facing owner `π[k]`;
- the canonical Hessian estimate
  `powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing`.

Source/core/bridge triage:
- source-facing: Corollary 6.3.1's Hessian inequality for the trace-power quantity;
- core/canonical: the owner theorem in `Theorem_6_9`;
- bridge/view: the discarded ambient `Matrix` restatement with `IsSymm` assumptions.

This file previously rebuilt ambient matrix normed-space instances and restated the same result
under a parallel local theorem name. Corollary 6.3.1 adds no new mathematics beyond the canonical
symmetric-matrix owner theorem, so this file is now a pure recall item.
-/

/- Corollary 6.3.1 is the canonical symmetric-matrix Hessian estimate from `Theorem_6_9`. -/
recall powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing

/-! ### Definition_6_3 (from Chap06) -/
noncomputable section

open Metric

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 6.3 lies in the operator-norm / dual-pairing domain for dual-valued continuous
linear maps between real normed spaces.

Primary domain:
- operator norms of continuous linear maps `E₁ →L[ℝ] StrongDual ℝ E₂`
- dual-pairing support formulas on unit spheres

Sampled owner-style declarations:
- mathlib `ContinuousLinearMap.opNorm`
- mathlib `ContinuousLinearMap.sSup_sphere_eq_norm`
- project `dual_norm_eq_sSup_closedUnitBall` in `Chap04/Definition_4_4_4`
- project `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing` and
  `Seminorm.primalDualOperatorNorm_normSeminorm_eq_opNorm` in `Chap02/Definition_2_32`

Best owner abstraction:
- core/canonical: the ambient norm `‖·‖ : (E₁ →L[ℝ] StrongDual ℝ E₂) → ℝ`

Primitive data:
- a continuous linear map `A : E₁ →L[ℝ] StrongDual ℝ E₂`

Derived API:
- the one-sphere norm formula `ContinuousLinearMap.sSup_sphere_eq_norm`
- the two-ball pairing formula from `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`
- the textbook two-sphere pairing formula as a source-facing bridge

Source/core/bridge triage:
- source-facing: the textbook max/sup formula over `sphere (0 : E₁) 1 × sphere (0 : E₂) 1`
- core/canonical: `ContinuousLinearMap.opNorm`
- bridge/view: rewriting the canonical norm as the two-sphere dual-pairing supremum

This item is therefore refined so that the main entry is the canonical operator norm owner, while
the textbook two-sphere formula remains only as a companion bridge theorem. -/

/- Definition 6.3: the textbook operator norm `‖A‖_{1,2}` of a dual-valued map
`A : E₁ → E₂*` is the canonical ambient norm on `E₁ →L[ℝ] StrongDual ℝ E₂`. -/
#check (‖·‖ : (E₁ →L[ℝ] StrongDual ℝ E₂) → ℝ)

/- The unit-sphere formula for the codomain norm of `A` is already the canonical mathlib bridge
from the owner `‖A‖` to a source-facing supremum. -/
recall ContinuousLinearMap.sSup_sphere_eq_norm

-- Proof sketch: combine mathlib's one-sphere operator-norm formula for `A` with the chapter's
-- closed-unit-ball dual-norm formula for each `A x`, then pass from closed balls to spheres by
-- radial rescaling and identify the iterated supremum with the supremum over the product of unit
-- spheres.
/-- Companion bridge for Definition 6.3: the canonical operator norm of a dual-valued continuous
linear map is the supremum of the dual pairing over the product of the unit spheres; under the
textbook finite-dimensional hypotheses, this supremum is a maximum. -/
theorem operatorNorm_eq_sSup_dualPairing_unitSpheres (A : E₁ →L[ℝ] StrongDual ℝ E₂) :
    ‖A‖ =
      sSup ((fun xu : E₁ × E₂ ↦ A xu.1 xu.2) ''
        Set.prod (sphere (0 : E₁) 1) (sphere (0 : E₂) 1)) := sorry

end

/-! ### Lemma_6_3 (from Chap06) -/
noncomputable section

open scoped BigOperators
open scoped StandardSimplex

/- Lemma 6.3 lives in the finite simplex / entropy prox-geometry domain.

Sampled owner declarations:
* mathlib `stdSimplex`, via the Chapter 6 notation `Δ[n]`;
* mathlib `stdSimplex.barycenter` and `stdSimplex.barycenter_apply`, the canonical simplex center;
* project `entropyFunction` in `Chap02/Proposition_2_5`, the entropy owner on `Fin n → ℝ`;
* project `simplexL1Seminorm` and
  `entropyFunction_strongConvexOnWith_l1_stdSimplex` in `Chap02/Proposition_2_5`, the owner
  strong-convexity API on `Δ[n]`;
* project `EuclideanSpace.l1Seminorm` and
  `EuclideanSpace.entropyFunction_strongConvexOnWith_l1_preimage_stdSimplex` in
  `Chap02/Proposition_2_5`, the Euclidean-coordinate bridge;
* project `normalizedEntropyProxFunction` in `Chap06/Definition_6_14`.

Best owner abstraction:
* source-facing: the three textbook entropy-prox facts of Lemma 6.3, evaluated at the simplex
  center `(1 / n) \bar e_n`;
* core/canonical: `Δ[n]`, `stdSimplex.barycenter`, `entropyFunction`,
  `normalizedEntropyProxFunction`, `simplexL1Seminorm`, `StrongConvexOnWith`, and `IsGreatest`;
* bridge/view: the Euclidean-coordinate realization of the canonical simplex barycenter and the
  Euclidean pullback of the simplex owner theorem.

Primitive data:
* the positive dimension `n : ℕ+`;
* the canonical simplex barycenter `(stdSimplex.barycenter : Δ[n])`.

Derived API:
* the Euclidean-coordinate bridge `stdSimplexBarycenterEuclidean`;
* the simplex-owner strong-convexity theorem for the ambient normalized entropy formula on
  `Δ[n]`;
* the Euclidean-coordinate bridge theorem for that owner statement;
* the value-at-center and maximal-value statements for `normalizedEntropyProxFunction`.

Source/core/bridge triage:
* source-facing: the three entropy-prox statements from Lemma 6.3;
* core/canonical owners reused directly: `Δ[n]`, `stdSimplex.barycenter`, `entropyFunction`,
  `normalizedEntropyProxFunction`, `simplexL1Seminorm`, `StrongConvexOnWith`, and `IsGreatest`;
* bridge/view kept here: `stdSimplexBarycenterEuclidean` and the Euclidean-coordinate transport of
  the simplex owner theorem.

The previous local duplicates `probabilitySimplex`, `simplexEntropyProxFunction`, and
`IsOneStronglyConvexOnProbabilitySimplex` have been deleted. Their mathematical content is already
owned canonically upstream by the simplex owner `Δ[n]`, the entropy owner `entropyFunction`, the
normalized entropy prox owner `normalizedEntropyProxFunction`, and the seminorm-based strong
convexity owner `StrongConvexOnWith`.
-/

/-- The Euclidean-coordinate realization of the canonical barycenter of `Δ_n`. -/
abbrev stdSimplexBarycenterEuclidean (n : ℕ+) : EuclideanSpace ℝ (Fin (n : ℕ)) :=
  (EuclideanSpace.equiv (Fin (n : ℕ)) ℝ).symm (stdSimplex.barycenter : Δ[n])

-- Proof sketch: Proposition 2.5 gives the owner strong-convexity statement for `entropyFunction`
-- on `Δ[n]`; adding the constant `log n` yields the ambient formula whose restriction to `Δ[n]`
-- is `normalizedEntropyProxFunction n`.
/-- Lemma 6.3 (1): on the simplex owner `Δ_n`, the ambient normalized entropy formula underlying
`normalizedEntropyProxFunction n` is `1`-strongly convex with respect to the canonical `ℓ₁`
seminorm. -/
theorem normalizedEntropyProxFunction_strongConvexOnWith_l1_stdSimplex (n : ℕ+) :
    StrongConvexOnWith
      (simplexL1Seminorm (n : ℕ)) 1
      Δ[n]
      (fun x ↦ Real.log (n : ℝ) + entropyFunction (n : ℕ) x) := sorry

-- Proof sketch: transport the simplex-owner strong-convexity statement along the coordinate
-- equivalence `EuclideanSpace.equiv (Fin n) ℝ`.
/-- Euclidean-coordinate bridge for Lemma 6.3 (1). -/
theorem normalizedEntropyProxFunction_strongConvexOnWith_l1_preimage_stdSimplex (n : ℕ+) :
    StrongConvexOnWith
      (EuclideanSpace.l1Seminorm (n : ℕ)) 1
      ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n])
      (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) ↦
        Real.log (n : ℝ) +
          entropyFunction (n : ℕ) ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) x)) := sorry

-- Proof sketch: evaluate the normalized entropy prox-function at the canonical simplex barycenter;
-- the entropy sum consists of `n` equal terms `(1 / n) * log (1 / n)`, and the added `log n`
-- cancels the total.
/-- Lemma 6.3 (2): the normalized entropy prox-function vanishes at the canonical barycenter
`(1 / n) \bar e_n` of `Δ_n`. -/
theorem normalizedEntropyProxFunction_barycenter_eq_zero (n : ℕ+) :
    normalizedEntropyProxFunction n (stdSimplex.barycenter : Δ[n]) = 0 := sorry

-- Proof sketch: the entropy contribution is nonpositive on `Δ[n]`, so
-- `normalizedEntropyProxFunction n x ≤ log n` for all simplex points `x`; equality is attained at
-- any simplex vertex.
/-- Lemma 6.3 (3): the normalized entropy prox-function has maximal value `log n` on `Δ_n`. -/
theorem isGreatest_range_normalizedEntropyProxFunction_eq_log (n : ℕ+) :
    IsGreatest (Set.range (normalizedEntropyProxFunction n)) (Real.log (n : ℝ)) := sorry

/-- The supremum of the normalized entropy prox-function on `Δ_n` is `log n`. -/
theorem sSup_range_normalizedEntropyProxFunction_eq_log (n : ℕ+) :
    sSup (Set.range (normalizedEntropyProxFunction n)) = Real.log (n : ℝ) := by
  simpa using (isGreatest_range_normalizedEntropyProxFunction_eq_log n).csSup_eq

/-! ### Proposition_6_3 (from Chap06) -/
universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E₁ : Type v} {E₂ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

section

set_option linter.hashCommand false

/- Proposition 6.3 lies in the dual-valued operator-norm / transpose domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.flip`
- `ContinuousLinearMap.flip_apply`
- `ContinuousLinearMap.opNorm_flip`
- `ContinuousLinearMap.le_opNorm`

Best owner abstraction:
- source-facing: the adjoint/transposed operator `A* : E₂ → E₁*` of a dual-valued operator
  `A : E₁ → E₂*`;
- core/canonical: `A.flip`;
- bridge/view: rewriting the norm bound for `A.flip`
  with the canonical identity `‖A.flip‖ = ‖A‖`.

This item therefore keeps the norm identity as a direct recall of the canonical owner theorem and
adds only the source-facing estimate whose constant is rewritten from `‖A.flip‖` to `‖A‖`. -/

/- Proposition 6.3: the canonical transpose `A.flip` of a dual-valued continuous linear map has
the same operator norm as `A`. -/
#check (ContinuousLinearMap.opNorm_flip :
  ∀ A : E₁ →L[𝕜] StrongDual 𝕜 E₂, ‖A.flip‖ = ‖A‖)

/- Evaluating the canonical transpose gives the defining dual-pairing identity
`(A.flip u) x = (A x) u`. -/
#check (ContinuousLinearMap.flip_apply :
  ∀ (A : E₁ →L[𝕜] StrongDual 𝕜 E₂) (x : E₁) (u : E₂), (A.flip u) x = (A x) u)

/- The first operator-norm estimate in Proposition 6.3 is the canonical bound
`ContinuousLinearMap.le_opNorm` applied to `A`. -/
#check (ContinuousLinearMap.le_opNorm :
  ∀ (A : E₁ →L[𝕜] StrongDual 𝕜 E₂) (x : E₁), ‖A x‖ ≤ ‖A‖ * ‖x‖)

-- Proof sketch: apply `ContinuousLinearMap.le_opNorm` to `A.flip`, then rewrite the operator norm
-- with `ContinuousLinearMap.opNorm_flip`.
/-- Applying the operator-norm estimate to the canonical transpose `A.flip` gives the adjoint
bound with the same constant `‖A‖`. -/
theorem norm_flip_apply_le_opNorm
    (A : E₁ →L[𝕜] StrongDual 𝕜 E₂) (u : E₂) :
    ‖A.flip u‖ ≤ ‖A‖ * ‖u‖ := by
  simpa using A.flip.le_opNorm u

end

/-! ### Theorem_6_3 (from Chap06) -/
noncomputable section

open scoped BigOperators

universe u v

variable {E₁ : Type u} {E₂ : Type v}

/- Theorem 6.3 lies in the Chapter 6 smoothing / primal-dual gap domain.

Sampled owner-style declarations:
- `Finset.centerMass` and `Finset.centerMass_eq_of_sum_1`, the canonical owners for a finite
  normalized weighted average and its finite-sum expansion;
- `primal_dual_gap_bound_of_smoothed_lower_approximation` in `Lemma_6_12`, the chapter owner for
  recording a raw primal-dual gap bound canonically as interval membership in `Set.Icc`;
- `scaled_smoothing_parameter_product_eq` in `Proposition_6_28`, the chapter's algebraic owner for
  simplifying the optimized smoothing-parameter substitution.

Best owner abstraction:
- source-facing: Theorem 6.3's explicit weight family, weighted dual iterate `\hat u_N`, and
  optimized smoothing parameter `μ(N)`;
- core/canonical: `Finset.centerMass` for `\hat u_N` and raw interval membership
  `f x_N - φ(\hat u_N) ∈ Set.Icc 0 bound` for the primal-dual gap;
- bridge/view: the explicit coefficient formula
  `2 (i + 1) / ((N + 1) (N + 2))` for the weight family.

Primitive data:
- the explicit finite weight family on `Fin (N + 1)`;
- the chosen smoothing parameter `μ(N)` at a positive iteration count `N`;
- the smoothed objective value `fμ x_N` together with its pointwise lower-approximation at `x_N`
  and residual-gap bounds.

Derived API:
- the normalized weighted-average realization of `\hat u_N` through `Finset.centerMass`;
- the source finite-sum expansion of that weighted average;
- the canonical interval-valued gap bounds.

Source/core/bridge triage:
- source-facing: the explicit model weights, the weighted dual iterate `\hat u_N`, and the
  optimized Theorem 6.3 gap estimate;
- core/canonical: `Finset.centerMass` and `Set.Icc`;
- bridge/view: the explicit coefficient formula and finite-sum expansion.

The previous version kept parallel local public wrappers for the averaged dual iterate and the raw
gap. This refinement deletes those wrappers, reuses the chapter's weighted-average owner directly,
and restores Theorem 6.3 as a source-facing smoothing statement rather than an algebraic
post-processing lemma on an already packaged raw gap bound. -/

/-- The weight family
`a_i^(N) = 2 (i + 1) / ((N + 1) (N + 2))`
used in the weighted dual iterate `\hat u_N` of Theorem 6.3. -/
def explicitModelDualAverageWeights (N : ℕ) : Fin (N + 1) → ℝ :=
  fun i ↦ (2 * (((i : ℕ) : ℝ) + 1)) / (((N : ℝ) + 1) * ((N : ℝ) + 2))

-- Proof sketch: unfold `explicitModelDualAverageWeights`.
/-- Evaluating `explicitModelDualAverageWeights N` at `i` recovers the textbook coefficient
`2 (i + 1) / ((N + 1) (N + 2))`. -/
theorem explicitModelDualAverageWeights_apply (N : ℕ) (i : Fin (N + 1)) :
    explicitModelDualAverageWeights N i =
      (2 * (((i : ℕ) : ℝ) + 1)) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) :=
  rfl

-- Proof sketch: sum the arithmetic progression `1 + 2 + ··· + (N + 1)` and divide by
-- `((N + 1) (N + 2)) / 2`.
/-- The explicit-model weights form a normalized weight family. -/
theorem explicitModelDualAverageWeights_sum_eq_one (N : ℕ) :
    ∑ i, explicitModelDualAverageWeights N i = 1 := by
  sorry

-- Proof sketch: apply `Finset.centerMass_eq_of_sum_1` and use
-- `explicitModelDualAverageWeights_sum_eq_one`.
/-- The center of mass with `explicitModelDualAverageWeights N` is the source finite sum
`\hat u_N = Σ_{i=0}^N 2 (i + 1) / ((N + 1) (N + 2)) u_i`. -/
theorem centerMass_explicitModelDualAverageWeights_eq_sum
    [AddCommGroup E₂] [Module ℝ E₂]
    (N : ℕ) (u : Fin (N + 1) → E₂) :
    Finset.univ.centerMass (explicitModelDualAverageWeights N) u =
      ∑ i, explicitModelDualAverageWeights N i • u i := by
  simpa using
    (Finset.univ.centerMass_eq_of_sum_1 u (explicitModelDualAverageWeights_sum_eq_one N))

section ExplicitModelSmoothing

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The smoothing parameter
`μ(N) = 2 ‖A‖ / √(N (N + 1)) * √(D₁ / D₂)`
chosen in Theorem 6.3. -/
def explicitModelSmoothingParameter
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+) : ℝ :=
  (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ / D₂)

-- Proof sketch: unfold `explicitModelSmoothingParameter`.
/-- Evaluating `explicitModelSmoothingParameter` recovers the displayed formula for `μ(N)`. -/
theorem explicitModelSmoothingParameter_def
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (D₁ D₂ : ℝ) (N : ℕ+) :
    explicitModelSmoothingParameter A D₁ D₂ N =
      (2 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ / D₂) :=
  rfl

-- Proof sketch: write
-- `f x_N - φ(\hat u_N) = (f x_N - fμ x_N) + (fμ x_N - φ(\hat u_N))`.
-- The smoothing lower-approximation bounds the first term by `μ(N) D₂`, while the source
-- residual hypothesis bounds the second term. The lower bound comes from
-- `φ(\hat u_N) ≤ fμ x_N ≤ f x_N`.
/-- Companion source-facing bridge for Theorem 6.3: if the smoothed value `fμ x_N` lies between
`φ(\hat u_N)` and `f x_N`, if the lower smoothing estimate at `x_N` has error at most `μ(N) D₂`,
and if the residual smoothed gap is bounded by the model term
`4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))`, then the raw primal-dual gap at
`(x_N, \hat u_N)` lies in the interval
`[0, μ(N) D₂ + 4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))]`. -/
theorem explicitModelPrimalDualGap_mem_Icc_of_smoothed_gap_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M : ℝ)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
      (explicitModelSmoothingParameter A D₁ D₂ N * D₂ +
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) := by
  sorry

-- Proof sketch: first apply `explicitModelPrimalDualGap_mem_Icc_of_smoothed_gap_bound`.
-- Then substitute the explicit choice of `μ(N)` and simplify the first two upper-bound terms to
-- `4 ‖A‖ √(D₁ D₂) / √(N (N + 1))`, using the chapter's algebraic owner
-- `scaled_smoothing_parameter_product_eq`.
/-- Theorem 6.3: let
`μ(N) = 2 ‖A‖ / √(N (N + 1)) * √(D₁ / D₂)` and
`\hat u_N = Finset.univ.centerMass (explicitModelDualAverageWeights N) u`.
If `φ(\hat u_N) ≤ fμ x_N ≤ f x_N`, if `fμ` is a lower smoothing of `f` with error at most
`μ(N) D₂` at `x_N`, and if the smoothed residual gap at `(x_N, \hat u_N)` is bounded by
`4 ‖A‖² D₁ / (μ(N) N (N + 1)) + 4 M D₁ / (N (N + 1))`,
then
`0 ≤ f(x_N) - φ(\hat u_N) ≤ 4 ‖A‖ √(D₁ D₂) / √(N (N + 1)) + 4 M D₁ / (N (N + 1))`. -/
theorem optimized_primal_dual_gap_bound_for_explicit_model_smoothing
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f fμ : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 < D₂)
    (hxN_approx :
      fμ xN ≥ f xN - explicitModelSmoothingParameter A D₁ D₂ N * D₂)
    (hφ_le : φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ fμ xN)
    (hfμ_le : fμ xN ≤ f xN)
    (hsmoothed_gap :
      fμ xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤
        (4 * ‖A‖ ^ (2 : ℕ) * D₁) /
            (explicitModelSmoothingParameter A D₁ D₂ N * ((N : ℝ) * ((N : ℝ) + 1))) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
      ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
        (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))) := by
  sorry

-- Proof sketch: combine the optimized interval bound with the hypothesis
-- `4 ‖A‖ √(D₁ D₂) / ε + 2 √(M D₁ / ε) ≤ N`, then check that the right-hand side of the bound is
-- at most `ε`.
/-- If the iteration count dominates the Theorem 6.3 complexity expression, then the weighted
dual iterate `\hat u_N` and the primal iterate `x_N` form an `ε`-accurate primal-dual pair. -/
theorem primal_dual_gap_le_epsilon_of_iteration_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (f : E₁ → ℝ) (φ : E₂ → ℝ)
    (N : ℕ+) (xN : E₁) (u : Fin ((N : ℕ) + 1) → E₂)
    (D₁ D₂ M ε : ℝ) (hε : 0 < ε)
    (hgap :
      f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ∈ Set.Icc 0
        ((4 * ‖A‖ / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) * Real.sqrt (D₁ * D₂) +
          (4 * M * D₁) / ((N : ℝ) * ((N : ℝ) + 1))))
    (hiter :
      (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ε + 2 * Real.sqrt (M * D₁ / ε) ≤ (N : ℝ)) :
    f xN - φ (Finset.univ.centerMass (explicitModelDualAverageWeights N) u) ≤ ε := by
  sorry

end ExplicitModelSmoothing

end
