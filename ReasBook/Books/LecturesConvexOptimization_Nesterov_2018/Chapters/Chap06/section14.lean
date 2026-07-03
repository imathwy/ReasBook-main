

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_14 (from Chap06) -/
noncomputable section

open scoped BigOperators
open scoped StandardSimplex

/- Definition 6.14 lies in the finite simplex / entropic prox-geometry domain.

Sampled owner declarations:
* project `EuclideanSpace.l1Seminorm`, the canonical coordinate `ℓ₁` seminorm on `ℝⁿ`;
* project `EuclideanSpace.l1Seminorm_apply`, the coordinate formula for that owner;
* project `entropyFunction`, the canonical entropy owner on `Fin n → ℝ`;
* project `entropyFunction_apply`, the coordinate expansion of that owner.

Best owner abstraction:
* source-facing: the normalized entropy prox-function on the simplex `Δ[n]`;
* core/canonical: `EuclideanSpace.l1Seminorm` for the ambient geometry and `entropyFunction` for
  the entropy term;
* bridge/view: restricting `x ↦ log n + entropyFunction n x` to the simplex subtype `Δ[n]`.

Primitive data:
* the positive dimension `n : ℕ+`.

Derived API:
* the pointwise formula for the normalized entropy prox-function on `Δ[n]`;
* the textbook use of `EuclideanSpace.l1Seminorm (n : ℕ)` and
  `EuclideanSpace.l1Seminorm (m : ℕ)` as the ambient norms on `ℝⁿ` and `ℝᵐ`.

Source/core/bridge triage:
* source-facing: `normalizedEntropyProxFunction`;
* core/canonical: `EuclideanSpace.l1Seminorm` and `entropyFunction`;
* bridge/view: this file, which keeps the simplex-subtype prox function but deletes the duplicate
  bundled prox-structure wrapper.
-/

/-- Definition 6.14: on the standard simplex `Δ_n`, the entropy prox-function is
`x ↦ log n + ∑ᵢ xᵢ log xᵢ`; the ambient norm is the canonical coordinate `ℓ₁` seminorm
`EuclideanSpace.l1Seminorm (n : ℕ)`. The same owner specializes to the textbook pair
`(d₁, d₂)` by using the dimensions `n` and `m`. -/
def normalizedEntropyProxFunction (n : ℕ+) : Δ[n] → ℝ :=
  fun x ↦ Real.log (n : ℝ) + entropyFunction (n : ℕ) x

/-- The ambient norm from Definition 6.14 is the canonical coordinate `ℓ₁` seminorm on `ℝⁿ`,
written in textbook form as the sum of the coordinate absolute values. -/
-- Proof sketch: specialize `EuclideanSpace.l1Seminorm_apply` to real coordinates and rewrite
-- `‖x i‖` as `|x i|`.
theorem l1Seminorm_eq_sum_abs (n : ℕ+) (x : EuclideanSpace ℝ (Fin (n : ℕ))) :
    EuclideanSpace.l1Seminorm (n : ℕ) x = ∑ i : Fin (n : ℕ), |x i| := sorry

/-- Evaluating `normalizedEntropyProxFunction n` gives the textbook formula
`log n + ∑ᵢ xᵢ log xᵢ` on `Δ_n`. -/
-- Proof sketch: unfold `normalizedEntropyProxFunction` and then expand `entropyFunction`
-- coordinatewise using `entropyFunction_apply`.
theorem normalizedEntropyProxFunction_apply (n : ℕ+) (x : Δ[n]) :
    normalizedEntropyProxFunction n x =
      Real.log (n : ℝ) + ∑ i : Fin (n : ℕ), x i * Real.log (x i) := sorry

/-! ### Lemma_6_14 (from Chap06) -/
open Matrix
open RealSymmetricMatrixSpace
open PositiveSemidefiniteCone
open scoped BigOperators MatrixOrder NNReal RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Lemma 6.14 lies in the chapter's symmetric-matrix/Frobenius spectral-calculus domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 5 `𝕊^n₊`, `PositiveSemidefiniteCone.nnrpow`, and the induced notation `X ^ p` on
  `𝕊^n₊` in `Definition_5_4_4_3`, the established positive-semidefinite owner and its intrinsic
  nonnegative-power bridge;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the established
  Frobenius owner `⟪·, ·⟫_F` on `𝕊^n`;
- mathlib `CFC.nnrpow`, the canonical ambient nonnegative-spectrum functional-calculus power.

Best owner abstraction:
- source-facing: the symmetric-matrix/Frobenius inequality of Lemma 6.14;
- core/canonical: the chapter carriers `𝕊^n`, `𝕊^n₊`, and `⟪·, ·⟫_F`;
- bridge/view: the ambient matrix real-power operation on a positive-semidefinite symmetric
  matrix, viewed back in `𝕊^n`.

Primitive data:
- nonnegative exponents `p q : ℝ≥0`;
- a positive-semidefinite symmetric matrix `X : 𝕊^n₊`;
- a symmetric direction `H : 𝕊^n`.

Derived API:
- the source-facing PSD power notation `X ^ p` on `𝕊^n₊`;
- the symmetric square `H ^ 2`.

Source/core/bridge triage:
- source-facing: Lemma 6.14 itself on symmetric matrices and the Frobenius pairing;
- core/canonical: `𝕊^n`, `𝕊^n₊`, `X ^ p` on `𝕊^n₊`, `⟪·, ·⟫_F`, and intrinsic eigenvalues on
  `𝕊^n`;
- bridge/view: the coercion from `𝕊^n₊` to `𝕊^n` and then to ambient matrices.

The refinement below reuses the chapter owner `X ^ p` on the intrinsic cone subtype `X : 𝕊^n₊`,
keeps the source-facing inequality on the single mixed trace term that appears in Proposition 6.33,
and does not export a separate owner for a one-off symmetrized package.
-/

-- Proof sketch: diagonalize the positive-semidefinite symmetric matrix `X` orthogonally, compare
-- the mixed power term entrywise using `a^p b^q ≤ a^(p+q)` on the nonnegative eigenvalues of `X`,
-- rewrite the resulting trace as the Frobenius pairing with `X^(p+q)` and
-- `H^2`, and then apply von Neumann's trace inequality to the positive semidefinite matrices
-- `X^(p+q)` and `H^2`.
/-- Lemma 6.14: for nonnegative exponents, a positive-semidefinite symmetric matrix `X`, and a
real symmetric matrix `H`, the single mixed trace term `trace (((X^p H X^q)ᵀ) H)` is bounded by
the Frobenius pairing of `X^(p+q)` with `H^2`, and this is in turn bounded by the pairing of the
eigenvalue vectors of `X^(p+q)` and `H^2`. -/
theorem frobenius_power_sandwich_bound
    (p q : ℝ≥0) (X : 𝕊^n₊) (H : SymmMat) :
    Matrix.trace
        (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat))
      ≤ ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F ∧
    ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
      ≤ ∑ i : Fin n, eigenvalues (X ^ (p + q) : 𝕊^n₊) i * eigenvalues (H ^ (2 : ℕ)) i :=
  sorry

/-! ### Proposition_6_14 (from Chap06) -/
open Matrix

noncomputable section

open scoped StandardSimplex
open scoped Matrix.Norms.L2Operator MatrixOrder

/- Proposition 6.14 lies in the finite simplex / entropy-smoothing / primal-dual gap domain.

Sampled owner declarations:
* `primal_dual_gap_bound_of_smoothed_lower_approximation` in `Lemma_6_12`, the chapter owner for
  the interval-valued raw primal-dual gap bound;
* `normalizedEntropyProxFunction` and
  `sSup_range_normalizedEntropyProxFunction_eq_log` in `Lemma_6_3`, the simplex entropy-prox owner
  and its maximal-value bridge;
* `l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self` in `Proposition_6_13`, the spectral
  bridge identifying the Euclidean operator norm with the displayed Gram-spectrum quantity.

Best owner abstraction:
* source-facing: the simplex matrix-game gap estimate written with the spectral right-hand side;
* core/canonical: interval membership `f xHat - φ uHat ∈ Set.Icc 0 bound`;
* bridge/view: the entropy-prox maximal value on `Δ[m]` and the operator-norm-to-spectrum rewrite.

Primitive data:
* the matrix `A`;
* the local lower-approximation bound at `xHat` with entropy budget
  `μ₂ * sSup (Set.range (normalizedEntropyProxFunction m))`;
* the pointwise inequalities `φ uHat ≤ fμ₂ xHat ≤ f xHat`;
* the residual smoothed gap bound `fμ₂ xHat - φ uHat ≤ r`;
* the chosen smoothing scale identifying that entropy budget with
  `4 ‖A‖ / √(N (N + 1))`.

Derived API:
* the operator-norm interval bound with residual term `r`;
* the spectral interval bound with residual term `r`;
* the paired-inequality companion form.

Source/core/bridge triage:
* source-facing: the spectral statement below;
* core/canonical: `primal_dual_gap_bound_of_smoothed_lower_approximation`;
* bridge/view: `sSup_range_normalizedEntropyProxFunction_eq_log` and
  `l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self`.

The previous version assumed the displayed spectral upper bound as a hypothesis and then returned
that same bound, which erased the actual simplex-smoothing content. The repaired version now
specializes the chapter's canonical raw-gap owner to the entropy-prox smoothing budget together
with the explicit residual smoothed-gap term, and uses the spectral theorem only as the final
rewrite step.
-/

-- Proof sketch: apply
-- `primal_dual_gap_bound_of_smoothed_lower_approximation` with
-- `D₂ = sSup (Set.range (normalizedEntropyProxFunction m))`. The simplex entropy-prox maximum is
-- nonnegative because it equals `log m`, and the assumed smoothing-scale identity rewrites the
-- upper endpoint to `4 ‖A‖ / √(N (N + 1))`.
section

variable {m n : ℕ+} (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ)
variable (f fμ₂ : Δ[n] → ℝ) (φ : Δ[m] → ℝ)
variable (N : ℕ) (xHat : Δ[n]) (uHat : Δ[m]) {μ₂ r : ℝ}

/-- The simplex matrix-game primal-dual gap lies in the canonical interval
`[0, 4 ‖A‖ / √(N (N + 1)) + r]` once the entropy-smoothing lower-approximation budget equals that
operator-norm quantity and the residual smoothed gap is bounded by `r`. -/
theorem simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_norm_bound
    (happrox :
      f xHat - μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) ≤ fμ₂ xHat)
    (hφ_le : φ uHat ≤ fμ₂ xHat)
    (hsmoothed_gap : fμ₂ xHat - φ uHat ≤ r)
    (hfμ₂_le : fμ₂ xHat ≤ f xHat)
    (hscale :
      μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) =
        (4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))
    :
    f xHat - φ uHat ∈ Set.Icc 0
      (((4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) + r) := by
  simpa [hscale] using
    (primal_dual_gap_bound_of_smoothed_lower_approximation
      happrox hφ_le hsmoothed_gap hfμ₂_le)

-- Proof sketch: first obtain the operator-norm interval bound above, then rewrite `‖A‖` by
-- `l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self`.
/-- Proposition 6.14: for the entropy-smoothed simplex matrix game, if the smoothing budget is
chosen so that
`μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) = 4 ‖A‖ / √(N (N + 1))`,
then the primal-dual gap at `(xHat, uHat)` lies in the interval whose upper endpoint is the
spectral quantity
`4 * sqrt (sSup (spectrum ℝ (Aᵀ * A))) / sqrt (N (N + 1)) + r`, provided the residual smoothed
gap `fμ₂ xHat - φ uHat` is bounded by `r`. -/
theorem simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_spectral_bound
    (happrox :
      f xHat - μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) ≤ fμ₂ xHat)
    (hφ_le : φ uHat ≤ fμ₂ xHat)
    (hsmoothed_gap : fμ₂ xHat - φ uHat ≤ r)
    (hfμ₂_le : fμ₂ xHat ≤ f xHat)
    (hscale :
      μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) =
        (4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))
    :
    f xHat - φ uHat ∈ Set.Icc 0
      ((4 * Real.sqrt (sSup (spectrum ℝ (Aᵀ * A)))) /
        Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) + r) := by
  simpa [l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self A] using
    simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_norm_bound
      A f fμ₂ φ N xHat uHat happrox hφ_le hsmoothed_gap hfμ₂_le hscale

/-- Proposition 6.14 in paired-inequality form: the simplex matrix-game primal-dual gap is
nonnegative and bounded above by the spectral entropy-smoothing estimate together with the
residual smoothed-gap term `r`. -/
theorem simplex_matrix_game_primalDualGap_nonneg_le_entropy_smoothing_spectral_bound
    (happrox :
      f xHat - μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) ≤ fμ₂ xHat)
    (hφ_le : φ uHat ≤ fμ₂ xHat)
    (hsmoothed_gap : fμ₂ xHat - φ uHat ≤ r)
    (hfμ₂_le : fμ₂ xHat ≤ f xHat)
    (hscale :
      μ₂ * sSup (Set.range (normalizedEntropyProxFunction m)) =
        (4 * ‖A‖) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)))
    :
    0 ≤ f xHat - φ uHat ∧
      f xHat - φ uHat ≤
        (4 * Real.sqrt (sSup (spectrum ℝ (Aᵀ * A)))) /
          Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) + r := by
  simpa [Set.mem_Icc] using
    simplex_matrix_game_primalDualGap_mem_Icc_of_entropy_smoothing_spectral_bound
      A f fμ₂ φ N xHat uHat happrox hφ_le hsmoothed_gap hfμ₂_le hscale

end

/-! ### Theorem_6_14 (from Chap06) -/
noncomputable section

open scoped BigOperators Gradient TotalVariationNotation WeightSequenceNotation

universe u

namespace ConditionalGradientContraction

section HolderGradient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `HolderGradientOn v Gv Q f g` records that the chosen dual field `g` represents the
within-set derivative of `f` on `Q` at every feasible point and is `v`-Hölder there with
constant `Gv`, using mathlib's canonical on-set Hölder owner `HolderOnWith`. -/
class HolderGradientOn
    (v Gv : NNReal) (Q : Set E) (f : E → ℝ) (g : E → StrongDual ℝ E) : Prop where
  hasFDerivWithinAt {x : E} (hx : x ∈ Q) : HasFDerivWithinAt f (g x) Q x
  holderOn : HolderOnWith Gv v g Q

namespace HolderGradientOn

theorem norm_sub_le
    {v Gv : NNReal} {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E}
    (hf : HolderGradientOn v Gv Q f g) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖g x - g y‖ ≤ (Gv : ℝ) * Real.rpow ‖x - y‖ (v : ℝ) := by
  simpa [dist_eq_norm] using hf.holderOn.dist_le hx hy

end HolderGradientOn

end HolderGradient

section LinearizedCompositeGap

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The extended-valued feasible-point bridge for the Chapter 6 linearized composite gap,
obtained by viewing the canonical restricted dual value of the real-valued lift of `Ψ` in
`EReal`. -/
abbrev linearizedCompositeGap
    (S : Set E) (Ψ : E → ℝ) (g : StrongDual ℝ E) (x0 : S) : EReal :=
  withTopToEReal
    (restrictedDualFunction S (fun x ↦ (Ψ x : WithTop ℝ))
      ⟨x0, by simp [withTopEffectiveDomain, x0.property]⟩ g)

end LinearizedCompositeGap

section TotalVariationBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- In the ambient-gradient specialization, the chosen-dual gap
`linearizedCompositeGap S Ψ g x₀` reduces to the Chapter 6 total-variation owner
`δ[S, f, Ψ](x₀)`. -/
theorem linearModelTotalVariation_eq_linearizedCompositeGap
    (S : Set E) (f Ψ : E → ℝ) (x0 : S) :
    δ[S, f, Ψ](x0) =
      linearizedCompositeGap S Ψ (InnerProductSpace.toDualMap ℝ E (∇ f x0)) x0 := sorry

end TotalVariationBridge

section ContractionErrorTerm

/-- The error quantity `C_{v,t}` attached to the scalar initial gap `Δ(x₀)`, the weights `a_t`,
the canonical accumulated weights `A_t = A[a](t)`, and the Hölder data `G_v` and `D`. This is
the source-facing specialization of `linearOptimizationOracleErrorBound`, with the factor
`(1 + v)⁻¹` absorbed into the Hölder constant. -/
abbrev contractionErrorTerm
    (Δ0 : ℝ) (a : ℕ → ℝ) (Gv D v : ℝ) (t : ℕ) : ℝ :=
  linearOptimizationOracleErrorBound Δ0 a (Gv / (1 + v)) D v t

namespace ContractionErrorNotation

/- Source-facing Lean notation for the Chapter 6 constant `C_{v,t}` with the ambient data fixed
by the surrounding context. -/
scoped notation:max "C[" Δ0 ", " a ", " Gv ", " D ", " v "](" t:arg ")" =>
  contractionErrorTerm Δ0 a Gv D v t

end ContractionErrorNotation

end ContractionErrorTerm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The estimating functional sequence `φ_t` generated from the weights `a_t`, the initial model
`\tilde f`, the smooth term `f`, the chosen dual gradient field, the regularizer `Ψ`, and the
iterate sequence `x_t`. -/
def estimatingFunctionalSequence
    (a : ℕ → ℝ) (tildeF : E → ℝ) (f : E → ℝ) (gradF : E → StrongDual ℝ E) (Ψ : E → ℝ)
    (xSeq : ℕ → E) : ℕ → E → ℝ
  | 0 => fun x ↦ a 0 * tildeF x
  | t + 1 => fun x ↦
      estimatingFunctionalSequence a tildeF f gradF Ψ xSeq t x +
        a (t + 1) *
          (f (xSeq t) + gradF (xSeq t) (x - xSeq t) + Ψ x)

namespace EstimatingFunctionNotation

/- Source-facing Lean notation for the Chapter 6 estimating sequence `φ_t(x)` with all ambient
data fixed explicitly. -/
scoped notation:max "φ[" a ", " tildeF ", " f ", " gradF ", " Ψ ", " xSeq "]("
    t:arg ", " x:arg ")" =>
  estimatingFunctionalSequence a tildeF f gradF Ψ xSeq t x

end EstimatingFunctionNotation

namespace ContractedFeasibleSetTrustRegionScheme

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- The estimating functional sequence `φ_t` attached to a contracted-feasible-set trust-region
scheme and an initial model `\tilde f`. -/
abbrev estimatingFunction
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    (a : ℕ → ℝ) (tildeF : E → ℝ) : ℕ → E → ℝ :=
  estimatingFunctionalSequence
    a tildeF problem.smoothPart method.gradient (withTopRealPart problem.nonsmoothPart) method

namespace EstimatingFunctionNotation

/- Source-facing Lean notation for the specialized estimating sequence `φ_t(x)` attached to
Algorithm 6.5. -/
scoped notation:max "φ[" method ", " a ", " tildeF "](" t:arg ", " x:arg ")" =>
  ContractedFeasibleSetTrustRegionScheme.estimatingFunction method a tildeF t x

end EstimatingFunctionNotation

end ContractedFeasibleSetTrustRegionScheme

open ContractedFeasibleSetTrustRegionScheme
open scoped ContractionErrorNotation EstimatingFunctionNotation

/- Theorem 6.14 lies in the Chapter 6 contracted conditional-gradient / estimating-sequence
domain.

Mandatory domain-style sampling:
- `accumulatedWeights` / `weightCoefficient` in `Definition_6_53`, the chapter owners of
  `A[a](t)` and `τ[a](t)`;
- `ContractedFeasibleSetTrustRegionScheme` in `Algorithm_6_5`, the source-facing owner of the
  iterate, step-size, and contracted-subproblem data;
- `linearizedCompositeGap` in this file, the chosen-dual Chapter 6 gap owner attached to the
  actual linear model used by Algorithm 6.5;
- `linearModelTotalVariation` in `Definition_6_59`, the Chapter 6 owner `δ[Q, f, Ψ](x)` of the
  ambient-gradient total variation at a feasible point;
- `linearOptimizationOracleErrorBound` in `Definition_6_53`, the canonical Chapter 6 owner whose
  specialization here is the source-facing error term `C_{v,t}`;
- `HolderGradientOn.upper_model` in `Proposition_6_39`, the nearby Hölder upper-model bridge used
  to control the smooth remainder.

Best owner abstraction:
- source-facing: Theorem 6.14's weighted estimating-function bound and the one-step decrease
  bound written with the chosen-dual gap `linearizedCompositeGap`;
- core/canonical: `ContractedFeasibleSetTrustRegionScheme`, `A[a](t)`, `τ[a](t)`,
  `linearOptimizationOracleErrorBound`, `HolderGradientOn`, and the ambient-gradient owner
  `linearModelTotalVariation`;
- bridge/view: `linearModelTotalVariation_eq_linearizedCompositeGap`, which identifies the
  chosen-dual owner with `δ[Q, f, Ψ](x)` only under an explicit ambient-gradient specialization.

Primitive data:
- the ambient composite problem and Algorithm 6.5 method data;
- the weight sequence `a`, together with the positivity condition `∀ t, 0 < a t` and the
  canonical coefficient identity `method.stepSize t = τ[a](t)`;
- the Hölder-gradient owner `HolderGradientOn` and the feasible-set diameter bound.

Derived API:
- the specialized estimating sequence `estimatingFunction`;
- the theorem-surface notation `φ[method, a, \tilde f](t, x)` for that specialized sequence;
- the source-facing Chapter 6 error term `contractionErrorTerm`, together with the theorem-surface
  notation `C[Δ₀, a, Gᵥ, D, v](t)`, both derived from `linearOptimizationOracleErrorBound`;
- the weighted objective upper bound, the chosen-dual decrease estimate below, and its ambient-
  gradient specialization through `linearModelTotalVariation_eq_linearizedCompositeGap`.

Source/core/bridge triage:
- source-facing: the two statements of Theorem 6.14;
- core/canonical: the chapter owners listed above, with Theorem 6.14 (2) surfaced through the
  actual chosen-dual linear model carried by `method.gradient`;
- bridge/view: `linearizedCompositeGap`, whose defining body is exactly the canonical
  `restrictedDualFunction` bridge, and `linearModelTotalVariation_eq_linearizedCompositeGap`,
  which specializes that chosen-dual owner to `δ[Q, f, Ψ](x_t)` when the ambient gradient really
  matches the chosen field.
-/

-- Proof sketch: prove the estimate by induction on `t`. For the induction step, unfold
-- `ContractedFeasibleSetTrustRegionScheme.estimatingFunction`, apply the contracted-subproblem
-- minimizing property from `Algorithm_6_5` at step `t` to the contracted point determined by the
-- comparison vector `x ∈ Q`, then use the Hölder upper-model bound coming from `hf_holder`
-- together with the positive-weight hypothesis `ha_pos`, the diameter bound `hdiam`, and the
-- weight identity `τ_t = a_{t+1} / A_{t+1}` to absorb the remainder into
-- `contractionErrorTerm`.
/-- Theorem 6.14 (1): along Algorithm 6.5, if the initial model `\tilde f` underestimates the
initial objective up to the scalar initial-gap term `Δ(x₀)` and the weights satisfy `a_t > 0`,
then for every Hölder exponent parameter `v : NNReal`, every index `t ≥ 0`, and every
comparison point `x ∈ Q`, one has
`A_t \bar f(x_t) ≤ φ_t(x) + C_{v,t}`. -/
theorem weighted_objective_le_estimatingFunction_add_contractionError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    (a : ℕ → ℝ) (tildeF : E → ℝ) (Δ0 : ℝ) {v Gv : NNReal} {D : ℝ}
    (hinitial :
      ∀ ⦃x : E⦄, x ∈ problem.feasibleSet →
        problem.smoothPart x0 + withTopRealPart problem.nonsmoothPart x0 ≤ tildeF x + Δ0)
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) {x : E} (hx : x ∈ problem.feasibleSet) :
      A[a](t) *
          (problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) ≤
        φ[method, a, tildeF](t, x) +
          C[Δ0, a, (Gv : ℝ), D, (v : ℝ)](t) := sorry

section LinearizedCompositeGapObjectiveDrop

-- Proof sketch: compare `x_{t+1}` with the contracted candidate `(1 - τ_t) x_t + τ_t y` in the
-- local minimizing property, identify the best comparison over `y ∈ Q` with the chosen-dual gap
-- `linearizedCompositeGap problem.feasibleSet (withTopRealPart problem.nonsmoothPart)
--   (method.gradient (method t)) (method.iterates t)`,
-- and then use the Hölder upper-model estimate from `hf_holder` plus the diameter control
-- `hdiam` to bound the remainder by
-- `(G_v D^(1+v) / (1+v)) τ_t^(1+v)`.
/-- Theorem 6.14 (2): at every step of Algorithm 6.5, the composite-objective decrease
`\bar f(x_t) - \bar f(x_{t+1})` is bounded below by the step size times the chosen-dual
linearized composite gap attached to the actual linear model used at `x_t`, minus the Hölder
remainder
`(G_v D^(1+v) / (1 + v)) τ_t^(1+v)`. -/
theorem objective_drop_ge_stepSize_mul_linearizedCompositeGap_sub_holderError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) :
      (((problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            linearizedCompositeGap problem.feasibleSet
              (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
              (method.iterates t) -
          (((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
              Real.rpow (method.stepSize t) (1 + (v : ℝ)) : ℝ) : EReal) := sorry

end LinearizedCompositeGapObjectiveDrop

section TotalVariationObjectiveDrop

variable [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: apply the chosen-dual decrease theorem above and then rewrite the gap term by the
-- supplied identification with the Chapter 6 total-variation owner. This identification is the
-- one induced, for example, by `linearModelTotalVariation_eq_linearizedCompositeGap` when the
-- chosen derivative field really is the ambient gradient at `x_t`.
/-- Under the additional hypothesis that the chosen-dual gap used by Algorithm 6.5 agrees at
`x_t` with the Chapter 6 total-variation owner `δ[Q, f, Ψ](x_t)` (for instance because the chosen
derivative field agrees there with the ambient gradient), Theorem 6.14 (2) specializes to the
ambient-gradient total-variation form. -/
theorem objective_drop_ge_stepSize_mul_totalVariation_sub_holderError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ)
    (hgap :
      linearizedCompositeGap problem.feasibleSet
          (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
          (method.iterates t) =
        δ[problem.feasibleSet, problem.smoothPart,
          withTopRealPart problem.nonsmoothPart]((method.iterates t))) :
      (((problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            (δ[problem.feasibleSet, problem.smoothPart,
              withTopRealPart problem.nonsmoothPart]((method.iterates t))) -
          (((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
              Real.rpow (method.stepSize t) (1 + (v : ℝ)) : ℝ) : EReal) := by
  have hdrop :=
    objective_drop_ge_stepSize_mul_linearizedCompositeGap_sub_holderError
      method hf_holder hdiam t
  simpa [hgap] using hdrop

end TotalVariationObjectiveDrop

end ConditionalGradientContraction

end
