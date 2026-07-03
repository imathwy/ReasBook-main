import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_11 (from Chap07) -/
noncomputable section

open scoped SupportFunction WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 7.11 lies in the support-function / subdifferential geometry of convex bodies.

Primary domain:
- support functions of convex bodies and the Euclidean radii of their subdifferentials at `0`

Sampled owner-style declarations:
- `ConvexBody` from mathlib
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`
- `subdifferentialWithin` with notation `∂[Q] f(x)` in `Chap03/Theorem_3_44`

Best owner abstraction:
- `ConvexBody E`

Primitive data:
- a convex body `Q₂ : ConvexBody E`

Derived API:
- the real-valued support-function bridge `Q₂.supportFunctionReal`
- the source-facing set `∂F(0)` as `Q₂.supportFunctionSubdifferentialAtZero`
- the radii sets `γ₀`, `γ₁`, and the ratio `α`

Source/core/bridge triage:
- source-facing: the radii and relative-scale ratio attached to the support function of `Q₂`
- core/canonical: `ConvexBody`, `ξ[Q]`, and `∂[Q] f(x)`
- bridge/view: `supportFunctionReal` and `supportFunctionSubdifferentialAtZero`

The previous file duplicated both the support-function owner and the real-valued unconstrained
subdifferential owner, and it packaged the convex-body data in a second wrapper structure whose
interior assumption never entered the definitions. This refinement keeps the source-facing radii
and ratio, but moves the public owner to `ConvexBody E` and derives the rest from the existing
chapter API.
-/

namespace ConvexBody

/-- The real-valued support function of the convex body `Q₂`, obtained from the Chapter 3 owner
`ξ[Q₂] : E → EReal` by the canonical `toReal` bridge. For convex bodies this matches the textbook
finite support value. -/
abbrev supportFunctionReal (Q2 : ConvexBody E) : E → ℝ :=
  fun v ↦ (ξ[(Q2 : Set E)] v).toReal

@[simp] theorem supportFunctionReal_apply (Q2 : ConvexBody E) (v : E) :
    Q2.supportFunctionReal v = (ξ[(Q2 : Set E)] v).toReal :=
  rfl

/-- The subdifferential `∂F(0)` of the real-valued support function of `Q₂`. -/
abbrev supportFunctionSubdifferentialAtZero (Q2 : ConvexBody E) : Set E :=
  subdifferentialWithin (Set.univ : Set E) Q2.supportFunctionReal (0 : E)

@[simp] theorem mem_supportFunctionSubdifferentialAtZero_iff
    {Q2 : ConvexBody E} {g : E} :
    g ∈ Q2.supportFunctionSubdifferentialAtZero ↔
      ∀ y : E, Q2.supportFunctionReal y ≥ Q2.supportFunctionReal 0 + inner ℝ g (y - 0) := by
  change g ∈ subdifferentialWithin (Set.univ : Set E) Q2.supportFunctionReal (0 : E) ↔
      ∀ y : E, Q2.supportFunctionReal y ≥ Q2.supportFunctionReal 0 + inner ℝ g (y - 0)
  simpa using
    (mem_subdifferentialWithin_iff :
      g ∈ subdifferentialWithin (Set.univ : Set E) Q2.supportFunctionReal (0 : E) ↔
        (0 : E) ∈ (Set.univ : Set E) ∧
          ∀ ⦃y : E⦄, y ∈ (Set.univ : Set E) →
            Q2.supportFunctionReal y ≥ Q2.supportFunctionReal 0 + inner ℝ g (y - 0))

/-- The positive Euclidean radii whose closed balls are contained in `∂F(0)`. -/
def gammaZeroRadii (Q2 : ConvexBody E) : Set ℝ :=
  {r | 0 < r ∧ Metric.closedBall (0 : E) r ⊆ Q2.supportFunctionSubdifferentialAtZero}

/-- Membership in `gammaZeroRadii` means that the closed Euclidean ball of radius `r` is contained
in `∂F(0)`. -/
theorem mem_gammaZeroRadii_iff {Q2 : ConvexBody E} {r : ℝ} :
    r ∈ Q2.gammaZeroRadii ↔
      0 < r ∧ Metric.closedBall (0 : E) r ⊆ Q2.supportFunctionSubdifferentialAtZero :=
  Iff.rfl

/-- The positive Euclidean radii whose closed balls contain `∂F(0)`. -/
def gammaOneRadii (Q2 : ConvexBody E) : Set ℝ :=
  {r | 0 < r ∧ Q2.supportFunctionSubdifferentialAtZero ⊆ Metric.closedBall (0 : E) r}

/-- Membership in `gammaOneRadii` means that `∂F(0)` is contained in the closed Euclidean ball of
radius `r`. -/
theorem mem_gammaOneRadii_iff {Q2 : ConvexBody E} {r : ℝ} :
    r ∈ Q2.gammaOneRadii ↔
      0 < r ∧ Q2.supportFunctionSubdifferentialAtZero ⊆ Metric.closedBall (0 : E) r :=
  Iff.rfl

/-- The inner Euclidean radius `γ₀(F)` of `∂F(0)`, formalized as the supremum of the admissible
inscribed radii. -/
def gammaZero (Q2 : ConvexBody E) : ℝ :=
  sSup Q2.gammaZeroRadii

/-- Expanding `gammaZero` gives the supremum of the radii whose closed balls lie in `∂F(0)`. -/
theorem gammaZero_eq_sSup (Q2 : ConvexBody E) :
    Q2.gammaZero = sSup Q2.gammaZeroRadii :=
  rfl

/-- The outer Euclidean radius `γ₁(F)` of `∂F(0)`, formalized as the infimum of the admissible
enclosing radii. -/
def gammaOne (Q2 : ConvexBody E) : ℝ :=
  sInf Q2.gammaOneRadii

/-- Expanding `gammaOne` gives the infimum of the radii whose closed balls contain `∂F(0)`. -/
theorem gammaOne_eq_sInf (Q2 : ConvexBody E) :
    Q2.gammaOne = sInf Q2.gammaOneRadii :=
  rfl

/-- Definition 7.11: for the support function `F(v) = max_{u ∈ Q₂} ⟪v, u⟫` of a convex body
`Q₂`, the relative-scale ratio `α(F)` is the quotient `γ₀(F) / γ₁(F)` of the inner and outer
Euclidean radii of `∂F(0)`. The textbook hypothesis `0 ∈ interior Q₂` is not needed to define
this quotient itself, so it is left to later positivity/nondegeneracy results instead of being
packaged as primitive data here. -/
def relativeScaleRatio (Q2 : ConvexBody E) : ℝ :=
  Q2.gammaZero / Q2.gammaOne

/-- Expanding `relativeScaleRatio` recovers the quotient `γ₀(F) / γ₁(F)`. -/
theorem relativeScaleRatio_eq (Q2 : ConvexBody E) :
    Q2.relativeScaleRatio = Q2.gammaZero / Q2.gammaOne :=
  rfl

/-- If the inner radius is positive and does not exceed the outer radius, then the relative-scale
ratio is positive and at most `1`. -/
theorem relativeScaleRatio_pos_and_le_one
    (Q2 : ConvexBody E)
    (hγ0 : 0 < Q2.gammaZero)
    (hγ01 : Q2.gammaZero ≤ Q2.gammaOne) :
    0 < Q2.relativeScaleRatio ∧ Q2.relativeScaleRatio ≤ 1 := by
  rw [relativeScaleRatio_eq]
  have hγ1 : 0 < Q2.gammaOne := lt_of_lt_of_le hγ0 hγ01
  constructor
  · exact div_pos hγ0 hγ1
  · have hγ1_inv : 0 < Q2.gammaOne⁻¹ := inv_pos.mpr hγ1
    simpa [div_eq_mul_inv, hγ1.ne'] using
      mul_le_mul_of_nonneg_right hγ01 hγ1_inv.le

end ConvexBody

/-! ### Lemma_7_11 (from Chap07) -/
noncomputable section

universe u

open scoped ConstrainedArgmin

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Lemma 7.11 lies in Chapter 7's barrier-regularized affine-maximization domain.

Mandatory domain-style sampling before refinement:
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner for
  constrained minimizers and the canonical feasibility-plus-`IsMinOn` bridge;
- `IsMaxOn` in mathlib's `Order/Filter/Extr`, the canonical maximality predicate on a set;
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter owner for supremum values of real
  objectives on a feasible set;
- `Uβ` / `Argmaxβ` in `Chap07/Definition_7_53`, the nearby barrier-regularized maximization API
  that likewise separates a source-facing payoff from its maximizer layer.

Best owner abstraction:
- source-facing: the affine payoff `x ↦ ℓ x - β (F x - F x₀)` and Lemma 7.11's attained-maximizer
  comparison estimates;
- core/canonical: the constrained-minimizer owner `argmin[P] F` for the base point `x₀`, together
  with mathlib's `IsMaxOn` for the two maximizers;
- bridge/view: `maximalValueOn` from `Definition_7_56`, used downstream by `Definition_7_55` to
  pass from attained maximizers to the value notation `ℓ⋆(β)`.

Primitive data:
- the feasible set `P`;
- the barrier term `F`;
- the base point `x₀`;
- the affine functional `ℓ`;
- the regularization parameter `β`.

Derived API:
- the barrier-regularized payoff owner `affineBarrierRegularizedPayoff`;
- the attained-maximizer comparison lemmas below.

Source/core/bridge triage:
- source-facing: the payoff owner and the three comparison lemmas from Lemma 7.11;
- core/canonical: `argmin[P] F` and `IsMaxOn`;
- bridge/view: the `maximalValueOn` specialization in `Definition_7_55`.

The refinement keeps the source-facing payoff owner local to this file. The statement-level repair
is to reuse the existing constrained-argmin owner for `x₀` and to encode the two maximizers with
their missing feasibility data instead of bare `IsMaxOn` hypotheses, whose mathlib meaning alone
does not express attainment on `P`.
-/

/-- The barrier-regularized affine payoff
`ℓ(x) - β (F(x) - F(x₀))` attached to an affine functional `ℓ`, a barrier term `F`, and a base
point `x₀`. -/
def affineBarrierRegularizedPayoff
    (x0 : E) (β : ℝ) (ℓ : AffineMap ℝ E ℝ) (F : E → ℝ) (x : E) : ℝ :=
  ℓ x - β * (F x - F x0)

-- Proof sketch: unfold `affineBarrierRegularizedPayoff`.
/-- Expanding `affineBarrierRegularizedPayoff x₀ β ℓ F x` gives the affine value `ℓ(x)` minus the
barrier penalty `β (F(x) - F(x₀))`. -/
theorem affineBarrierRegularizedPayoff_def
    (x0 : E) (β : ℝ) (ℓ : AffineMap ℝ E ℝ) (F : E → ℝ) (x : E) :
    affineBarrierRegularizedPayoff x0 β ℓ F x =
      ℓ x - β * (F x - F x0) :=
  rfl

section Lemma711

variable {P : Set E} {F : E → ℝ} {ℓ : AffineMap ℝ E ℝ}
variable {x0 xStar xBeta : E} {β v : ℝ}

local notation "Φβ" => affineBarrierRegularizedPayoff x0 β ℓ F

-- Proof sketch: since `x₀` minimizes `F` on `P`, every feasible value satisfies
-- `F(x) - F(x₀) ≥ 0`. Hence the regularized payoff is bounded above pointwise on `P` by the
-- affine functional `ℓ`, and comparing the maximizers `xBeta` and `xStar` gives the result.
/-- Lemma 7.11 (1): if `xBeta` belongs to `P` and maximizes the barrier-regularized affine payoff
there, `xStar` belongs to `P` and maximizes `ℓ` there, and `x₀` minimizes `F` on `P`, then
`ℓ⋆(β) ≤ ℓ⋆`. -/
theorem affineBarrierRegularizedPayoff_max_le_affine_max
    (hβ : 0 < β)
    (hx0 : x0 ∈ argmin[P] F)
    (hxStar_mem : xStar ∈ P)
    (hxStar_max : IsMaxOn ℓ P xStar)
    (hxBeta_mem : xBeta ∈ P)
    (hxBeta_max : IsMaxOn Φβ P xBeta) :
    Φβ xBeta ≤ ℓ xStar := sorry

-- Proof sketch: evaluate the regularized payoff at the segment points
-- `x₀ + α • (xStar - x₀)`, use the affine identity for `ℓ`, and apply the barrier estimate
-- `F(x₀ + α • (xStar - x₀)) ≤ F(x₀) - v log(1 - α)`. Optimizing the resulting one-variable lower
-- bound in `α` yields the logarithmic error term.
/-- Lemma 7.11 (2): under the same attained-maximizer setup, if every segment from `x₀` to a point
of `P` stays in `P` and satisfies the displayed barrier estimate, then
`ℓ⋆ ≤ ℓ⋆(β) + β v (1 + [log ((ℓ⋆ - ℓ₀) / (β v))]_+)`. -/
theorem affineMax_le_affineBarrierRegularizedPayoff_max_add_logTerm
    (hβ : 0 < β) (hv : 0 < v)
    (hx0 : x0 ∈ argmin[P] F)
    (hxStar_mem : xStar ∈ P)
    (hxStar_max : IsMaxOn ℓ P xStar)
    (hxBeta_mem : xBeta ∈ P)
    (hxBeta_max : IsMaxOn Φβ P xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ xStar ≤
      Φβ xBeta +
        β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0) := sorry

-- Proof sketch: start from the same segment lower bound for the regularized payoff, rewrite it
-- as `Δ ≤ A / α - (β v / α) log(1 - α)`, use `log (1 + t) ≤ t`, and minimize the resulting
-- expression `A / α + B / (1 - α)` over `α ∈ (0, 1)` to obtain the square bound.
/-- Lemma 7.11 (3): under the same attained-maximizer and barrier-segment hypotheses, the affine
gap from `x₀` to the maximizer `xStar` is bounded by
`(sqrt (ℓ⋆(β) - ℓ₀) + sqrt (β v))²`. -/
theorem affineMax_sub_base_le_sq_sqrt_add_sqrt_of_affineBarrierRegularizedPayoff_max
    (hβ : 0 < β) (hv : 0 < v)
    (hx0 : x0 ∈ argmin[P] F)
    (hxStar_mem : xStar ∈ P)
    (hxStar_max : IsMaxOn ℓ P xStar)
    (hxBeta_mem : xBeta ∈ P)
    (hxBeta_max : IsMaxOn Φβ P xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ xStar - ℓ x0 ≤
      (Real.sqrt (Φβ xBeta - ℓ x0) +
        Real.sqrt (β * v)) ^ (2 : ℕ) := sorry

end Lemma711

end

/-! ### Proposition_7_11 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Proposition 7.11 lies in Chapter 7's positive-definite matrix-path / log-determinant potential
domain.

Sampled owner-style declarations:
- `logDetBarrierAmbient` and `logDetBarrier` in `Chap05/Definition_5_4_4_5`, the chapter owners
  for the ambient `-log det` formula and its intrinsic positive-definite barrier;
- `logDetBarrier_lineDeriv_eq_frobeniusInner` and its second-directional companion in
  `Chap05/Lemma_5_4_4_1`, the canonical derivative owners for the same matrix potential;
- `Matrix.PosDef`, the canonical matrix-level positivity owner used to justify the logarithmic
  domain.

Best owner abstraction:
- source-facing: the scalar path potential `V(α) = log (det G(0) / det G(α))`;
- core/canonical: the Chapter 5 ambient owner `logDetBarrierAmbient n`;
- bridge/view: the determinant-ratio formula and the trace identities obtained by differentiating
  along the scalar path.

Primitive data:
- the matrix path `G : ℝ → Mat`;
- the parameter family `τ : Fin n → ℝ`;
- positivity of `G α` near `α = 0`;
- differentiability of `G` and of its scalar derivative at `0`.

Derived API:
- the source-facing ratio potential;
- the Chapter 5 bridge expressing that potential as a difference of ambient `-log det` terms on
  the positive-definite locus;
- the first- and second-derivative identities at `α = 0`.

This refinement keeps the source-facing scalar potential, but removes the duplicate derivative
witness data `G₁`, `G₂` from the public theorem surface: the canonical derivatives are
`deriv G 0` and `deriv (deriv G) 0`, while the Chapter 5 barrier owner remains the core
matrix-level abstraction behind the formulas.
-/

/-- The logarithmic determinant-ratio potential
`V(α) = log (det G(0) / det G(α))` attached to a matrix path `G`. -/
def logDetRatioPotential
    (G : ℝ → Mat) (α : ℝ) : ℝ :=
  Real.log (Matrix.det (G 0) / Matrix.det (G α))

/-- Expanding `logDetRatioPotential G α` gives the determinant-ratio formula
`log (det G(0) / det G(α))`. -/
theorem logDetRatioPotential_def
    (G : ℝ → Mat) (α : ℝ) :
    logDetRatioPotential G α =
      Real.log (Matrix.det (G 0) / Matrix.det (G α)) := rfl

/- On the positive-definite locus, the source-facing determinant-ratio potential is the difference
of the Chapter 5 ambient barrier values at `G α` and `G 0`. -/
theorem logDetRatioPotential_eq_sub_logDetBarrierAmbient
    (G : ℝ → Mat) {α : ℝ} (hG0 : (G 0).PosDef) (hGα : (G α).PosDef) :
    logDetRatioPotential G α =
      logDetBarrierAmbient n
          (⟨G α, by
            rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hGα.isHermitian⟩ : SymmMat) -
        logDetBarrierAmbient n
          (⟨G 0, by
            rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hG0.isHermitian⟩ : SymmMat) := by
  rw [logDetRatioPotential, logDetBarrierAmbient_apply, logDetBarrierAmbient_apply,
    Real.log_div hG0.det_pos.ne' hGα.det_pos.ne']
  ring_nf

section

variable (G : ℝ → Mat) (τ : Fin n → ℝ)
variable (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
variable (hG₁ : DifferentiableAt ℝ G 0)
variable (hG₂ : DifferentiableAt ℝ (deriv G) 0)
variable (htrace₁ : Matrix.trace ((G 0)⁻¹ * deriv G 0) = ∑ i : Fin n, (τ i - 1))
variable
  (htrace₂ :
    Matrix.trace
        ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
      -∑ i : Fin n, (τ i - 1) ^ (2 : ℕ))

-- Proof sketch: differentiate `V(α) = log (det G(0) / det G(α))` using Jacobi's formula for
-- `det`, the derivative of matrix inversion, and the cyclicity of the trace; then substitute the
-- two assumed trace identities at `α = 0`.
/-- Proposition 7.11: if a matrix path `G` is twice differentiable at `0`, stays positive
definite near `0`, and its first and second trace identities are encoded by the parameters
`τ₁, …, τₙ`, then the determinant-ratio potential
`V(α) = log (det G(0) / det G(α))` satisfies the stated formulas for `V'(0)` and `V''(0)`. -/
theorem logDetRatioPotential_derivatives_at_zero
    :
    deriv (logDetRatioPotential G) 0 = (n : ℝ) - ∑ i : Fin n, τ i ∧
      iteratedDeriv 2 (logDetRatioPotential G) 0 =
        ∑ i : Fin n, (τ i - 1) ^ (2 : ℕ) := by
  sorry

-- Proof sketch: apply `logDetRatioPotential_derivatives_at_zero` to obtain the first derivative
-- identity, then rewrite the sum `∑ i, τ i` using the given identification with
-- `(\|g\|_D^*)^2`.
/-- If the sum of the parameters `τ₁, …, τₙ` is identified with `(\|g\|_D^*)^2`, then the first
derivative of the determinant-ratio potential is `n - (\|g\|_D^*)^2`. -/
theorem logDetRatioPotential_deriv_at_zero_of_dualNormSq
    (dualNormSq : ℝ) (hdualNormSq : dualNormSq = ∑ i : Fin n, τ i) :
    deriv (logDetRatioPotential G) 0 = (n : ℝ) - dualNormSq := by
  simpa [hdualNormSq] using
    (logDetRatioPotential_derivatives_at_zero G τ hpos hG₁ hG₂ htrace₁ htrace₂).1

end

end

/-! ### Theorem_7_11 (from Chap07) -/
noncomputable section

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "PosMat" => { G : Matrix (Fin n) (Fin n) ℝ // Matrix.PosDef G }
local notation "ConstraintVec" => { d : E // d ≠ 0 }

/- Theorem 7.11 lies in the chapter's relative-scale minimax / recursive outer-iterate /
first-stopping-time domain.

Sampled owner-style declarations:
- `iterativeSmoothingParameter`, `iterativeSmoothingStoppingTime`, and
  `iterativeSmoothingOutputPoint` in `Algorithm_7_9.lean`;
- `iterativeSmoothingBlockLength` in `Algorithm_7_9.lean`, the canonical owner of the per-stage
  lower-level work budget;
- `relativeScaleSubgradientApproximationTotalLowerLevelSteps` in `Theorem_7_3.lean` and
  `schemeSNRestartingTotalLowerLevelSteps` in `Theorem_7_5.lean`, the nearby chapter pattern for
  deriving total lower-level work from canonical stopping data;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for the terminal relative
  accuracy conclusion.

Best owner abstraction:
- source-facing: Theorem 7.11's stopping-time, terminal-value, and total-work bounds for the
  Algorithm 7.9 relative-scale scheme;
- core/canonical: the Algorithm 7.9 owners
  `xHat : ℕ → E`, `iterativeSmoothingParameter a δ`,
  `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`,
  `iterativeSmoothingStoppingTime hTerminate`, and
  `iterativeSmoothingBlockLength (m : ℕ) n δ γ`;
- bridge/view: the derived total lower-level work
  `iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate`.

Primitive data:
- the lower-level subroutine `S`, the family `a`, and the geometric data `d : ConstraintVec`
  and `G`;
- an explicit Algorithm 7.9 outer iterate `xHat` together with the auxiliary hypotheses that it
  starts at `x₀`, has positive stagewise smoothing parameters, and satisfies the recursive update
  rule;
- the termination witness `hTerminate` for the canonical first accepted outer stage;
- the feasible-set lower bound, the feasibility of the generated canonical orbit, the initial
  objective bound, and the terminal relative-gap estimate.

Derived API:
- the recursive orbit `x̂_t`;
- the smoothing parameter at stage `t`, namely
  `iterativeSmoothingParameter a δ (xHat t)`;
- the textbook stopping time `T`;
- the accepted output point `\hat x_T`;
- the total lower-level work up to `T`.

Source/core/bridge triage:
- source-facing: the three bounds asserted by Theorem 7.11;
- core/canonical: the Algorithm 7.9 iterate, smoothing, stopping-time, and output owners;
- bridge/view: the total-work product `T * \tilde N`.

This file now uses the refined source-facing owner directly: the explicit outer iterate `xHat`,
with the stagewise positivity and recursive update information kept as ordinary hypotheses rather
than hidden behind a typeclass wrapper, together with the canonical stopping-time API derived from
that iterate.
-/

/-- The total number of lower-level steps used by Algorithm 7.9 up to its canonical stopping
time, assuming that each outer stage uses the canonical block length
`iterativeSmoothingBlockLength (m : ℕ) n δ γ`. -/
def iterativeSmoothingTotalLowerLevelSteps
    (δ γ : ℝ) {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) : ℕ :=
  iterativeSmoothingStoppingTime hTerminate *
    iterativeSmoothingBlockLength (m : ℕ) n δ γ

/-- Expanding `iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate` gives the product of the
canonical stopping time and the canonical block length. -/
theorem iterativeSmoothingTotalLowerLevelSteps_def
    (δ γ : ℝ) {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) :
    iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate =
      iterativeSmoothingStoppingTime hTerminate *
        iterativeSmoothingBlockLength (m : ℕ) n δ γ :=
  rfl

section Complexity

variable
  {S : (E → ℝ) → ℝ → Set E → PosMat → E → ℕ → E}
  {a : Fin (m : ℕ) → E} {d : ConstraintVec} {G : PosMat}
  {δ γ fStar : ℝ} {feasibleSet : Set E} {xHat : ℕ → E}

variable
  (hZero : xHat 0 = iterativeSmoothingInitialPoint d G)
  (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
  (hSucc :
    ∀ t : ℕ,
      xHat (t + 1) =
        iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t))

variable (hTerminate : iterativeSmoothingTerminates a xHat)

local notation "x̂" => xHat
local notation "F" => maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
local notation "s" => iterativeSmoothingStoppingIndex hTerminate
local notation "T" => iterativeSmoothingStoppingTime hTerminate
local notation "x̂T" => iterativeSmoothingOutputPoint hTerminate

-- Proof sketch: for every `t < iterativeSmoothingStoppingIndex hTerminate`,
-- `iterativeSmoothingStoppingIndex_min hTerminate` gives
-- `F (x̂ (t + 1)) < (1 / e) * F (x̂ t)`, so the canonical orbit decays geometrically before the
-- accepted stage. Compare the feasible preterminal iterate `x̂ s` with `fStar`, combine this with
-- the initial estimate `F (x̂ 0) ≤ γ √n fStar`, and obtain
-- `(T : ℝ) ≤ 1 + log (γ √n)`.
/-- Theorem 7.11 (1): the stopping time is bounded by `1 + log (γ √n)` once the scale parameter
is positive. -/
theorem iterativeSmoothing_stoppingTime_le
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hPreterminal_feasible : x̂ s ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : E) (_hx : x ∈ feasibleSet), fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (T : ℝ) ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) := sorry

-- Proof sketch: multiply the terminal relative-gap estimate by `1 + δ`, use `0 < 1 + δ`, and
-- rearrange the resulting linear inequality to isolate `F x̂T`.
/-- Theorem 7.11 (2): the accepted output point satisfies
`f(\hat x_T) ≤ (1 + δ) f*` in the positive-`δ` regime. -/
theorem iterativeSmoothing_outputPoint_value_le
    (hδ : 0 < δ)
    (hTerminal_relative_gap :
      F x̂T - fStar ≤ (δ / (1 + δ)) * F x̂T) :
    F x̂T ≤ (1 + δ) * fStar := sorry

-- Proof sketch: combine the stopping-time bound from Theorem 7.11 (1) with the definition of
-- `iterativeSmoothingTotalLowerLevelSteps` as the product of the canonical stopping time and the
-- canonical block length, then expand the block-length expression.
/-- Theorem 7.11 (3): the total number of lower-level steps is bounded by the stated explicit
complexity expression once the scale parameter and relative-accuracy parameter are in their
textbook range. -/
theorem iterativeSmoothing_totalLowerLevelSteps_le
    (hδ : 0 < δ)
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hPreterminal_feasible : x̂ s ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : E) (_hx : x ∈ feasibleSet), fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate : ℝ) ≤
      2 * γ * Real.exp 1 * (1 + Real.log (γ * Real.sqrt (n : ℝ))) *
        Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ) := sorry

/-- If the optimal value `f*` is positive, then the accepted output point in Theorem 7.11 has
relative accuracy `δ` with respect to `f*` in the sense of Definition 7.1. -/
theorem iterativeSmoothing_outputPoint_isRelativeAccuracy
    (hfStar_pos : 0 < fStar)
    (hδ : 0 < δ)
    (hOutput_value_ge : fStar ≤ F (iterativeSmoothingOutputPoint hTerminate))
    (hTerminal_relative_gap :
      F (iterativeSmoothingOutputPoint hTerminate) - fStar ≤
        (δ / (1 + δ)) * F (iterativeSmoothingOutputPoint hTerminate)) :
    IsRelativeAccuracy fStar δ (F (iterativeSmoothingOutputPoint hTerminate)) := by
  have hOne_add_δ : 0 < 1 + δ := by
    linarith
  have hMul :
      (F (iterativeSmoothingOutputPoint hTerminate) - fStar) * (1 + δ) ≤
        δ * F (iterativeSmoothingOutputPoint hTerminate) := by
    have hScaled :=
      mul_le_mul_of_nonneg_right hTerminal_relative_gap hOne_add_δ.le
    have hOne_add_δ_ne : (1 + δ) ≠ 0 := ne_of_gt hOne_add_δ
    simpa [div_eq_mul_inv, hOne_add_δ_ne, mul_assoc, mul_left_comm, mul_comm] using hScaled
  have hUpper : F (iterativeSmoothingOutputPoint hTerminate) ≤ (1 + δ) * fStar := by
    nlinarith [hMul]
  exact ⟨hfStar_pos, hOutput_value_ge, hUpper⟩

end Complexity
