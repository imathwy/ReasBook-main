import Mathlib
import Mathlib.Analysis.InnerProductSpace.Subspace

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_3 (from Chap07) -/
noncomputable section

open Metric

universe u

variable {E : Type u} [PseudoMetricSpace E]

/- Definition 7.3 lies in the nearest-point / distance-to-set domain.

Sampled owner declarations:
* `Metric.infDist`, the canonical distance-to-set owner;
* `Metric.isGLB_infDist`, the attained-infimum bridge for `infDist`;
* `Metric.infDist_le_dist_of_mem`, the pointwise comparison lemma used downstream to recover
  minimizing properties;
* `Metric.infDist_eq_iInf`, the canonical metric-space expansion showing that the owner lives at
  the intrinsic `dist` layer rather than at a norm-specific presentation.

Source/core/bridge triage:
* source-facing/core owner: `IsProjectionPointOn Q x p`;
* bridge/view: `isProjectionPointOn_iff_eq_sInf`.

Primitive data:
* the set `Q`, ambient point `x`, and candidate point `p`.

Derived API:
* feasibility `p ∈ Q`;
* the attained-infimum reformulation of the defining metric equality.

Accordingly, the owner is refined to the intrinsic metric layer
`dist x p = Metric.infDist x Q`; norm formulas belong in downstream bridge lemmas, not in the
core owner. -/

/-- Definition 7.3: a point `p ∈ Q` is a projection of `x` onto `Q` when its distance to `x`
realizes the distance from `x` to the set `Q`. -/
def IsProjectionPointOn (Q : Set E) (x p : E) : Prop :=
  p ∈ Q ∧ dist x p = infDist x Q

/-- A point is a projection of `x` onto `Q` exactly when it lies in `Q` and its distance to `x`
equals the infimum of the distance function on `Q`. -/
-- Proof sketch: if `p` is a projection point, then `p ∈ Q`, so `Q` is nonempty and
-- `Metric.isGLB_infDist` identifies `infDist x Q` with the infimum of `((dist x ·) '' Q)`;
-- conversely, the displayed equality is exactly the defining equality after rewriting that
-- infimum as `infDist x Q`.
theorem isProjectionPointOn_iff_eq_sInf {Q : Set E} {x p : E} :
    IsProjectionPointOn Q x p ↔
      p ∈ Q ∧ dist x p = sInf ((dist x ·) '' Q) := by
  constructor <;> rintro ⟨hpQ, hp⟩
  · have hinf : IsGLB ((dist x ·) '' Q) (infDist x Q) :=
      Metric.isGLB_infDist ⟨p, hpQ⟩
    exact ⟨hpQ, hp.trans (hinf.csInf_eq ⟨_, ⟨p, hpQ, rfl⟩⟩).symm⟩
  · have hinf : IsGLB ((dist x ·) '' Q) (infDist x Q) :=
      Metric.isGLB_infDist ⟨p, hpQ⟩
    exact ⟨hpQ, hp.trans (hinf.csInf_eq ⟨_, ⟨p, hpQ, rfl⟩⟩)⟩

/-! ### Lemma_7_3 (from Chap07) -/
noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped SupportFunction RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 7.3 lies in Chapter 7's symmetric-matrix support-function / spectral-radius domain.

Sampled owner-style declarations:
- Chapter 3 `supportFunction` and `supportFunction_apply`, the chapter owner for support functions;
- Chapter 5 `𝕊^n`, `RealSymmetricMatrixSpace.eigenvalues`, and `⟪·, ·⟫_F`, the established
  symmetric-matrix carrier and Frobenius geometry;
- Chapter 7 `spectral_eigenvalue_l1_unit_ball`, the source-facing owner of the set `Q₂`;
- Chapter 7 `ρ(X)`, the canonical spectral-radius surface on `𝕊^n`.

Best owner abstraction:
- source-facing: Lemma 7.3's support-function formula for the spectral radius on `𝕊^n`;
- core/canonical: `spectral_eigenvalue_l1_unit_ball n`, `ξ[·]`, `⟪·, ·⟫_F`, and `ρ(X)`;
- bridge/view: the explicit trace-supremum formula obtained by expanding the owner support function
  on the Frobenius symmetric-matrix space.

Primitive data:
- `X : 𝕊^n`.

Derived API:
- the closedness / convexity / Frobenius-ball bounds for `spectral_eigenvalue_l1_unit_ball n`;
- the explicit trace formula for `(ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal`;
- Lemma 7.3's main identity `ρ(X) = (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal`.

This refinement deletes the duplicate local trace-pairing, Hermitian-set, and semidefinite-gauge
owners, together with the duplicate local Frobenius inner-product instances. The file now reuses
the Chapter 5 owners directly and keeps only the source-facing bridge theorems specific to this
lemma.
-/

-- Proof sketch: the eigenvalue map on `𝕊^n` is continuous, so the defining `ℓ₁`-sublevel set is
-- closed in the inherited Frobenius topology.
/-- The set `Q₂` of symmetric matrices whose eigenvalue `ℓ₁`-sum is at most `1` is closed. -/
theorem isClosed_spectral_eigenvalue_l1_unit_ball
    (n : ℕ) :
    IsClosed (spectral_eigenvalue_l1_unit_ball n) := sorry

-- Proof sketch: `Q₂` is the unit ball of the nuclear norm restricted to symmetric matrices, so
-- it is convex.
/-- The set `Q₂` is convex. -/
theorem convex_spectral_eigenvalue_l1_unit_ball
    (n : ℕ) :
    Convex ℝ (spectral_eigenvalue_l1_unit_ball n) := sorry

-- Proof sketch: if the Frobenius norm is at most `1 / √n`, then Cauchy--Schwarz bounds the
-- eigenvalue `ℓ₁`-norm by `1`.
/-- The Frobenius closed ball of radius `1 / √n` in `𝕊^n` is contained in `Q₂`. -/
theorem closedBall_subset_spectral_eigenvalue_l1_unit_ball
    (n : ℕ) :
    Metric.closedBall (0 : 𝕊^n) (1 / Real.sqrt n) ⊆
      spectral_eigenvalue_l1_unit_ball n := sorry

-- Proof sketch: on `Q₂`, the Frobenius norm is the eigenvalue `ℓ₂`-norm, which is bounded above
-- by the eigenvalue `ℓ₁`-norm.
/-- The set `Q₂` is contained in the Frobenius closed ball of radius `1`. -/
theorem spectral_eigenvalue_l1_unit_ball_subset_closedBall
    (n : ℕ) :
    spectral_eigenvalue_l1_unit_ball n ⊆
      Metric.closedBall (0 : 𝕊^n) (1 : ℝ) := sorry

-- Proof sketch: expand the Chapter 3 support function on the inner-product space `𝕊^n`, then
-- identify the inherited inner product with the Chapter 5 Frobenius trace pairing on symmetric
-- matrices.
/-- Expanding the support function of `Q₂` at `X` gives the textbook trace supremum formula. -/
theorem supportFunction_toReal_Q2_eq_sSup_trace
    (X : SymmMat) :
    (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal =
      sSup ((fun U : SymmMat ↦ Matrix.trace ((X : Mat) * (U : Mat))) ''
        spectral_eigenvalue_l1_unit_ball n) := sorry

-- Proof sketch: Definition 7.17 identifies `ρ(X)` as the canonical spectral-radius owner on
-- `𝕊^n`, and Lemma 7.3 expresses this owner as the support function of `Q₂` with respect to the
-- Frobenius geometry.
/-- Lemma 7.3: for a real symmetric matrix `X`, the spectral radius `ρ(X)` is the support
function of `Q₂`. -/
theorem realSymmetricMatrix_toReal_spectralRadius_eq_supportFunction_Q2
    (X : SymmMat) :
    ρ(X) = (ξ[spectral_eigenvalue_l1_unit_ball n] X).toReal := sorry

/-! ### Proposition_7_3 (from Chap07) -/
noncomputable section

open Matrix
open scoped BigOperators SupportFunction

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ₋₁" => EuclideanSpace ℝ (Fin (n - 1))

/- Proposition 7.3 lies in the chapter's homogeneous linear-programming / support-envelope
duality domain.

Sampled owner-style declarations:
* `supportFunction` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for
  suprema of linear functionals over sets;
* `linearEqualityFeasibleSet` and `mem_linearEqualityFeasibleSet_iff` in
  `Chap03/LinearEqualityFeasibleSet`, the chapter owner for feasible regions cut out by
  `u ∈ Q` and a linear equality `A u = b`;
* `zeroOneBox` in `Chap01/Definition_1_3_1`, the project's explicit-dimension box-owner pattern;
* `linearOptimizationProblemWithNonnegativityConstraints` in `Chap05/Definition_5_4_3_1`, a
  nearby project file that specializes equality-feasible-set owners to linear programs.

Best owner abstraction:
* source-facing: the Chapter 7 homogeneous linear-programming value `f*` and dual profile `φ₁`;
* core/canonical: the Chapter 3 support-function owner applied to `coordinatewiseUnitBox m`,
  together with the Chapter 3 equality-feasible-set owner
  `linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin 0`;
* bridge/view: the coordinatewise box-membership lemma and the explicit sum-of-absolute-values
  formula for `φ₁`.

Primitive data:
* the source-facing box `coordinatewiseUnitBox m`;
* the matrix `hatA` and vector `c`.

Derived API:
* the feasible set and optimal value of the homogeneous linear program;
* the support-function/supremum expansion of `φ₁`;
* the explicit `∑ |(hatA.mulVec y)ᵢ + cᵢ|` formula and the least-value theorem.

This refinement keeps the Chapter 7 source-facing owners, but gives the box its explicit dimension
parameter and presents the feasible region as a thin specialization of the canonical
`linearEqualityFeasibleSet` owner instead of rebuilding the conjunction by hand.
-/

/-- The coordinatewise box `[-1, 1]^m` in `ℝ^m`. -/
abbrev coordinatewiseUnitBox (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {u | ∀ i, |u i| ≤ 1}

/-- Membership in `coordinatewiseUnitBox` means satisfying `|uᵢ| ≤ 1` in every coordinate. -/
@[simp]
theorem mem_coordinatewiseUnitBox_iff {u : Eₘ} :
    u ∈ coordinatewiseUnitBox m ↔ ∀ i, |u i| ≤ 1 :=
  Iff.rfl

/-- The function `φ₁(y)` is the Chapter 3 support function of the coordinatewise box `[-1, 1]^m`,
evaluated at the affine coefficient vector `\hat A y + c`. -/
def homogeneousLinearProgrammingPhi1
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) : Eₙ₋₁ → ℝ :=
  fun y ↦ (ξ[coordinatewiseUnitBox m] (hatA.toEuclideanLin y + c)).toReal

/-- Evaluating `homogeneousLinearProgrammingPhi1 hatA c` at `y` recovers its defining supremum
of the linear functional `u ↦ ⟪\hat A y + c, u⟫` over `coordinatewiseUnitBox`. -/
-- Proof sketch: expand the Chapter 3 support-function owner by `supportFunction_apply`.
theorem homogeneousLinearProgrammingPhi1_eq_sSup
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) (y : Eₙ₋₁) :
    homogeneousLinearProgrammingPhi1 hatA c y =
      sSup
        ((fun u : Eₘ ↦ inner ℝ (hatA.toEuclideanLin y + c) u) '' coordinatewiseUnitBox m) := sorry

/-- The box-constrained feasible set of the dual linear program
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. -/
abbrev homogeneousLinearProgrammingFeasibleSet
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) : Set Eₘ :=
  linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin 0

/-- Membership in `homogeneousLinearProgrammingFeasibleSet hatA` means satisfying the linear
constraint `\hat Aᵀ u = 0` together with the coordinatewise bounds `|uᵢ| ≤ 1`. -/
@[simp]
theorem mem_homogeneousLinearProgrammingFeasibleSet_iff
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (u : Eₘ) :
    u ∈ homogeneousLinearProgrammingFeasibleSet hatA ↔
      hatA.transpose.mulVec u = 0 ∧ u ∈ coordinatewiseUnitBox m := by
  change
    u ∈ linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin
      (0 : Eₙ₋₁) ↔
      hatA.transpose.mulVec u = 0 ∧ u ∈ coordinatewiseUnitBox m
  rw [mem_linearEqualityFeasibleSet_iff]
  constructor
  · rintro ⟨hu, hA⟩
    refine ⟨?_, hu⟩
    ext i
    have hi : (hatA.transpose.toEuclideanLin u) i = 0 := by
      simpa using congrArg (fun v : Eₙ₋₁ ↦ v i) hA
    simpa using hi
  · rintro ⟨hA, hu⟩
    refine ⟨hu, ?_⟩
    ext i
    have hi : (hatA.transpose.mulVec u) i = 0 := by
      simpa using congrArg (fun v ↦ v i) hA
    simpa using hi

/-- The optimal value `f*` of the box-constrained dual linear program
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. -/
def homogeneousLinearProgrammingOptimalValue
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) : ℝ :=
  sSup ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA)

/-- Expanding `homogeneousLinearProgrammingOptimalValue hatA c` gives the defining supremum of
the linear functional `u ↦ ⟪c, u⟫` over the feasible set. -/
-- Proof sketch: unfold `homogeneousLinearProgrammingOptimalValue`.
theorem homogeneousLinearProgrammingOptimalValue_eq_sSup
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) :
    homogeneousLinearProgrammingOptimalValue hatA c =
      sSup ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA) := sorry

/-- The auxiliary function `φ₁` is the sum of the coordinatewise absolute values
`|(\hat A y + c)ᵢ|`. -/
-- Proof sketch: expand the support-function form of `φ₁`, observe that the maximization over
-- `coordinatewiseUnitBox m` decouples by coordinates, and maximize each scalar term
-- `(\hat A y + c)ᵢ uᵢ` over `|uᵢ| ≤ 1`.
theorem homogeneousLinearProgrammingPhi1_eq_sum_abs
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) (y : Eₙ₋₁) :
    homogeneousLinearProgrammingPhi1 hatA c y =
      ∑ i : Fin m, |(hatA.toEuclideanLin y + c) i| := sorry

/-- Proposition 7.3: the box-constrained dual optimal value
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}` is the minimum value attained by the function
`y ↦ homogeneousLinearProgrammingPhi1 hatA c y`. -/
-- Proof sketch: use linear-programming duality for the primal problem
-- `max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. The Lagrangian introduces a free multiplier `y` for
-- `\hat Aᵀ u = 0` and nonnegative multipliers for the box constraints, and eliminating the latter
-- yields the dual objective `homogeneousLinearProgrammingPhi1 hatA c y`. Strong duality then
-- identifies the primal optimal value with the least element of the value set of `φ₁`.
theorem homogeneousLinearProgrammingOptimalValue_isLeast_phi1_values
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) :
    IsLeast (Set.range (homogeneousLinearProgrammingPhi1 hatA c))
      (homogeneousLinearProgrammingOptimalValue hatA c) := sorry

end

/-! ### Theorem_7_3 (from Chap07) -/
noncomputable section

universe u

section

variable {X : Type u}

/- Theorem 7.3 lies in the autonomous discrete-trajectory / first-stopping-time domain.

Sampled owner-style declarations:
- `relativeScaleSubgradientApproximationIterate`,
  `relativeScaleSubgradientApproximationStoppingIndex`, and
  `relativeScaleSubgradientApproximationStoppingTime` in `Algorithm_7_2.lean`;
- `ConstrainedLevelMethod.stoppingIndex` in `Chap03/Algorithm_3_11.lean`;
- `gradientMethod` in `Chap01/Algorithm_1_6_1.lean`;
- `NewtonSystem.orbit` in `Chap01/Algorithm_1_7_1.lean`.

Best owner abstraction:
- source-facing: Theorem 7.3's stopping-time, terminal-value, and work bounds for Algorithm 7.2;
- core/canonical: the Algorithm 7.2 iterate owner
  `relativeScaleSubgradientApproximationIterate G f x0 δ α γ0` together with the canonical
  stopping index/time derived from `hTerminate`;
- bridge/view: the derived lower-level work count
  `relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate`.

Primitive data:
- the update-scheme data `G`, `f`, `x0`, `δ`, `α`, and `γ0`;
- the existence witness `hTerminate` for the stopping criterion;
- the actual optimality data and Chapter 7 parameter relations;
- the lower-level stage guarantee attached to the fixed block length.

Derived API:
- the canonical stage sequence `\hat x_t`;
- the first stopping index `s` and stopping time `T = s + 1`;
- the total lower-level work up to `T`;
- the three bounds asserted by Theorem 7.3.

Source/core/bridge triage:
- source-facing: the three theorem conclusions;
- core/canonical: the Algorithm 7.2 iterate and stopping-time owners;
- bridge/view: the work-count formula `T * (\hat N + 1)`.

The stopping data already has a canonical owner in `Algorithm_7_2.lean`, so this file states the
Theorem 7.3 conclusions directly on that owner instead of introducing a separate public result
wrapper.
-/

/-- The total number of lower-level gradient steps used by the relative-scale subgradient
approximation trajectory up to its stopping time, assuming that each stage uses
`relativeScaleSubgradientApproximationBlockLength δ α + 1` lower-level steps. -/
def relativeScaleSubgradientApproximationTotalLowerLevelSteps
    {f : X → ℝ} {G : ℕ → ℝ → X} {x0 : X} {δ α γ0 : ℝ}
    (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0) : ℕ :=
  relativeScaleSubgradientApproximationStoppingTime hTerminate *
    (relativeScaleSubgradientApproximationBlockLength δ α + 1)

-- Proof sketch: unfold `relativeScaleSubgradientApproximationTotalLowerLevelSteps`.
/-- Expanding `relativeScaleSubgradientApproximationTotalLowerLevelSteps` gives the product of the
stopping time and the per-stage lower-level step count. -/
theorem relativeScaleSubgradientApproximationTotalLowerLevelSteps_def
    {f : X → ℝ} {G : ℕ → ℝ → X} {x0 : X} {δ α γ0 : ℝ}
    (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0) :
    relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate =
      relativeScaleSubgradientApproximationStoppingTime hTerminate *
        (relativeScaleSubgradientApproximationBlockLength δ α + 1) :=
  rfl

section TerminationBounds

variable [NormedAddCommGroup X]
variable {f : X → ℝ} {G : ℕ → ℝ → X} {x0 xStar : X} {δ α γ0 γ1 : ℝ}

local notation "x̂" => relativeScaleSubgradientApproximationIterate G f x0 δ α γ0

variable
  (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0)

local notation "T" => relativeScaleSubgradientApproximationStoppingTime hTerminate

-- Proof sketch: use `relativeScaleSubgradientApproximationStoppingIndex_min` to show that before
-- the first accepted stage the objective decays by the factor `1 / √e`, then combine the
-- resulting estimate at `T - 1` with the optimality witness `hxStar` and the lower bound
-- `α * f x0 ≤ f xStar` to obtain `(T : ℝ) ≤ 1 + 2 log (1 / α)`. For the terminal value, apply the
-- lower-level stage guarantee at time `T - 1`, use the distance bound
-- `‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar`, rewrite the chapter parameter relation as
-- `α = γ0 / γ1`, and derive the required coefficient estimate from the canonical block-length
-- formula in `relativeScaleSubgradientApproximationBlockLength`. Finally multiply the per-stage
-- block length by the stopping-time bound to control the total lower-level work.
/-- Theorem 7.3 (1): under the canonical stopping-time setup for Algorithm 7.2, the stopping time
`T` is bounded above by `1 + 2 log (1 / α)`. -/
theorem relativeScaleSubgradientApproximation_stopping_time_bound
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_relation : α = γ0 / γ1)
    (hLowerLevel_gap :
      ∀ t : ℕ,
        f (x̂ (t + 1)) - f xStar ≤
          (γ1 / Real.sqrt ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
            ‖x0 - xStar‖)
    : (T : ℝ) ≤ 1 + 2 * Real.log (1 / α) := sorry

-- Proof sketch: apply the lower-level stage guarantee at time `T - 1`, use the distance bound
-- `‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar`, rewrite `α = γ0 / γ1`, and compare the
-- resulting terminal estimate with the minimizer value `f xStar`.
/-- Theorem 7.3 (2): under the canonical stopping-time setup for Algorithm 7.2, the terminal value
`f(\hat x_T)` has relative accuracy `δ` with respect to `f(xStar)`. -/
theorem relativeScaleSubgradientApproximation_terminal_relative_accuracy
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_relation : α = γ0 / γ1)
    (hLowerLevel_gap :
      ∀ t : ℕ,
        f (x̂ (t + 1)) - f xStar ≤
          (γ1 / Real.sqrt ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
            ‖x0 - xStar‖)
    : IsRelativeAccuracy (f xStar) δ (f (x̂ T)) := sorry

-- Proof sketch: combine the stopping-time bound from Theorem 7.3 (1) with the explicit formula
-- for `relativeScaleSubgradientApproximationTotalLowerLevelSteps`, using that each stage performs
-- `relativeScaleSubgradientApproximationBlockLength δ α + 1` lower-level steps.
/-- Theorem 7.3 (3): under the canonical stopping-time setup for Algorithm 7.2, the total number
of lower-level gradient steps up to time `T` is bounded by
`(e / α²) (1 + 1 / δ)² (1 + 2 log (1 / α))`. -/
theorem relativeScaleSubgradientApproximation_total_lower_level_steps_bound
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_relation : α = γ0 / γ1)
    (hLowerLevel_gap :
      ∀ t : ℕ,
        f (x̂ (t + 1)) - f xStar ≤
          (γ1 / Real.sqrt ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
            ‖x0 - xStar‖)
    :
    (relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate : ℝ) ≤
      ((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ) *
        (1 + 2 * Real.log (1 / α)) := sorry

end TerminationBounds

end
