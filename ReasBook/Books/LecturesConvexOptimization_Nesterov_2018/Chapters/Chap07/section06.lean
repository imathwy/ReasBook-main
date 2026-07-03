import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_6 (from Chap07) -/
open Metric

universe u

/- Domain review for this item: it lies in the real continuous-dual / operator-norm domain.

Sampled owner-style declarations:
- mathlib `StrongDual`
- mathlib `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
- mathlib `IsCompact.exists_sSup_image_eq`
- project `dual_norm_eq_sSup_closedUnitBall` in `Chap04/Definition_4_4_4`

Best owner abstraction:
- source-facing: the textbook dual norm of a real continuous linear functional;
- core/canonical: the existing norm `‖·‖ : StrongDual ℝ E → ℝ`;
- bridge/view: the Chapter 4 support-function formula `dual_norm_eq_sSup_closedUnitBall`.

Primitive data:
- a real normed space `E`;
- a continuous linear functional `g : StrongDual ℝ E`.

Derived API:
- the canonical norm owner `‖g‖`;
- the closed-unit-ball support formula, reused directly from Chapter 4;
- in finite dimensions, existence of a maximizer on the primal closed unit ball.

Source/core/bridge triage:
- source-facing: the dual norm and its finite-dimensional attainment formula;
- core/canonical: the norm on `StrongDual ℝ E`;
- bridge/view: `dual_norm_eq_sSup_closedUnitBall`.

The previous local theorem `dual_norm_eq_sSup_pairing_closedUnitBall` duplicated the exact
Chapter 4 bridge `dual_norm_eq_sSup_closedUnitBall`. This file is therefore recall-first: it
reuses the canonical owner and the existing bridge, and keeps only the new finite-dimensional
attainment statement. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 7.6: the dual norm is the canonical norm on the continuous dual `StrongDual ℝ E`.
-/
#check (‖·‖ : StrongDual ℝ E → ℝ)

/- The textbook closed-unit-ball formula is exactly the existing Chapter 4 bridge theorem. -/
recall dual_norm_eq_sSup_closedUnitBall

section

variable [FiniteDimensional ℝ E]

/-- The dual norm of a continuous linear functional is attained on the primal closed unit ball. -/
-- Proof sketch: use compactness of the closed unit ball in finite dimensions and continuity of
-- `x ↦ g x` to obtain a maximizer, then identify the attained supremum with `‖g‖` via
-- `dual_norm_eq_sSup_closedUnitBall`.
theorem dual_norm_exists_maximizer_closedUnitBall (g : StrongDual ℝ E) :
    ∃ x ∈ closedBall (0 : E) 1, ‖g‖ = g x := sorry

end

end

/-! ### Lemma_7_6 (from Chap07) -/
noncomputable section

open scoped BigOperators

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 7.6 lies in the Chapter 7 finite-family ellipsoid-rounding domain.

Sampled owner-style declarations:
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter owner of the unit ellipsoid;
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing owner of radius-parametrized
  ellipsoids;
- `IsBetaRounding` in `Chap07/Definition_7_27`, the chapter owner for the pair of inner/outer
  ellipsoid containments;
- `weightedPrimalAverage` in `Chap07/Proposition_7_30`, a nearby Chapter 7 mean construction for
  finite families.

Best owner abstraction:
- source-facing: Lemma 7.6's empirical ellipsoid rounding of `convexHull ℝ (Set.range a)`;
- core/canonical: `IsBetaRounding` together with the underlying ellipsoid owners
  `affineEllipsoid` and `matrixEllipsoid`;
- bridge/view: the explicit arithmetic-mean and empirical-matrix formulas below.

Primitive data:
- the vertex family `a : Fin m → E`.

Derived API:
- the arithmetic mean of the vertices;
- the radius `√(m (m - 1))`;
- the normalized empirical shape matrix;
- the resulting `IsBetaRounding` witness for the convex hull.

The main duplicate wheel in the previous version was the conjunction-shaped theorem statement:
its two conclusions are exactly the fields of `IsBetaRounding`. This file now states the result at
that owner level and keeps the coordinate formulas only as supporting definitions.
-/

/-- The arithmetic mean of the vertices `a i`. -/
def polytopeArithmeticMean (a : Fin m → E) : E :=
  (m : ℝ)⁻¹ • ∑ i : Fin m, a i

/-- The outer-radius parameter `R = √(m (m - 1))` used in the empirical ellipsoid bound. -/
def polytopeRoundingRadius (m : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * (m - 1 : ℕ))

/-- The empirical covariance-shape matrix
`R⁻² ∑ᵢ (aᵢ - â) (aᵢ - â)ᵀ` attached to the vertex family `a`. -/
def polytopeRoundingMatrix (a : Fin m → E) : Matrix (Fin n) (Fin n) ℝ :=
  ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ •
    ∑ i : Fin m,
      Matrix.vecMulVec
        (a i - polytopeArithmeticMean a)
        (a i - polytopeArithmeticMean a)

-- Proof sketch: compare support functions. For the outer inclusion, compute the support function of
-- the ellipsoid with shape `polytopeRoundingMatrix a` and bound it below by the maximum over the
-- vertices. For the inner inclusion, use the zero-sum relation among the centered support values
-- and optimize their squared sum under the upper bound by the maximal component.
/-- Lemma 7.6: if the convex hull of the vertices `a i` has nonempty interior, then the empirical
ellipsoid centered at the arithmetic mean gives a
`polytopeRoundingRadius m`-rounding of that convex hull. -/
theorem convexHull_range_between_empirical_ellipsoids_of_interior_nonempty
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    IsBetaRounding
      (convexHull ℝ (Set.range a))
      (polytopeRoundingRadius m)
      (polytopeRoundingMatrix a)
      (polytopeArithmeticMean a) := sorry

end

/-! ### Proposition_7_6 (from Chap07) -/
noncomputable section

open Asymptotics
open Filter

local notation "DimPair" => ℕ × ℕ

/- Proposition 7.6 lies in the chapter's asymptotic-complexity comparison domain.

Sampled owner-style declarations:
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- mathlib `Filter.comap`, the canonical way to express the regime where only the first coordinate
  tends to infinity;
- mathlib `Filter.principal`, the canonical way to impose the side condition
  `0 < p < n (n + 1) / 2`.

Best owner abstraction:
- source-facing: the comparison between the gradient-method total complexity bound
  `n^2 p^2 + (1 / δ) n^(5 / 2) (p + n) log n` and the short-step interior-point bound
  `p n^(5 / 2) (p + n) log (n / δ)`;
- core/canonical: `Asymptotics.IsBigO` on the chapter's admissible-dimension filter;
- bridge/view: none beyond the filter owner itself.

Primitive data:
- the admissible dimension regime `0 < p < n (n + 1) / 2` with `n → ∞`;
- an accuracy profile `δ(n, p)`;
- the gradient-method total arithmetic-work profile `TG`.

Derived API:
- the eventual dominance of the gradient-method upper bound by the short-step interior-point
  complexity model under the source condition `δ ≥ O(1 / p)`.

The source proposition compares two displayed complexity formulas rather than introducing a new
wrapper notion. This file therefore keeps the canonical filter owner for the admissible regime and
states the comparison directly on mathlib's `=O` surface.
-/

/-- The filter expressing statements that hold for all sufficiently large `n` and every positive
`p` satisfying `p < n (n + 1) / 2`. -/
def restrictedDimensionFilter : Filter DimPair :=
  comap Prod.fst atTop ⊓
    principal
      (setOf fun dims : DimPair ↦
        0 < dims.2 ∧ dims.2 < dims.1 * (dims.1 + 1) / 2)

-- Proof sketch: use the eventual lower bound `C / p ≤ δ(n, p)` and the positivity of `p` on
-- `restrictedDimensionFilter` to compare `(1 / δ(n, p))` with a constant multiple of `p`.
-- Then use `δ(n, p) ≤ n` to control `log n` by `log (n / δ(n, p))` up to absolute constants.
-- On the admissible regime `p < n (n + 1) / 2`, the polynomial term `n^2 p^2` is absorbed by
-- `p n^(5 / 2) (p + n) log (n / δ(n, p))`, so the displayed gradient-method bound is dominated by
-- the displayed short-step interior-point bound.
/-- Proposition 7.6 [Chapter7_1.json:40]: along the admissible regime
`0 < p < n (n + 1) / 2` with `n → ∞`, if the total arithmetic complexity `T_G(n, p)` of method
`(7.1.30)` is bounded by
`O(n^2 p^2 + (1 / δ(n, p)) n^(5 / 2) (p + n) log n)` and the required relative accuracy profile
`δ(n, p)` is eventually bounded above by `n` and below by a positive constant multiple of `1 / p`,
then `T_G(n, p)` is also bounded by the short-step path-following complexity scale
`O(p n^(5 / 2) (p + n) log (n / δ(n, p)))`. In this asymptotic sense, the gradient-type method is
preferable whenever `δ ≥ O(1 / p)`. -/
theorem gradientMethod_isBigO_shortStepPathFollowing_of_accuracy_eventually_ge_const_inv_p
    (δ TG : DimPair → ℝ) {C : ℝ} (hC : 0 < C)
    (hδ_upper : ∀ᶠ dims in restrictedDimensionFilter, δ dims ≤ (dims.1 : ℝ))
    (hδ_lower : ∀ᶠ dims in restrictedDimensionFilter, C / (dims.2 : ℝ) ≤ δ dims)
    (hTG :
      TG =O[restrictedDimensionFilter]
        (fun dims ↦
          (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
            (1 / δ dims) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
              ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ))) :
    TG =O[restrictedDimensionFilter]
      (fun dims ↦
        (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := sorry

end

/-! ### Theorem_7_6 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 7.6 lies in Chapter 7's centrally symmetric ellipsoid-rounding / stopping-index domain.

Sampled owner-style declarations:
- `CentralSymmetricRoundingMethod.stoppingCriterion` and
  `CentralSymmetricRoundingMethod.stoppingIndex` in `Algorithm_7_5`, the canonical first-hit
  stopping API for Algorithm 7.5;
- `CentralSymmetricRoundingMethod.threshold_lt_radius_of_lt_stoppingIndex` in `Algorithm_7_5`,
  the owner-level continuation inequality `γ √n < rₖ` before the first stopping index;
- `IsBetaRounding` in `Definition_7_27` and `IsInitialApproximation` in `Definition_7_29`, the
  chapter owners for centered initial ellipsoid data.

Best owner abstraction:
- source-facing: the iteration bound for the actual Algorithm 7.5 run, measured at its canonical
  first stopping index;
- core/canonical: `CentralSymmetricRoundingMethod`, its stopping API, and the centered
  ellipsoid-rounding owner `IsBetaRounding`;
- bridge/view: theorem-level invariance and log-determinant growth hypotheses attached only to
  genuinely continuing steps.

Primitive data:
- the centrally symmetric rounding method itself;
- the canonical termination witness for that method;
- the initial outer radius `R` appearing in the centered rounding datum.

Derived API:
- the stopping index `method.stoppingIndex hTerminate`;
- the continuation inequality `γ √n < rₖ` before stopping;
- the initial centered rounding data packaged by `IsBetaRounding`;
- the lower bound `1 ≤ R`, derived internally from the initial rounding data together with
  `method.one_le_dim`;
- the determinant-growth lower bound used in the complexity estimate.

The previous statement was organized around an arbitrary `N` and separate proof-bridge hypotheses
for `σₖ` and `log det`. This refinement moves the main theorem back to the owner layer of
Algorithm 7.5: the bound is stated for the canonical first stopping index, the lower bound on
`σₖ` is derived from the continuation inequality, the lower bound `1 ≤ R` is recovered internally
from the initial rounding datum, and the initial containment data are packaged by the chapter
rounding owner.
-/

namespace CentralSymmetricRoundingMethod

section StoppingBounds

variable (method : CentralSymmetricRoundingMethod n)
variable (hTerminate : method.Terminates)

local notation "s" => method.stoppingIndex hTerminate

-- Proof sketch: derive `1 ≤ R` from the initial centered rounding data and `method.one_le_dim`.
-- Sum the lower bound for `log det Gₖ₊₁ - log det Gₖ` over the genuinely continuing steps
-- `k < s`; for each such `k`, the continuation inequality `γ √n < rₖ` is supplied canonically by
-- `threshold_lt_radius_of_lt_stoppingIndex`. Compare the resulting lower bound for
-- `log det G_s - log det G₀` with the upper bound coming from the initial centered rounding
-- `W₁(G₀) ⊆ C ⊆ W_R(G₀)` and the persistent inner containments `W₁(Gₖ) ⊆ C`.
/-- Theorem 7.6: if an Algorithm 7.5 run starts from the centered `R`-rounding
`W₁(G₀) ⊆ C ⊆ W_R(G₀)`, if every post-update iterate before the first stopping index still
satisfies `W₁(Gₖ) ⊆ C`, and if every genuinely continuing step `k < s` gains at least
`2 log γ - (γ² - 1) / γ²` in `log det Gₖ`, then the canonical first stopping index `s` is
bounded by `2 n γ² / (γ - 1)² * log R`. -/
theorem stoppingIndex_le
    {R : ℝ}
    (hInitial : IsBetaRounding (method.body : Set E) R (method 0) (0 : E))
    (hinner :
      ∀ k : ℕ, k < s →
        W[1]((method (k + 1))) ⊆ (method.body : Set E))
    (hlogDet :
      ∀ k : ℕ, k < s →
        Real.log (Matrix.det (method (k + 1))) ≥
          Real.log (Matrix.det (method k)) +
            (2 * Real.log method.gamma -
              (method.gamma ^ (2 : ℕ) - 1) / method.gamma ^ (2 : ℕ))) :
    (s : ℝ) ≤
      2 * (n : ℝ) * method.gamma ^ (2 : ℕ) / (method.gamma - 1) ^ (2 : ℕ) * Real.log R := sorry

end StoppingBounds

end CentralSymmetricRoundingMethod

end
