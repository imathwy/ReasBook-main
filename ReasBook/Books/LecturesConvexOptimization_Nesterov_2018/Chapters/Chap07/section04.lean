import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_4 (from Chap07) -/
noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 7.4: a conic unconstrained minimization problem on a real inner product space
consists of a nonempty closed convex feasible set `Q₁` avoiding the origin together with a convex
positively `1`-homogeneous real-valued objective `f`, under the standing nondegeneracy condition
`0 ∈ interior (∂f(0))`. Since the objective is `E → ℝ`, the textbook assumption `dom f = E` is
built into the type, while the ambient constrained-problem data are owned canonically by
`SetConstrainedMinimizationProblem`. -/
structure ConicUnconstrainedMinimizationProblem (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends SetConstrainedMinimizationProblem E where
  /-- The feasible set `Q₁` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q₁` is closed. -/
  feasibleSet_isClosed : IsClosed feasibleSet
  /-- The feasible set `Q₁` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The origin does not belong to `Q₁`. -/
  zero_not_mem_feasibleSet : (0 : E) ∉ feasibleSet
  /-- The objective `f : E → ℝ` is convex on the whole space. -/
  objective_convex : ConvexOn ℝ Set.univ objective
  /-- The objective `f` is positively homogeneous of degree `1`. -/
  objective_posHomogeneous : IsPositivelyHomogeneousOn 1 Set.univ objective
  /-- The origin lies in the interior of the subdifferential `∂f(0)`. -/
  zero_mem_interior_subdifferential :
    (0 : E) ∈ interior (∂ (fun y ↦ (objective y : WithTop ℝ))(0))

namespace ConicUnconstrainedMinimizationProblem

/-- A conic unconstrained minimization problem can be used as its underlying objective function.
-/
instance : CoeFun (ConicUnconstrainedMinimizationProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a conic unconstrained minimization problem returns its objective value. -/
@[simp] theorem coe_apply (problem : ConicUnconstrainedMinimizationProblem E) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The positive-homogeneity field recovers the textbook nonnegative scaling law. -/
theorem map_nonneg_smul
    (problem : ConicUnconstrainedMinimizationProblem E) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    problem (t • x) = t * problem x := by
  simpa [NNReal.smul_def, Real.rpow_one, smul_eq_mul] using
    problem.objective_posHomogeneous.map_smul (by simp) (⟨t, ht⟩ : NNReal)

end ConicUnconstrainedMinimizationProblem

/-! ### Lemma_7_4 (from Chap07) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.4 lies in Chapter 7's positive-definite ellipsoid-rounding / rank-one update domain.

Sampled owner-style declarations:
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Chap03/Lemma_3_2_7`, the chapter owner and
  defining membership theorem for unit-radius ellipsoids;
- `matrixEllipsoid`, `centeredMatrixEllipsoid_one_eq_affineEllipsoid`, and
  `mem_centeredMatrixEllipsoid_iff_dualNorm_le` in `Definition_7_26`, the radius-parametrized
  ellipsoid owner and its positive-definite dual-norm bridge;
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the `G`-primal norm and its
  induced dual norm;
- `centralSymmetryRoundingObjective` and `centralSymmetryRoundingAlphaStar` in `Proposition_7_8`,
  the scalar owner declarations for the logarithmic objective and its critical point;
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner from mathlib.

Best owner abstraction:
- source-facing: the rank-one matrix path, the signed convex hull, and the scalar potential data
  specific to Lemma 7.4;
- core/canonical: `affineEllipsoid`, `positiveDefMatrixNorm`, and `Matrix.vecMulVec`;
- bridge/view: the ellipsoid-containment and determinant-ratio theorems for the source-facing
  constructions.

Primitive data:
- a matrix `G : Mat`;
- a direction `g : E`;
- an interpolation parameter `α : ℝ`;
- a positive-definiteness proof `hG` only when the `G`-dual norm enters.

Derived API:
- the centered unit ellipsoid is expressed directly through `affineEllipsoid`, not through a
  parallel local owner;
- the scalar parameter `σ`;
- the matrix-level potential and optimal parameter, obtained by specializing the scalar owner from
  `Proposition_7_8`;
- the containment and determinant-ratio conclusions used downstream in Definition 7.28.

Source/core/bridge triage:
- source-facing: `rankOneUpdatedMatrix`, `rankOneUpdateAugmentedHull`, `rankOneUpdateSigma`,
  `rankOneUpdatePotential`, and `rankOneUpdateOptimalAlpha`;
- core/canonical: `affineEllipsoid`, `positiveDefMatrixNorm`, and `Matrix.vecMulVec`;
- bridge/view: the remaining theorem-level consequences below.

The centered unit ellipsoid already belongs to the chapter owner `affineEllipsoid`, so this file
keeps only the genuinely source-facing rank-one update objects and derives their ellipsoid views
from that owner. -/

/-- The rank-one matrix update `G(α) = (1 - α) G + α ggᵀ`. -/
def rankOneUpdatedMatrix
    (G : Mat) (g : E) (α : ℝ) : Mat :=
  (1 - α) • G + α • Matrix.vecMulVec g g

-- Proof sketch: unfold `rankOneUpdatedMatrix` and simplify the scalar coefficients at `α = 0`.
/-- At `α = 0`, the rank-one update `G(α)` is the original matrix `G`. -/
@[simp] theorem rankOneUpdatedMatrix_zero
    (G : Mat) (g : E) :
    rankOneUpdatedMatrix G g 0 = G := by
  simp [rankOneUpdatedMatrix]

/-- The convex body `C_{± g}(G)`, defined as the convex hull of the unit ellipsoid `E(G, 0)` and
the two points `g` and `-g`. -/
def rankOneUpdateAugmentedHull
    (G : Mat) (g : E) : Set E :=
  convexHull ℝ (E(G, (0 : E)) ∪ ({g, -g} : Set E))

-- Proof sketch: unfold `rankOneUpdateAugmentedHull`.
/-- Expanding `rankOneUpdateAugmentedHull G g` gives the convex hull of `E(G, 0) ∪ {g, -g}`. -/
theorem rankOneUpdateAugmentedHull_def
    (G : Mat) (g : E) :
    rankOneUpdateAugmentedHull G g =
      convexHull ℝ (E(G, (0 : E)) ∪ ({g, -g} : Set E)) :=
  rfl

/-- The quantity `σ = (1 / n) ‖g‖_{G,*}² - 1` appearing in the determinant estimate. -/
def rankOneUpdateSigma
    (G : Mat) (hG : G.PosDef) (g : E) : ℝ :=
  (‖g‖[⟨G, hG⟩,*] ^ (2 : ℕ)) / n - 1

-- Proof sketch: unfold `rankOneUpdateSigma`.
/-- Expanding `rankOneUpdateSigma G g` gives `(‖g‖_{G,*}^2 / n) - 1`. -/
theorem rankOneUpdateSigma_def
    (G : Mat) (hG : G.PosDef) (g : E) :
    rankOneUpdateSigma G hG g =
      (‖g‖[⟨G, hG⟩,*] ^ (2 : ℕ)) / n - 1 :=
  rfl

/-- The logarithmic determinant potential
`V(α) = log (1 + α (n (1 + σ) - 1)) + (n - 1) log (1 - α)`. -/
def rankOneUpdatePotential
    (G : Mat) (hG : G.PosDef) (g : E) (α : ℝ) : ℝ :=
  centralSymmetryRoundingObjective n (rankOneUpdateSigma G hG g) α

-- Proof sketch: unfold `rankOneUpdatePotential` and then `centralSymmetryRoundingObjective`.
/-- Expanding `rankOneUpdatePotential G g α` gives the explicit closed form for `V(α)`. -/
theorem rankOneUpdatePotential_def
    (G : Mat) (hG : G.PosDef) (g : E) (α : ℝ) :
    rankOneUpdatePotential G hG g α =
      Real.log (1 + α * ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1)) +
        ((n : ℝ) - 1) * Real.log (1 - α) := by
  simp [rankOneUpdatePotential, centralSymmetryRoundingObjective]

/-- The candidate maximizer `α* = σ / (n (1 + σ) - 1)` for the potential `V`. -/
def rankOneUpdateOptimalAlpha
    (G : Mat) (hG : G.PosDef) (g : E) : ℝ :=
  centralSymmetryRoundingAlphaStar n (rankOneUpdateSigma G hG g)

-- Proof sketch: unfold `rankOneUpdateOptimalAlpha` and then `centralSymmetryRoundingAlphaStar`.
/-- Expanding `rankOneUpdateOptimalAlpha G g` gives the explicit formula for `α*`. -/
theorem rankOneUpdateOptimalAlpha_def
    (G : Mat) (hG : G.PosDef) (g : E) :
    rankOneUpdateOptimalAlpha G hG g =
      rankOneUpdateSigma G hG g /
        ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1) := by
  simp [rankOneUpdateOptimalAlpha, centralSymmetryRoundingAlphaStar]

-- Proof sketch: this is the matrix specialization of
-- `centralSymmetryRoundingAlphaStar_mem_Ico` from Proposition 7.8.
/-- If `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then the candidate maximizer
`α* = σ / (n (1 + σ) - 1)` lies in the interval `[0, 1)`. -/
theorem rankOneUpdateOptimalAlpha_mem_Ico
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    rankOneUpdateOptimalAlpha G hG g ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [rankOneUpdateOptimalAlpha] using
    centralSymmetryRoundingAlphaStar_mem_Ico hn hσ.le

-- Proof sketch: compare support functions. For every `x`, the quadratic form of `G(α)` is bounded
-- by the maximum of the support functions of `W₁(G)` and `conv({±g})`, and the support function of
-- the convex hull is the maximum of the two support functions.
/-- The unit ellipsoid associated with `G(α)` is contained in the convex hull of `W₁(G)` and the
two points `±g`. -/
theorem rankOneUpdatedMatrix_affineEllipsoid_subset_augmentedHull
    (G : Mat) (hG : G.PosDef) (g : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    E(rankOneUpdatedMatrix G g α, (0 : E)) ⊆
      rankOneUpdateAugmentedHull G g := sorry

-- Proof sketch: use the matrix determinant lemma to rewrite
-- `det (rankOneUpdatedMatrix G g α) / det G` as the closed form depending on
-- `rankOneUpdateSigma G g`.
/-- The logarithmic potential `V(α)` agrees with the determinant ratio
`log (det G(α) / det G)`. -/
theorem rankOneUpdatePotential_eq_log_det_ratio
    (G : Mat) (hG : G.PosDef) (g : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    rankOneUpdatePotential G hG g α =
      Real.log (Matrix.det (rankOneUpdatedMatrix G g α) / Matrix.det G) := sorry

-- Proof sketch: specialize the scalar maximizer theorem
-- `centralSymmetryRoundingObjective_isMaxOn_iff` from Proposition 7.8 at
-- `σ = rankOneUpdateSigma G hG g`.
/-- Lemma 7.4: if `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then `V(α)` attains its
maximum on `[0, 1)` at `α* = σ / (n (1 + σ) - 1)`. -/
theorem rankOneUpdatePotential_isMaxOn_optimalAlpha
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    IsMaxOn (rankOneUpdatePotential G hG g) (Set.Ico (0 : ℝ) 1)
      (rankOneUpdateOptimalAlpha G hG g) := by
  have hα :
      rankOneUpdateOptimalAlpha G hG g ∈ Set.Ico (0 : ℝ) 1 :=
    rankOneUpdateOptimalAlpha_mem_Ico G hG g hn hσ
  simpa [rankOneUpdatePotential, rankOneUpdateOptimalAlpha] using
    (centralSymmetryRoundingObjective_isMaxOn_iff hn hσ.le hα).2 rfl

-- Proof sketch: specialize the scalar value formula
-- `centralSymmetryRoundingObjective_alphaStar_value` from Proposition 7.8.
/-- If `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then evaluating `V` at `α*` gives
the closed formula from Lemma 7.4. -/
theorem rankOneUpdatePotential_at_optimalAlpha
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) =
      Real.log (1 + rankOneUpdateSigma G hG g) +
        ((n : ℝ) - 1) *
          Real.log
            (((n : ℝ) - 1) * (1 + rankOneUpdateSigma G hG g) /
              ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1)) := by
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hcoeff :
      ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1) ≠ 0 := by
    have hcoeff_pos : 0 < (n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1 := by
      nlinarith
    exact ne_of_gt hcoeff_pos
  have hvalue :
      centralSymmetryRoundingObjective n (rankOneUpdateSigma G hG g)
          (centralSymmetryRoundingAlphaStar n (rankOneUpdateSigma G hG g)) =
        Real.log (1 + rankOneUpdateSigma G hG g) +
          ((n : ℝ) - 1) *
            Real.log
              (((n : ℝ) - 1) * (1 + rankOneUpdateSigma G hG g) /
                ((n : ℝ) * (1 + rankOneUpdateSigma G hG g) - 1)) :=
    centralSymmetryRoundingObjective_alphaStar_value hcoeff
  simpa [rankOneUpdatePotential, rankOneUpdateOptimalAlpha] using hvalue

-- Proof sketch: rewrite the second logarithm as `log (1 - t)` with
-- `t = σ / (n (1 + σ) - 1)` and apply the standard bound `log (1 - t) ≥ -t / (1 - t)`.
/-- If `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then the optimal value of `V` is
bounded below by `log (1 + σ) - σ / (1 + σ)`. -/
theorem rankOneUpdatePotential_optimalAlpha_lower_bound_log
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    Real.log (1 + rankOneUpdateSigma G hG g) -
        rankOneUpdateSigma G hG g / (1 + rankOneUpdateSigma G hG g) ≤
      rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) := sorry

-- Proof sketch: compare the function
-- `σ ↦ log (1 + σ) - σ / (1 + σ) - σ^2 / ((1 + σ) (2 + σ))`
-- with `0` by differentiating and checking that its derivative is nonnegative on `σ ≥ 0`.
/-- If `2 ≤ n` and `σ = (1 / n) ‖g‖_{G,*}^2 - 1` is positive, then the optimal value of `V` is
bounded below by `σ² / ((1 + σ) (2 + σ))`. -/
theorem rankOneUpdatePotential_optimalAlpha_lower_bound_rational
    (G : Mat) (hG : G.PosDef) (g : E) (hn : 2 ≤ n)
    (hσ : 0 < rankOneUpdateSigma G hG g) :
    (rankOneUpdateSigma G hG g ^ (2 : ℕ)) /
        ((1 + rankOneUpdateSigma G hG g) * (2 + rankOneUpdateSigma G hG g)) ≤
      rankOneUpdatePotential G hG g (rankOneUpdateOptimalAlpha G hG g) := sorry

/-! ### Proposition_7_4 (from Chap07) -/
noncomputable section

open Asymptotics
open Filter

local notation "DimPair" => ℕ × ℕ

/- Proposition 7.4 lies in the chapter's support-function smoothing / one-step work asymptotics
domain.

Sampled owner-style declarations:
- `SupportFunctionSmoothingMethod` in `Algorithm_7_3`, the chapter owner of Method `S_N(R)`;
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- `restrictedDimensionFilter` in `Proposition_7_6.lean`, the chapter owner of the admissible
  dimension regime `0 < p < n (n + 1) / 2` with `n → ∞`;
- `frobeniusGramPreliminaryArithmeticWorkBound` in `Proposition_7_5.lean`, the nearby
  source-facing work owner for the Frobenius-Gram subroutine that contributes to one step of the
  method.

Best owner abstraction:
- source-facing: the direct one-step work profile
  `(n, p) ↦ gradientWork (n, p) + projectionWork (n, p) + auxiliaryWork (n, p)`;
- core/canonical: `Asymptotics.IsBigO` on `restrictedDimensionFilter`;
- bridge/view: none beyond reading the source prose as the sum of its three component costs.

Primitive data:
- the three component cost profiles for one step of the method.

Derived API:
- the final `=O` bound by `n^2 (n + p)` on the chapter's restricted-dimension filter.

There is no genuine upstream owner in this chapter for the arithmetic work of one Algorithm 7.3
iteration. The previous version introduced a namespace-packaged alias for the sum of three
arbitrary profiles, but that alias carried no additional method data and violated the no-wrapper
rule. This refinement therefore keeps the proposition directly on the source-facing sum profile
while still reusing the canonical filter owner `restrictedDimensionFilter` from Proposition 7.6.
-/

-- Proof sketch: add the three assumed `O`-bounds for the gradient, projection, and auxiliary
-- vector computations. On the restricted regime `p < n (n + 1) / 2`, the quadratic term `p^2`
-- is absorbed by `n^3 + n^2 p`, and `n^3 + n^2 p = n^2 (n + p)`.
/-- Proposition 7.4: along the restricted-dimension regime where `n → ∞` and
`0 < p < n (n + 1) / 2`, if one iteration of Method `S_N(R)` has gradient work
`O(p n^2)`, Frobenius-projection work `O(n^3)`, and auxiliary `ℝ^p` arithmetic work `O(p^2)`,
then the total one-step arithmetic work, obtained by summing those three component profiles, is
`O(n^2 (n + p))`. -/
theorem supportFunctionSmoothingIterationWork_isBigO_n_sq_mul_n_add_p
    (gradientWork projectionWork auxiliaryWork : DimPair → ℝ)
    (hgradient : gradientWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ)))
    (hprojection : projectionWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (3 : ℕ)))
    (hauxiliary : auxiliaryWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.2 : ℝ) ^ (2 : ℕ))) :
    (fun dims ↦ gradientWork dims + projectionWork dims + auxiliaryWork dims) =O[
      restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2)) := by
  sorry

end

/-! ### Theorem_7_4 (from Chap07) -/
universe u

section

variable {X : Type u}

/- Theorem 7.4 lies in the chapter's relative-accuracy / lower-level direct-scheme domain.

Sampled owner-style declarations:
- `aPrioriRadiusEstimate` in `Definition_7_9.lean`, the Chapter 7 owner for the scalar radius
  parameter used by the lower-level scheme;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for relative-value accuracy;
- `relativeScaleSubgradientApproximationStep` in `Algorithm_7_2.lean`, which uses the same
  lower-level scheme surface `ℕ → ℝ → X`;
- `subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value` in
  `Theorem_7_2.lean`, the sibling one-shot relative-value conversion theorem.

Best owner abstraction:
- source-facing: Theorem 7.4's conversion of the stagewise direct-structure gap estimate into a
  one-shot relative-value bound at a floor-chosen index;
- core/canonical: a lower-level scheme `S : ℕ → ℝ → X` evaluated at the Chapter 7 radius owner
  `aPrioriRadiusEstimate f γ0 x0`;
- bridge/view: the specific stage index `⌊2 / (α² δ)⌋`, with `IsRelativeAccuracy` remaining the
  ambient chapter owner for the stronger two-sided notion.

Primitive data:
- `f`, `S`, `x0`, `α`, `γ0`, `δ`, and `fStar`;
- the stagewise gap estimate for `f (S k (aPrioriRadiusEstimate f γ0 x0))`;
- the source proof's comparison `α * f x0 ≤ fStar`.

Derived API:
- the floor-chosen stage `⌊2 / (α² δ)⌋`;
- the final upper bound `f (S_N (aPrioriRadiusEstimate f γ0 x0)) ≤ (1 + δ) fStar`.

Source/core/bridge triage:
- source-facing: the theorem's upper-bound conclusion at the chosen stage;
- core/canonical: `aPrioriRadiusEstimate` and the lower-level scheme surface `ℕ → ℝ → X`;
- bridge/view: the arithmetic passage from the stagewise coefficient `2 / (α² (k + 1))` to the
  target coefficient `δ`.

The theorem is the Chapter 7 arithmetic conversion step, so it should expose the source proof's
primitive comparison `α * f x0 ≤ fStar` rather than hiding it inside an already-normalized
`fStar`-scaled estimate. The ambient Euclidean and convex-analytic setup belongs to the
construction of the direct-structure scheme and its gap bound, not to this conversion lemma
itself, so those stronger assumptions are omitted here.
-/

-- Proof sketch: evaluate the assumed gap estimate at
-- `N = Nat.floor (2 / (α ^ (2 : ℕ) * δ))`. The floor inequality implies
-- `2 / (α ^ (2 : ℕ) * (N + 1 : ℝ)) ≤ δ`, so the gap is at most `δ * (α * f x0)`. Then use the
-- source comparison `α * f x0 ≤ fStar` to get
-- `f (S N (aPrioriRadiusEstimate f γ0 x0)) - fStar ≤ δ * fStar`, which rearranges to the claimed
-- upper bound.
/-- Theorem 7.4 [Chapter7_1.json:27]: if `α` and `δ` are positive, the Chapter 7 normalization
`α * f(x₀) ≤ f*` holds, and every direct-structure iterate at radius
`aPrioriRadiusEstimate f γ0 x0 = (1 / γ₀(F)) f(x₀)` satisfies the gap estimate
`f (S_k ((1 / γ₀(F)) f(x₀))) - f* ≤ (2 / (α(F)^2 (k + 1))) * α(F) * f(x₀)`, then the iterate
with index `⌊2 / (α(F)^2 δ)⌋` satisfies
`f (S_N ((1 / γ₀(F)) f(x₀))) ≤ (1 + δ) f*`. -/
theorem direct_structure_iterate_value_le_one_add_delta_mul_optimal_value
    (f : X → ℝ) (S : ℕ → ℝ → X) (x0 : X) (α γ0 δ fStar : ℝ)
    (hα : 0 < α) (hδ : 0 < δ)
    (hOptimalValue_lower : α * f x0 ≤ fStar)
    (hEstimate :
      ∀ k : ℕ,
        f (S k (aPrioriRadiusEstimate f γ0 x0)) - fStar ≤
          (2 / (α ^ (2 : ℕ) * (k + 1 : ℝ))) * (α * f x0)) :
    f (S (Nat.floor (2 / (α ^ (2 : ℕ) * δ))) (aPrioriRadiusEstimate f γ0 x0)) ≤
      (1 + δ) * fStar := sorry

end
