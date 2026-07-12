import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Lemma_3_2_7
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_23
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_26
import LecturesConvexOptimization_Nesterov_2018.Chap07.Proposition_7_8

-- Declarations for this item will be appended below by the statement pipeline.

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
