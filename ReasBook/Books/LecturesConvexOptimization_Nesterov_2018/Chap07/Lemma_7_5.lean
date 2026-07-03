import Mathlib
import Nesterov.Chap07.Definition_7_30
import Nesterov.Chap07.Definition_7_31

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm OneSidedHullNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.5 lies in Chapter 7's one-sided rounding / scalar interval-maximizer domain.

Sampled owner-style declarations:
- `IsMaxOn`, the canonical mathlib owner for interval maximizers;
- `centralSymmetryRoundingAlphaStar_mem_Ico` and
  `centralSymmetryRoundingObjective_isMaxOn_iff` in `Proposition_7_8`, the nearby chapter scalar
  maximizer pattern with the same interval-feasibility issue;
- `oneSidedRoundingUpdatedMatrix` in `Definition_7_31`, the source-facing matrix-path owner whose
  determinant ratio is encoded by the scalar potential below;
- `convexHullOfWeightedUnitBallAndPoint` and its support-function theorem in `Definition_7_30`,
  the source-facing geometric owner for the one-sided containment statement.

Best owner abstraction:
- source-facing: the one-sided scalar potential `V`, its parameter `σ`, and the critical point
  `α*`;
- core/canonical: `IsMaxOn` on `Set.Ico (0 : ℝ) 1`;
- bridge/view: the ellipsoid-containment and determinant-ratio theorems connecting the scalar owner
  to the matrix-level source objects; the translated ellipsoid center belongs to this theorem layer
  because the source formula only makes sense under the nonzero-radius hypothesis.

Primitive data:
- a positive-definite matrix owner `G`;
- a vector `g`;
- a scalar parameter `α`.

Derived API:
- the auxiliary scalar `σ = (r - n) / (n + 1)`;
- the explicit candidate maximizer `α*`;
- theorem-level interval feasibility, maximizer, value, and lower-bound consequences.
- theorem-level translated-ellipsoid consequences under `r = ‖g‖[G,*] ≠ 0`.

The dimension lower bound belongs to the theorem layer rather than the data layer: it is needed to
ensure that the explicit `α*` really lies in `[0, 1)` and that the closed-form logarithmic value is
well-defined, but it is not part of the owner definitions themselves. -/

/-- The logarithmic determinant potential
`V(α) = log (det G(α) / det G(0)) = 2 log (1 + α (r - 1) / 2) + (n - 1) log (1 - α)`
written with the canonical dual radius `r = ‖g‖*_G`. -/
def oneSidedRoundingPotential
    (G : {A : Mat // A.PosDef}) (g : E) (α : ℝ) : ℝ :=
  2 * Real.log (1 + α * ((‖g‖[G,*] - 1) / 2)) +
    ((n : ℝ) - 1) * Real.log (1 - α)

-- Proof sketch: unfold `oneSidedRoundingPotential`.
/-- Expanding `oneSidedRoundingPotential G g α` gives the explicit scalar formula for `V(α)`. -/
theorem oneSidedRoundingPotential_def
    (G : {A : Mat // A.PosDef}) (g : E) (α : ℝ) :
    oneSidedRoundingPotential G g α =
      2 * Real.log (1 + α * ((‖g‖[G,*] - 1) / 2)) +
        ((n : ℝ) - 1) * Real.log (1 - α) :=
  rfl

/-- The canonical quantity `σ = (r - n) / (n + 1)` attached to the dual radius
`r = ‖g‖*_G`. -/
def oneSidedRoundingSigma
    (G : {A : Mat // A.PosDef}) (g : E) : ℝ :=
  (‖g‖[G,*] - (n : ℝ)) / ((n : ℝ) + 1)

-- Proof sketch: unfold `oneSidedRoundingSigma`.
/-- Expanding `oneSidedRoundingSigma G g` recovers `(r - n) / (n + 1)` with `r = ‖g‖*_G`. -/
theorem oneSidedRoundingSigma_def
    (G : {A : Mat // A.PosDef}) (g : E) :
    oneSidedRoundingSigma G g =
      (‖g‖[G,*] - (n : ℝ)) / ((n : ℝ) + 1) :=
  rfl

/-- The candidate maximizer
`α* = (2 / (n + 1)) ((r - n) / (r - 1))`
for the one-sided rounding potential, with `r = ‖g‖*_G`. -/
def oneSidedRoundingAlphaStar
    (G : {A : Mat // A.PosDef}) (g : E) : ℝ :=
  ((2 : ℝ) / ((n : ℝ) + 1)) *
    ((‖g‖[G,*] - (n : ℝ)) / (‖g‖[G,*] - 1))

-- Proof sketch: use `2 ≤ n` and `r ≥ n` to obtain `1 < r`, then verify directly that
-- `0 ≤ (2 / (n + 1)) ((r - n) / (r - 1)) < 1`.
/-- If `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then the explicit critical point `α*` lies in
the interval `[0, 1)`. -/
theorem oneSidedRoundingAlphaStar_mem_Ico
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingAlphaStar G g ∈ Set.Ico (0 : ℝ) 1 := sorry

-- Proof sketch: compare support functions, using
-- `ξ[C_[g](G)] x = max {ξ[W₁(G)] x, ⟪g, x⟫}` and the explicit support function of the translated
-- ellipsoid `W[1]((((r - 1) / (2r)) * α) • g, oneSidedRoundingUpdatedMatrix G g α)` with
-- `r = ‖g‖[G,*] ≠ 0`.
/-- The one-sided ellipsoid `E_α`, viewed through the Chapter 7 owner
`W[1]((((r - 1) / (2r)) * α) • g, oneSidedRoundingUpdatedMatrix G g α)` with
`r = ‖g‖[G,*] ≠ 0`, is contained in the convex hull `C_[g](G)` for every
`α ∈ [0, 1)`. -/
theorem oneSidedRoundingEllipsoid_subset_convexHullOfWeightedUnitBallAndPoint
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    W[1](((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) • g),
      (oneSidedRoundingUpdatedMatrix G g α)) ⊆
      C_[g](G) := sorry

-- Proof sketch: use the matrix determinant lemma on `oneSidedRoundingUpdatedMatrix G g α` and the
-- direct weighted-dual-norm formula `r = ‖g‖[G,*]` to rewrite the determinant ratio in closed
-- form.
/-- The scalar potential `V(α)` agrees with the logarithmic determinant ratio
`log (det G(α) / det G)`. -/
theorem oneSidedRoundingPotential_eq_log_det_ratio
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    oneSidedRoundingPotential G g α =
      Real.log (Matrix.det (oneSidedRoundingUpdatedMatrix G g α) / Matrix.det G.1) := sorry

-- Proof sketch: differentiate the explicit formula for `oneSidedRoundingPotential G g` on
-- `[0, 1)`, solve the first-order condition, and use concavity to conclude that the displayed
-- critical point is the maximizer.
/-- Lemma 7.5: if `2 ≤ n` and the dual radius `r = ‖g‖*_G` satisfies `r ≥ n`, then the potential
`V(α) = 2 log (1 + α (r - 1) / 2) + (n - 1) log (1 - α)` attains its maximum on `[0, 1)` at
`α* = (2 / (n + 1)) ((r - n) / (r - 1))`. -/
theorem oneSidedRoundingPotential_isMaxOn_alphaStar
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    IsMaxOn (oneSidedRoundingPotential G g) (Set.Ico (0 : ℝ) 1)
      (oneSidedRoundingAlphaStar G g) := sorry

-- Proof sketch: substitute `oneSidedRoundingAlphaStar G g` into the explicit formula for
-- `oneSidedRoundingPotential G g` and simplify the two logarithmic arguments.
/-- If `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then evaluating the one-sided rounding
potential at `α*` gives the closed formula from the lemma. -/
theorem oneSidedRoundingPotential_alphaStar_value
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) =
      2 * Real.log
          ((‖g‖[G,*] - 1) / ((n : ℝ) + 1)) +
        ((n : ℝ) - 1) *
          Real.log
            ((((n : ℝ) - 1) * (‖g‖[G,*] + 1)) /
              (((n : ℝ) + 1) * (‖g‖[G,*] - 1))) := sorry

-- Proof sketch: rewrite the value from `oneSidedRoundingPotential_alphaStar_value` in terms of
-- `σ = (r - n) / (n + 1)` and apply the scalar lower bound
-- `log (1 + σ) - σ / (1 + σ) ≤ ...`.
/-- If `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then the optimal value of the one-sided
rounding potential is bounded below by
`2 (log (1 + σ) - σ / (1 + σ))`, where `σ = (r - n) / (n + 1)`. -/
theorem oneSidedRoundingPotential_alphaStar_lower_bound_log
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    2 *
        (Real.log (1 + oneSidedRoundingSigma G g) -
          oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g)) ≤
      oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) := sorry

-- Proof sketch: combine `oneSidedRoundingPotential_alphaStar_lower_bound_log` with the scalar
-- estimate
-- `log (1 + σ) - σ / (1 + σ) ≥ σ^2 / ((1 + σ) (2 + σ))`.
/-- If `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then the optimal value of the one-sided
rounding potential is bounded below by
`2 σ² / ((1 + σ) (2 + σ))`, where `σ = (r - n) / (n + 1)`. -/
theorem oneSidedRoundingPotential_alphaStar_lower_bound_rational
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    2 * (oneSidedRoundingSigma G g ^ (2 : ℕ)) /
        ((1 + oneSidedRoundingSigma G g) * (2 + oneSidedRoundingSigma G g)) ≤
      oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) := sorry

end
