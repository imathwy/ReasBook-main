import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_5 (from Chap07) -/
noncomputable section

universe u

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

local notation "P" => ℝ × E

/- Definition 7.5 lies in the perspective-homogenization / unconstrained-minimization domain.

Sampled owner-style declarations:
* `perspectiveCone` in `Chap03/Remark_3_1_2_3`, the project owner of the positive cone supporting
  homogenized objectives;
* `perspectiveTransform` in `Chap03/Remark_3_1_2_3`, the project owner of the homogenized
  objective `(τ, y) ↦ τ φ(τ⁻¹ • y)`;
* `perspectiveTransform_isPositivelyHomogeneousOn` in `Chap03/Remark_3_1_2_3`, the canonical
  positive-scaling law for that homogenized objective on `perspectiveCone`;
* `IsMinOn f Set.univ x` and `isMinOn_univ_iff` in mathlib, the canonical whole-space minimizer
  language for the original problem.

Best owner abstraction:
* source-facing: the homogenized objective as the perspective transform on the perspective cone;
* core/canonical: `perspectiveTransform` together with
  `IsPositivelyHomogeneousOn 1 (perspectiveCone E : Set P)`;
* bridge/view: the unit slice `{z : P | z.1 = 1}` recovering the original objective.

Primitive data:
* the original objective `φ : E → ℝ`;
* the canonical cone owner `perspectiveCone E`;
* the canonical homogenized objective `perspectiveTransform φ`.

Derived API:
* the positive-homogeneity theorem on `perspectiveCone E`;
* evaluation on the unit slice `(1, y)`;
* the equivalence between minimizing `φ` on `E` and minimizing `perspectiveTransform φ` on the
  unit slice.

Source/core/bridge triage:
* source-facing: the homogenized perspective objective;
* core/canonical: `perspectiveTransform` on `perspectiveCone`;
* bridge/view: the unit-slice minimization statement.

The previous version collapsed Definition 7.5 to a Chapter 1
`SetConstrainedMinimizationProblem` on the affine slice `τ = 1`. That lost the chapter's actual
owner layer: the conic/perspective homogenization itself. This file therefore recalls the existing
project owner `perspectiveTransform` as the main entry and keeps the slice description only as a
bridge back to the original unconstrained problem.
-/

/- Definition 7.5: the homogenized objective of `φ` is the existing perspective transform on
`ℝ × E`, with its natural cone domain `perspectiveCone E`. -/
recall perspectiveCone
recall perspectiveTransform
recall perspectiveTransform_isPositivelyHomogeneousOn

/-- On the unit slice `τ = 1`, the perspective transform recovers the original objective `φ`. -/
@[simp] theorem perspectiveTransform_apply_one (φ : E → ℝ) (y : E) :
    perspectiveTransform φ (1, y) = φ y := by
  simp [perspectiveTransform, zero_lt_one]

/-- Minimizing `φ` on `E` is equivalent to minimizing its homogenized perspective transform on the
unit slice `τ = 1`. -/
theorem isMinOn_univ_iff_isMinOn_perspectiveTransform_unitSlice {φ : E → ℝ} {y : E} :
    IsMinOn φ Set.univ y ↔
      IsMinOn (perspectiveTransform φ) {z : P | z.1 = 1} (1, y) := by
  constructor
  · intro hy
    rw [isMinOn_iff]
    intro z hz
    rcases z with ⟨τ, x⟩
    have hy' : ∀ x : E, φ y ≤ φ x := isMinOn_univ_iff.mp hy
    have hτ : τ = 1 := hz
    subst hτ
    simpa using hy' x
  · intro hy
    rw [isMinOn_univ_iff]
    intro x
    have hx : (1, x) ∈ ({z : P | z.1 = 1} : Set P) := rfl
    simpa using (isMinOn_iff.mp hy) (1, x) hx

end

/-! ### Lemma_7_5 (from Chap07) -/
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

/-! ### Proposition_7_5 (from Chap07) -/
noncomputable section

open Matrix

variable {p n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 7.5 lies in the chapter's Frobenius-Gram / dense arithmetic-cost domain.

Sampled owner-style declarations:
- `Matrix.gram` in mathlib, the canonical Frobenius Gram-matrix owner for a family of
  coefficient matrices;
- `matrix_gram_apply_eq_entrywise_sum` in `Chap07/Definition_7_21`, the Chapter 7 bridge from
  that owner to the textbook Frobenius double sum;
- `linearMatrixGramOperator_toMatrixOrthonormal` in `Chap07/Definition_7_21`, the bridge from the
  source-facing operator `G = L†L` to its Gram matrix;
- `gramMatrix` in `Chap07/Proposition_7_24`, another use of the same canonical Gram owner.

Best owner abstraction:
- source-facing: the preliminary arithmetic-work bound for forming the Frobenius Gram matrix and
  inverting it;
- core/canonical: `Matrix.gram ℝ` on matrix-entry coordinates;
- bridge/view: `matrix_gram_apply_eq_entrywise_sum`.

Primitive data:
- `n`, `p : ℕ`.

Derived API:
- the canonical Frobenius Gram owner `Matrix.gram ℝ`;
- the parameter-only arithmetic-work expression
  `frobeniusGramPreliminaryArithmeticWorkBound n p`;
- its explicit expansion and regime-specific quadratic bound.

Source/core/bridge triage:
- source-facing: the arithmetic complexity statement of Proposition 7.5;
- core/canonical: `Matrix.gram ℝ`;
- bridge/view: the entrywise identity `matrix_gram_apply_eq_entrywise_sum`.

The previous file kept local raw-matrix inner-product scaffolding just to mention the Gram owner.
This refinement deletes that scaffolding and reuses the Chapter 7 Frobenius Gram owner directly,
leaving this file to own only the new arithmetic-work model and its asymptotic consequence.
-/

section

variable (p n)

/- Proposition 7.5 uses the canonical Frobenius Gram-matrix owner. -/
set_option linter.hashCommand false in
#check (Matrix.gram ℝ : (Fin p → Mₙ) → Matrix (Fin p) (Fin p) ℝ)

end

/-- A dimension-only arithmetic upper bound for the preliminary computation that first forms the
Frobenius Gram matrix of a family of coefficient matrices and then computes its inverse. -/
def frobeniusGramPreliminaryArithmeticWorkBound (n p : ℕ) : ℕ :=
  p ^ 2 * n ^ 2 + p ^ 3

/-- Expanding `frobeniusGramPreliminaryArithmeticWorkBound n p` recovers the sum of the
Gram-matrix formation cost `p^2 n^2` and the matrix-inversion cost `p^3`. -/
-- Proof sketch: unfold `frobeniusGramPreliminaryArithmeticWorkBound`.
theorem frobeniusGramPreliminaryArithmeticWorkBound_eq
    (n p : ℕ) :
    frobeniusGramPreliminaryArithmeticWorkBound n p = p ^ 2 * n ^ 2 + p ^ 3 :=
  sorry

-- Proof sketch: use `hpn` to deduce `p < n^2`, hence `p^3 ≤ p^2 n^2`, and then absorb the
-- inversion term into the explicit preliminary-work expression
-- `p^2 n^2 + p^3`.
/-- The preliminary arithmetic-work model is bounded by `2 p^2 n^2` on the admissible regime
`p < n (n + 1) / 2`. -/
theorem frobeniusGramPreliminaryArithmeticWorkBound_le_two_mul
    {n p : ℕ} (hpn : p < n * (n + 1) / 2) :
    frobeniusGramPreliminaryArithmeticWorkBound n p ≤ 2 * (p ^ 2 * n ^ 2) := sorry

-- Proof sketch: take the constant witness `C = 2` and apply the explicit upper bound above.
/-- Proposition 7.5 [Chapter7_2.json:38]: if `A₁, …, Aₚ ∈ ℝ^(n × n)` and `G` is the Frobenius
Gram matrix with entries `G^(i,j) = ⟪Aᵢ, Aⱼ⟫_F`, then under the size condition
`p < n(n + 1) / 2` the preliminary computation modeled by
`frobeniusGramPreliminaryArithmeticWorkBound n p` has total arithmetic work bounded by a constant
multiple of `p^2 n^2`, i.e. of order `O(p^2 n^2)`. -/
theorem frobeniusGramPreliminaryArithmeticWork_has_quadratic_bound
    {n p : ℕ} (hpn : p < n * (n + 1) / 2) :
    ∃ C : ℕ,
      frobeniusGramPreliminaryArithmeticWorkBound n p ≤ C * (p ^ 2 * n ^ 2) := sorry

end

/-! ### Theorem_7_5 (from Chap07) -/
noncomputable section

universe u

section

variable {X : Type u}
variable {f : X → ℝ} {S : ℕ → ℝ → X} {x0 xStar : X} {δ alphaF gamma0F : ℝ}

/- Theorem 7.5 lies in Chapter 7's relative-scale restarting / stopping-time domain.

Sampled owner-style declarations:
- `schemeSNRestartingIterate`, `schemeSNRestartingStoppingIndex`, and
  `schemeSNRestartingStoppingTime` in `Algorithm_7_4.lean`, which already own the canonical
  restart orbit and its first accepted stage;
- `relativeScaleSubgradientApproximation_stopping_time_bound` in `Theorem_7_3.lean`, the nearby
  chapter pattern where the theorem is stated directly on the canonical stopping-time owner;
- `IsMinOn` from mathlib, the canonical minimizer predicate needed to express the hidden optimal
  value comparison from the source proof.

Best owner abstraction:
- source-facing: the bound on the number `T` of restart points generated by Algorithm 7.4;
- core/canonical: `schemeSNRestartingStoppingTime hTerminate`;
- bridge/view: the minimizer witness `xStar` and the normalization inequality
  `alphaF * f x0 ≤ f xStar`, which package the source proof's comparison with the optimal value.

The source item is a single stopping-time estimate, so the public API here is one theorem stated
directly on the canonical stopping-time owner, with no extra packaging or auxiliary work-count
interface.
-/

variable (hTerminate : schemeSNRestartingTerminates S f x0 δ alphaF gamma0F)

-- Proof sketch: for every `t < schemeSNRestartingStoppingTime hTerminate - 1`,
-- `schemeSNRestartingStoppingIndex_min` shows that the restart orbit contracts by the factor
-- `1 / e`. Iterating this strict decay up to the last pre-accepted stage bounds
-- `f (x̂_{T-1})` by `exp (-(T - 1)) * f x0`. Since `xStar` is a global minimizer, one has
-- `f xStar ≤ f (x̂_{T-1})`; combining this with the normalization inequality
-- `alphaF * f x0 ≤ f xStar` and `0 < f x0` yields `alphaF ≤ exp (-(T - 1))`, hence
-- `(T : ℝ) ≤ 1 + log (1 / alphaF)`.
/-- Theorem 7.5 [Chapter7_1.json:29]: if Algorithm 7.4 terminates at its canonical stopping time
and `xStar` is a global minimizer whose value satisfies the homogeneous-model normalization
`alphaF * f(x₀) ≤ f(xStar)`, then the number `T` of generated restart points is bounded by
`1 + log (1 / alphaF)`. -/
theorem schemeSNRestarting_stopping_time_bound
    (hAlphaF_pos : 0 < alphaF)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : alphaF * f x0 ≤ f xStar) :
    (schemeSNRestartingStoppingTime hTerminate : ℝ) ≤ 1 + Real.log (1 / alphaF) := sorry

end
