import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators InnerProduct

universe u v

variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "E₂" => EuclideanSpace ℝ ι

/- Proposition 6.32 [Chapter6_1.json:101] lies in the finite Euclidean affine-minorant /
quadratic-dualization domain.

Sampled owner-style declarations:
- `EuclideanSpace.proj`, the canonical coordinate functionals on `EuclideanSpace ℝ ι`;
- `ContinuousLinearMap.smulRight`, the canonical way to assemble the row family
  `u ↦ ∑ⱼ uⱼ gⱼ` into one linear map;
- `ContinuousLinearMap.adjoint`, written `A†`, the canonical Hilbert adjoint owner;
- mathlib `HasGradientAt`, the canonical global-gradient owner for scalar functions on real
  inner-product spaces.

Best owner abstraction:
- source-facing: the offset vector `b`, the map `Aᵀ`, its adjoint `A`, and the minimization
  objective `φ`;
- core/canonical: `EuclideanSpace ℝ ι`, `ContinuousLinearMap.adjoint`, and `HasGradientAt`;
- bridge/view: the coordinate formulas for `b` and for the adjoint action `Ax`.

Primitive data:
- the row family `g : ι → E`;
- the base points `points : ι → E`;
- the affine offsets `f : ι → ℝ`.

Derived API:
- the Euclidean offset vector `b`;
- the linear map `Aᵀ : E₂ →L[ℝ] E` with `Aᵀ u = ∑ⱼ uⱼ gⱼ`;
- its adjoint `A : E →L[ℝ] E₂`;
- the dual objective `φ(u)` as the infimum of the quadratic affine minorants.

The source is intrinsically finite-dimensional on both sides. This file keeps that source-facing
surface, with `E₂ = EuclideanSpace ℝ ι` and `E` a finite-dimensional real inner-product space,
instead of rebuilding a matrix-only wrapper.
-/

/-- The offset vector `b` with coordinates `bⱼ = ⟪gⱼ, xⱼ⟫ - fⱼ`. -/
def affine_minorant_offset (g points : ι → E) (f : ι → ℝ) : E₂ :=
  (EuclideanSpace.equiv ι ℝ).symm fun j ↦ inner ℝ (g j) (points j) - f j

/-- The row operator `Aᵀ : EuclideanSpace ℝ ι →L[ℝ] E` with
`Aᵀ u = ∑ⱼ uⱼ gⱼ`. -/
def affine_minorant_adjointMap (g : ι → E) : E₂ →L[ℝ] E :=
  ∑ j : ι, (EuclideanSpace.proj j).smulRight (g j)

/-- The Hilbert adjoint `A : E →L[ℝ] EuclideanSpace ℝ ι` of `affine_minorant_adjointMap g`. -/
def affine_minorant_rowMap (g : ι → E) : E →L[ℝ] E₂ :=
  (affine_minorant_adjointMap g)†

/-- The quadratic affine minimand
`x ↦ ∑ⱼ uⱼ (fⱼ + ⟪gⱼ, x - xⱼ⟫) + (1 / 2) ‖x‖²`. -/
def affine_minorant_dualObjectiveMinimand
    (g points : ι → E) (f : ι → ℝ) (u : E₂) : E → ℝ :=
  fun x ↦
    (∑ j : ι, u j * (f j + inner ℝ (g j) (x - points j))) +
      (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)

/-- The dual objective `φ(u)`, defined as the infimum of the quadratic affine minorants over
all `x : E`. -/
def affine_minorant_dualObjective (g points : ι → E) (f : ι → ℝ) : E₂ → ℝ :=
  fun u ↦ sInf (Set.range (affine_minorant_dualObjectiveMinimand g points f u))

-- Proof sketch: expand the affine term, rewrite the linear part as
-- `⟪Aᵀ u, x⟫ - ⟪b, u⟫`, and complete the square in `x`; the minimizer is `x = -Aᵀ u`.
/-- Proposition 6.32 [Chapter6_1.json:101] (1): the infimum defining `φ(u)` is the explicit
quadratic expression `-⟪b, u⟫ - (1 / 2) ‖Aᵀ u‖²`. -/
theorem affine_minorant_dualObjective_eq_neg_inner_offset_sub_half_norm_sq
    (g points : ι → E) (f : ι → ℝ) (u : E₂) :
    affine_minorant_dualObjective g points f u =
      -inner ℝ (affine_minorant_offset g points f) u -
        (1 / 2 : ℝ) * ‖affine_minorant_adjointMap g u‖ ^ (2 : ℕ) := sorry

-- Proof sketch: first rewrite `φ` by the closed formula above, then differentiate the linear term
-- and the negative quadratic norm term; the latter contributes `-A(Aᵀ u)`.
/-- Proposition 6.32 [Chapter6_1.json:101] (2): the dual objective is differentiable on
`EuclideanSpace ℝ ι`, and at every `u` its gradient is `-b - A(Aᵀ u)`, encoded by the canonical
pointwise owner `HasGradientAt`. -/
theorem affine_minorant_dualObjective_hasGradientAt
    (g points : ι → E) (f : ι → ℝ) (u : E₂) :
    HasGradientAt
      (affine_minorant_dualObjective g points f)
      (-affine_minorant_offset g points f -
        affine_minorant_rowMap g (affine_minorant_adjointMap g u))
      u := sorry
