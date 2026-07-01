import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

/-
Lemma 6.2.3 lies in the Chapter 6 smoothed dual / excessive-gap domain.

Sampled owner-style declarations:
- mathlib `IsMinOn`, the canonical minimizer owner for the two prox subproblems;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Chap02/Definition_2_2`, the chapter
  owner for the convex first-order lower bound used at `x₀`;
- `smoothedDualObjectiveMinimand` in `Chap06/Definition_6_32`, the nearby chapter owner showing
  that the primal prox point should be treated through its minimizing property rather than through
  an auxiliary wrapper;
- `IsSmoothedDualMinimizerSelection.isMinOn` in `Chap06/Definition_6_33`, the pointwise Chapter 6
  bridge from a selector to the actual minimizer property.

Best owner abstraction:
- core/canonical: the actual chosen points `uBar` and `xμ₁uBar` together with their
  `IsMinOn`-based minimizing data.

Primitive data:
- the feasible set `Q₁`, the smoothed objective `fμ₂`, the prox term `d₁`, and the points
  `x₀`, `xBar`, `uBar`, `xμ₁uBar`;
- the convexity and gradient data at `x₀`;
- the minimizing properties of `xBar` and `xμ₁uBar` for the two linearized prox models;
- the identity expressing `φμ₁ uBar`.

Derived API:
- the excessive-gap inequality `fμ₂ xBar ≤ φμ₁ uBar`.

Source/core/bridge triage:
- source-facing: the excessive-gap inequality for one chosen smoothed pair;
- core/canonical: the minimizer owners `IsMinOn` at the specific points `xBar` and `xμ₁uBar`;
- bridge/view: the identity giving `φμ₁ uBar` in terms of the selected prox point.

The previous statement kept whole selector functions `uμ₂` and `xμ₁` plus an auxiliary subtype
`Q₂`, even though the theorem only used the single values `uμ₂ x₀` and `xμ₁ (uμ₂ x₀)`. This is
not chapter-canonical data: the mathematics depends only on the chosen dual point and chosen prox
point together with their minimizing properties. The refined owner theorem therefore keeps those
points directly and deletes the parallel selector-function layer.
-/

-- Proof sketch: convexity of `fμ₂` and the gradient hypothesis give the affine lower bound
-- at `xBar`. Combining that bound with the minimizing property of `xBar` for the
-- `Lfμ₂`-weighted linearized prox model yields
-- `fμ₂ xBar ≤ fμ₂ x₀ + Lfμ₂ * (d₁ x₀ - d₁ xBar)`. The minimizing property of
-- `xμ₁uBar` for the `μ₁`-weighted model and the inequality `Lfμ₂ ≤ μ₁` then imply
-- `d₁ xμ₁uBar ≤ d₁ xBar`, and substituting this into the displayed identity for `φμ₁ uBar`
-- gives the excessive-gap inequality.
/-- Lemma 6.2.3: if `xBar ∈ Q₁` minimizes the linearized prox model
`x ↦ ⟪∇ f_{μ₂}(x₀), x - x₀⟫ + L₁(f_{μ₂}) d₁(x)` and `u_{μ₂}(x₀)` satisfies the standard
smoothed-gap identity through the selected primal prox point `xμ₁uBar`, then every
`μ₁ ≥ L₁(f_{μ₂})` yields the excessive-gap inequality `f_{μ₂}(xBar) ≤ φ_{μ₁}(uBar)`. -/
theorem smoothed_pair_excessive_gap_of_linearized_prox_minimizers
    {Q₁ : Set E₁} {fμ₂ : E₁ → ℝ} {φμ₁ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {x₀ xBar xμ₁uBar : Q₁} {uBar : E₂} {μ₁ Lfμ₂ : ℝ}
    (hconv : ConvexOn ℝ Q₁ fμ₂)
    (hfμ₂_grad : HasGradientWithinAt fμ₂ (gradientWithin fμ₂ Q₁ x₀) Q₁ x₀)
    (hbar_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) (x - x₀) + Lfμ₂ * d₁ x)
        Q₁
        xBar)
    (hxμ₁_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) x + μ₁ * d₁ x)
        Q₁
        xμ₁uBar)
    (hφμ₁ :
      φμ₁ uBar =
        fμ₂ x₀ + μ₁ * (d₁ x₀ - d₁ xμ₁uBar))
    (hμ₁ : Lfμ₂ ≤ μ₁) :
    fμ₂ xBar ≤ φμ₁ uBar := sorry

end
