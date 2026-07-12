import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

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
