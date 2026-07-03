import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_19 (from Chap06) -/
noncomputable section

universe u

/- Definition 6.19 lies in the chapter's primal-form smoothing / regularized-supremum domain.

Sampled owner-style declarations:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the Chapter 6 owner of the regularized
  maximand `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ d(u)`;
- `smoothedPrimalObjective` in `Definition_6_30`, the Chapter 6 owner of the corresponding
  supremum objective;
- `Definition_6_7`, which treats a source-facing smoothing definition as a direct specialization
  of `smoothedPrimalObjective` rather than introducing a parallel owner;
- `continuousLocationSmoothApproximation` in `Definition_6_16`, another thin source-facing
  specialization of the same owner.

Best owner abstraction:
- source-facing: the primal-form smoothed objective attached to the special dual penalty
  `u ↦ ⟪b, u⟫ + ⟪Bu, u⟫`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: the specialization `hatf = 0` and `hatφ u = b u + B u u`.

Primitive data:
- `B : E →L[ℝ] StrongDual ℝ E`;
- `Q : Set E`;
- `b : StrongDual ℝ E`;
- `d : E → ℝ`;
- `μ : ℝ`.

Derived API:
- the source-facing specialization `primalFormSmoothedObjective`;
- its owner-level expansion through `smoothedPrimalObjective_apply`;
- the explicit textbook supremum formula for the specialized maximand.

Source/core/bridge triage:
- source-facing: `primalFormSmoothedObjective`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: the companion theorems below expanding the specialization to the displayed formula.

The previous file introduced separate public owners for the linear term, the quadratic-linear
penalty, the maximand, and the final smoothed objective. Only the last object is source-facing
mathematics here; the others are just pieces of the chapter owner `smoothedPrimalObjective`.
This refinement deletes those duplicate wheels, keeps the source-facing specialization, and
derives the displayed formula directly from the canonical owner.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 6.19: in the primal-form smoothing specialization with `E₁ = E₂ = E`,
`Q₁ = Q₂ = Q`, `d₁ = d₂ = d`, and `A = B`, the smoothed subproblem `f_μ` is the Chapter 6
regularized-supremum owner specialized to the dual penalty `\hat φ(u) = ⟪b, u⟫ + ⟪Bu, u⟫`. -/
abbrev primalFormSmoothedObjective
    (B : E →L[ℝ] StrongDual ℝ E) (Q : Set E) (b : StrongDual ℝ E) (d : E → ℝ) (μ : ℝ) :
    E → ℝ :=
  smoothedPrimalObjective B Q 0 (fun u ↦ b u + B u u) d μ

/-- Expanding `primalFormSmoothedObjective` through the chapter owner gives the supremum of the
specialized regularized maximand over `Q`. -/
@[simp] theorem primalFormSmoothedObjective_def
    (B : E →L[ℝ] StrongDual ℝ E) (Q : Set E) (b : StrongDual ℝ E) (d : E → ℝ) (μ : ℝ) (x : E) :
    primalFormSmoothedObjective B Q b d μ x =
      sSup ((fun u : E ↦ B x u - (b u + B u u) - μ * d u) '' Q) := by
  simpa [primalFormSmoothedObjective, smoothedPrimalObjectiveMaximand] using
    smoothedPrimalObjective_apply B Q (0 : E → ℝ) (fun u : E ↦ b u + B u u) d μ x

/-- Evaluating `primalFormSmoothedObjective` recovers the textbook maximization oracle
`max_{u ∈ Q} {⟪Bx, u⟫ - μ d(u) - ⟪b, u⟫ - ⟪Bu, u⟫}`, encoded in Lean as a supremum over `Q`. -/
theorem primalFormSmoothedObjective_apply
    (B : E →L[ℝ] StrongDual ℝ E) (Q : Set E) (b : StrongDual ℝ E) (d : E → ℝ) (μ : ℝ) (x : E) :
    primalFormSmoothedObjective B Q b d μ x =
      sSup ((fun u : E ↦ B x u - μ * d u - b u - B u u) '' Q) := by
  have hmaximand :
      (fun u : E ↦ B x u - (b u + B u u) - μ * d u) =
        fun u : E ↦ B x u - μ * d u - b u - B u u := by
    funext u
    ring_nf
  rw [primalFormSmoothedObjective_def, hmaximand]

end

/-! ### Proposition_6_19 (from Chap06) -/
noncomputable section

open Module

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 6.19 lies in the chapter's minimax / dual-form smoothing domain.

Sampled owner-style declarations:
- `maximin_le_minimax` in `Chap01/Theorem_1_10_1`, the project owner of weak duality on indexed
  `⨅`/`⨆` expressions;
- `compact_convex_concave_minimax` in `Chap03/Theorem_3_37`, the chapter pattern of stating
  minimax results directly on slice-value expressions rather than through local value wrappers;
- `AffineVariationalInequalityProblem.gapFunction` in `Chap06/Definition_6_18`, the affine-VI
  owner whose ambient textbook formula is the same inner supremum surface when `B` comes from a
  packaged variational-inequality problem.

Best owner abstraction:
- source-facing: Proposition 6.19's sign-flipped dual-form smoothing representation;
- core/canonical: indexed `⨅`/`⨆` on the feasible subtype `Q` with values in `EReal`;
- bridge/view: the textbook pointwise payoffs `⟨B(v), w - v⟩` and `⟨B(v), v - w⟩`.

Primitive data:
- the feasible set `Q`;
- the operator field `B : E → Dual ℝ E`.

Derived API:
- the minimax value `⨅ w : Q, ⨆ v : Q, ⟪B(v), w - v⟫`;
- the maximin value `⨆ v : Q, ⨅ w : Q, ⟪B(v), w - v⟫`;
- the reversed minimax value `⨅ v : Q, ⨆ w : Q, ⟪B(v), v - w⟫`.

Source/core/bridge triage:
- source-facing: `dualFormSmoothingRepresentation`;
- core/canonical: the indexed `⨅`/`⨆` owners on `Q`;
- bridge/view: the pointwise sign-flip identity below.

The previous version rebuilt public owners for the payoff and for the three slice-value
expressions. This refinement deletes that duplicate wrapper layer and states the source-facing
theorem directly on the canonical indexed infimum/supremum surface.
-/

/-- The payoff `⟨B(v), w - v⟩` is the negative of the reversed payoff `⟨B(v), v - w⟩`. -/
theorem dualFormSmoothingPayoff_eq_neg_reversePayoff
    (B : E → Dual ℝ E) (w v : E) :
    ((B v (w - v) : ℝ) : EReal) = -((B v (v - w) : ℝ) : EReal) := by
  have hreal : (B v) (w - v) = -((B v) (v - w)) := by
    rw [show w - v = -(v - w) by abel, map_neg]
  exact_mod_cast hreal

/-- The maximin value of `⟨B(v), w - v⟩` equals the negative of the reversed minimax value of
`⟨B(v), v - w⟩`. -/
theorem dualFormSmoothingMaximinValue_eq_neg_reverseMinimaxValue
    (Q : Set E) (B : E → Dual ℝ E) :
    (⨆ v : Q, ⨅ w : Q, ((B v (w - v) : ℝ) : EReal)) =
      -⨅ v : Q, ⨆ w : Q, ((B v (v - w) : ℝ) : EReal) := sorry

/-- Proposition 6.19: if the extended-real minimax and maximin values of
`(w, v) ↦ ⟨B(v), w - v⟩` coincide, then that common value is also the negative of
`min_{v ∈ Q} max_{w ∈ Q} ⟨B(v), v - w⟩`. -/
theorem dualFormSmoothingRepresentation
    (Q : Set E) (B : E → Dual ℝ E)
    (hminimax :
      (⨅ w : Q, ⨆ v : Q, ((B v (w - v) : ℝ) : EReal)) =
        (⨆ v : Q, ⨅ w : Q, ((B v (w - v) : ℝ) : EReal))) :
    (⨅ w : Q, ⨆ v : Q, ((B v (w - v) : ℝ) : EReal)) =
      -⨅ v : Q, ⨆ w : Q, ((B v (v - w) : ℝ) : EReal) := by
  exact hminimax.trans (dualFormSmoothingMaximinValue_eq_neg_reverseMinimaxValue Q B)

end
