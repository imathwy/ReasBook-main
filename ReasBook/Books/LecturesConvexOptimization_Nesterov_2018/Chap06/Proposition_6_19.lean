import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
