import Mathlib
import Nesterov.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u}

/- Proposition 7.23 lies in Chapter 7's relative-accuracy / constrained-optimal-value transfer
domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  real-valued objective on a feasible set;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  constrained optimal-value owner;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_7`,
  the defining bridge to the infimum of the feasible value image in `EReal`;
- `inducedObjectiveInf` and `inducedRadiusInf` in `Chap07/Proposition_7_22`, the nearby chapter
  pattern using the same owner together with a `.toReal` bridge back to textbook real inequalities.

Best owner abstraction:
- source-facing: transfer of a relative-accuracy bound from the smoothed objective `f_p` to the
  original objective `φ` on the same feasible set;
- core/canonical: `(.mk Q f : SetConstrainedMinimizationProblem X).optimalValue`;
- bridge/view: the pointwise sandwich between `φ` and `f_p`.

Primitive data:
- a feasible set `Q : Set X`;
- the two objectives `φ` and `f_p`;
- a positive smoothing order `p : ℕ+`;
- the candidate point `yBar ∈ Q`;
- the feasible-set nonnegativity of `φ`;
- the pointwise lower and upper comparisons between `φ` and `f_p` on `Q`.

Derived API:
- the constrained optimization owners `(.mk Q φ : SetConstrainedMinimizationProblem X)` and
  `(.mk Q f_p : SetConstrainedMinimizationProblem X)`;
- the textbook real surfaces `((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal`
  and `((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal`;
- the relative-accuracy inequalities stated using those owners.

This refinement removes the duplicate local real-valued optimal-value wheel from the public
surface. The constrained minima of `φ` and `f_p` are canonically owned by
`SetConstrainedMinimizationProblem.optimalValue`; the proposition uses only the minimal `.toReal`
bridge needed to recover the textbook real inequalities from those owner values.
-/

-- Proof sketch: combine the feasible-set nonnegativity of `φ` with the pointwise bounds to get
-- `φ yBar ≤ sqrt (2 * f_p yBar)` and
-- `sqrt (2 * ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal) ≤
--   r^(1 / (2p)) * ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal`,
-- then use
-- `f_p yBar ≤ (1 + δ) *
--   ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal`.
-- The condition
-- `((1 + δ) / δ) * log r ≤ p` implies `r^(1 / (2p)) ≤ sqrt (1 + δ)` when `r > 1`; for `r ≤ 1`,
-- the factor `r^(1 / (2p))` only decreases the right-hand side, so the same conclusion is easier.
-- Thus
-- `φ yBar / ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal ≤
--   r^(1 / (2p)) * sqrt (1 + δ) ≤ 1 + δ`.
/-- Proposition 7.23: if `p` is a positive smoothing order, `f_p` lies between
`(1 / 2) φ^2` and `(1 / 2) r^(1 / p) φ^2` on the feasible set `Q`, and `yBar ∈ Q` is
`(1 + δ)`-optimal for `f_p`, then `yBar` is also `(1 + δ)`-optimal for `φ`, with both optimal
values read from the canonical Chapter 1 constrained optimization owner and projected back to `ℝ`
via `.toReal`. -/
theorem relative_accuracy_transfer_from_fp_to_phi
    (Q : Set X) (φ f_p : X → ℝ) (δ r : ℝ) (p : ℕ+) (yBar : X)
    (hyBar_mem : yBar ∈ Q)
    (hδ : 0 < δ)
    (hφ_nonneg : ∀ y ∈ Q, 0 ≤ φ y)
    (h_lower : ∀ y ∈ Q, (1 / 2 : ℝ) * φ y ^ (2 : ℕ) ≤ f_p y)
    (h_upper : ∀ y ∈ Q,
      f_p y ≤ (1 / 2 : ℝ) * Real.rpow r (1 / (p : ℝ)) * φ y ^ (2 : ℕ))
    (hp : ((1 + δ) / δ) * Real.log r ≤ (p : ℝ))
    (hyBar :
      f_p yBar ≤
        (1 + δ) * ((.mk Q f_p : SetConstrainedMinimizationProblem X).optimalValue).toReal) :
    φ yBar ≤
      (1 + δ) * ((.mk Q φ : SetConstrainedMinimizationProblem X).optimalValue).toReal := sorry

end
