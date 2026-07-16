import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_34
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Lemma_6_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 6.2.1 lies in the chapter's excessive-gap stopping-criterion domain.

Sampled owner-style declarations:
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the source-facing owner for the
  chapter's excessive-gap certificate;
- `satisfiesExcessiveGapCondition_preserved_under_update` in `Chap06/Theorem_6_4`, the Chapter 6
  update theorem stated directly in terms of that same source-facing owner;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the chapter bridge from an
  excessive-gap certificate to a raw duality-gap budget bound.

Best owner abstraction:
- the chapter's excessive-gap certificate, not a generic scalar gap sequence.

Primitive data:
- the source-facing excessive-gap certificate `satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁`;
- the local one-sided smoothing bounds `f xBar - μ₂ * D₂ ≤ fμ₂ xBar` and
  `φμ₁ uBar ≤ φ uBar + μ₁ * D₁`;
- the stopping inequality `μ₁ D₁ + μ₂ D₂ ≤ ε`.

Derived API:
- the stopping conclusion `f(xBar) - φ(uBar) ≤ ε`.

Source/core/bridge triage:
- source-facing: the chapter's excessive-gap certificate at the current primal-dual pair together
  with the stopping test on the smoothing budget;
- core/canonical: the chapter owner `satisfiesExcessiveGapCondition`;
- bridge/view: the raw duality-gap estimate obtained by combining the certificate with the
  smoothing bounds.
-/

universe u v

section

variable {X : Type u} {U : Type v}

-- Proof sketch: the excessive-gap certificate is exactly `fμ₂ xBar ≤ φμ₁ uBar`. Combine this
-- with the local smoothing bounds at `xBar` and `uBar` to obtain
-- `f xBar - φ uBar ≤ μ₁ D₁ + μ₂ D₂`, then use the stopping inequality
-- `μ₁ D₁ + μ₂ D₂ ≤ ε`.
/-- Text 6.2.1-Fixed-Horizon Drawback and Excessive-Gap Motivation: once a feasible pair
`(xBar, uBar)` satisfies the chapter's excessive-gap certificate and the current smoothing budget
obeys `μ₁ D₁ + μ₂ D₂ ≤ ε`, the raw duality gap is already `ε`-small. This source-facing stopping
criterion uses only the two smoothing inequalities at the current pair `(xBar, uBar)`, not global
smoothing bounds on all of `Q₁` and `Q₂`, so one can stop as soon as the current certificate
budget falls below `ε` instead of fixing a horizon in advance. -/
theorem raw_duality_gap_le_epsilon_of_satisfiesExcessiveGapCondition
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ φμ₁ : U → ℝ}
    {xBar : Q₁} {uBar : Q₂}
    {D₁ D₂ μ₁ μ₂ ε : ℝ}
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφμ₁_upper : φμ₁ uBar ≤ φ uBar + μ₁ * D₁)
    (hexcessive_gap : satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ xBar uBar)
    (hbudget : μ₁ * D₁ + μ₂ * D₂ ≤ ε) :
    f xBar - φ uBar ≤ ε := sorry

end
