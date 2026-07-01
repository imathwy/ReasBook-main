import Nesterov.Chap03.Lemma_3_1_12
import Nesterov.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 7.18 lies in the Chapter 7 strict-positivity / closed-convex weighted-sum
subdifferential domain.

Mandatory domain-style sampling before refinement:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in `Definition_7_81`, the source-facing
  owner and its primitive projection lemma;
- `ClosedConvexFunction` in `Chap03/Definition_3_1_1_5`, the canonical closed-convex owner for
  `WithTop ℝ`-valued functions, used on the chapter’s standard pointwise lift
  `fun x ↦ (f x : WithTop ℝ)`;
- `ClosedConvexFunction.nonneg_weighted_add` and
  `subdifferential_nonneg_weighted_add_eq_of_pos` in `Chap03/Lemma_3_1_12`, the chapter's
  closed-convex weighted-sum API written directly on the canonical pointwise combination
  `α₁ • f₁ + α₂ • f₂`;
- `ClosedConvexOn.nonneg_smul` in `Chap03/Theorem_3_1_5`, the owner pattern behind the zero-weight
  and one-summand branches.

Best owner abstraction:
- source-facing: `StrictlyPositiveOn Q f`;
- core/canonical: the closed-convex owner
  `ClosedConvexFunction (fun x ↦ (f x : WithTop ℝ))` together with the canonical pointwise
  weighted sum `α₁ • f₁ + α₂ • f₂`;
- bridge/view: the source-facing closure theorems in this file, which keep the conclusion on
  `StrictlyPositiveOn` while routing the genuinely two-summand case through the Chapter 3
  closed-convex sum rule.

Primitive data:
- the set `Q`;
- the summands `f₁`, `f₂`;
- the closed-convex owner witnesses `hcc₁`, `hcc₂` for the lifted summands;
- the weights `α₁`, `α₂`;
- the owner witnesses `hf₁`, `hf₂`.

Derived API:
- `StrictlyPositiveOn.nonneg_smul`;
- `StrictlyPositiveOn.nonnegative_linear_combination`.
-/

-- Proof sketch: if `α = 0`, the target is the zero function, whose only whole-space subgradient
-- is `0`; if `α > 0`, divide the defining subgradient inequality for `α • f` by `α` to recover a
-- subgradient of `f`, then rescale the strict-positivity inequality.
theorem StrictlyPositiveOn.nonneg_smul
    {Q : Set E} {f : E → ℝ} (hf : StrictlyPositiveOn Q f)
    {α : ℝ} (hα : 0 ≤ α) :
    StrictlyPositiveOn Q (α • f) := sorry

-- Proof sketch: split the zero-weight branches and dispatch them with
-- `StrictlyPositiveOn.nonneg_smul`. In the genuinely two-summand branch `α₁, α₂ > 0`, use
-- `subdifferential_nonneg_weighted_add_eq_of_pos` for the canonical `WithTop` lifts to write a
-- subgradient of `α₁ • f₁ + α₂ • f₂` as `α₁ • g₁ + α₂ • g₂`, then combine the defining
-- inequalities from `hf₁` and `hf₂`.
/-- Lemma 7.18: if the canonical `WithTop ℝ` lifts of `f₁` and `f₂` are closed convex and each
is strictly positive on `Q`, then every nonnegative linear combination `α₁ • f₁ + α₂ • f₂` is
strictly positive on `Q`. -/
theorem StrictlyPositiveOn.nonnegative_linear_combination
    {Q : Set E} {f₁ f₂ : E → ℝ}
    (hf₁ : StrictlyPositiveOn Q f₁) (hf₂ : StrictlyPositiveOn Q f₂)
    (hcc₁ : ClosedConvexFunction (fun x ↦ (f₁ x : WithTop ℝ)))
    (hcc₂ : ClosedConvexFunction (fun x ↦ (f₂ x : WithTop ℝ)))
    {α₁ α₂ : ℝ} (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    StrictlyPositiveOn Q (α₁ • f₁ + α₂ • f₂) := sorry
