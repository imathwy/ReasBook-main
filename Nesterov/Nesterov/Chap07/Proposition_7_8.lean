import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 7.8 lies in the scalar concavity / maximizer layer of the centrally symmetric
rounding argument.

Sampled owner-style declarations:
- mathlib `StrictConcaveOn`, the canonical owner for strict concavity on an interval;
- mathlib `IsMaxOn`, the canonical owner for interval maximizers;
- `rankOneUpdatePotential` in `Lemma_7_4`, the matrix-level specialization whose scalar part is the
  same logarithmic objective with `σ = (1 / n) ‖g‖_{G,*}² - 1`;
- `oneSidedRoundingPotential` in `Lemma_7_5`, a nearby chapter scalar maximizer statement with the
  same `IsMaxOn` owner discipline.

Best owner abstraction:
- source-facing: the scalar objective `V(α)` and its distinguished critical point `α*`;
- core/canonical: mathlib's `StrictConcaveOn` and `IsMaxOn`;
- bridge/view: later matrix-level specializations obtained by substituting a concrete `σ`.

Primitive data:
- the dimension parameter `n`;
- the scalar parameter `σ`;
- the interval variable `α`.

Derived API:
- strict concavity on `Set.Ico 0 1`;
- membership of the explicit critical point in that interval;
- the first-order characterization, maximizer characterization, and closed-form value at `α*`.

The scalar coefficient `n (1 + σ) - 1` is not kept as a separate public owner: it is derived data
inside the objective and critical-point formulas. -/

/-- The scalar objective `V(α)` on `[0, 1)` used in the centrally symmetric rounding estimate. -/
def centralSymmetryRoundingObjective (n : ℕ) (σ : ℝ) (α : ℝ) : ℝ :=
  Real.log (1 + α * ((n : ℝ) * (1 + σ) - 1)) +
    ((n : ℝ) - 1) * Real.log (1 - α)

/-- The explicit critical point `α* = σ / (n (1 + σ) - 1)` of the scalar objective. -/
def centralSymmetryRoundingAlphaStar (n : ℕ) (σ : ℝ) : ℝ :=
  σ / ((n : ℝ) * (1 + σ) - 1)

-- Proof sketch: write `V` as the sum of two logarithmic terms composed with affine maps taking
-- `[0, 1)` into `(0, ∞)`. The hypothesis `-1 ≤ σ` keeps the first logarithmic argument positive on
-- `Set.Ico 0 1`, `1 ≤ n` keeps the second logarithmic coefficient nonnegative, and the extra
-- nonconstancy hypothesis rules out the degenerate constant case. Strict concavity then follows
-- from strict concavity of `Real.log` on `Set.Ioi 0` together with stability under affine
-- reparametrization and addition.
/-- The objective `V` is strictly concave on `[0, 1)` once both logarithmic terms are well defined
and at least one of them is genuinely nonconstant. -/
theorem centralSymmetryRoundingObjective_strictConcaveOn
    {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : -1 ≤ σ)
    (hstrict : ((n : ℝ) * (1 + σ) - 1 ≠ 0) ∨ 1 < n) :
    StrictConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (centralSymmetryRoundingObjective n σ) := sorry

-- Proof sketch: use `2 ≤ n` and `0 ≤ σ` to show
-- `0 ≤ σ / (n (1 + σ) - 1) < 1`, equivalently that the explicit critical point lies in
-- `Set.Ico 0 1`.
/-- The explicit critical point `α*` lies in the interval `[0, 1)`. -/
theorem centralSymmetryRoundingAlphaStar_mem_Ico
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) :
    centralSymmetryRoundingAlphaStar n σ ∈ Set.Ico (0 : ℝ) 1 := sorry

-- Proof sketch: compute `V'(α)` on the genuine logarithmic domain, namely points of `[0, 1)` for
-- which the first logarithmic argument `1 + α (n (1 + σ) - 1)` is positive. On that domain, the
-- critical-point equation reduces to a linear equation in `α`, whose unique solution is
-- `α = σ / (n (1 + σ) - 1)`. The coefficient hypothesis keeps the displayed closed form defined.
/-- On the genuine logarithmic domain inside `[0, 1)`, the first-order condition for `V` is
equivalent to `α = α*`. -/
theorem centralSymmetryRoundingObjective_firstOrderCondition_iff
    {n : ℕ} {σ : ℝ} (hn : 1 ≤ n)
    (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hlog : 0 < 1 + α * ((n : ℝ) * (1 + σ) - 1)) :
    ((n : ℝ) - 1) / (1 - α) =
        (((n : ℝ) * (1 + σ) - 1) / (1 + α * ((n : ℝ) * (1 + σ) - 1))) ↔
      α = centralSymmetryRoundingAlphaStar n σ := sorry

-- Proof sketch: strict concavity gives uniqueness of a feasible maximizer on the convex set
-- `[0, 1)`. The first-order characterization identifies the only critical point with
-- `σ / (n (1 + σ) - 1)`, and the separate membership theorem shows that this point is feasible.
/-- Proposition 7.8: among feasible points `α ∈ [0, 1)`, the scalar objective `V` is maximized
exactly at `α* = σ / (n (1 + σ) - 1)`. -/
theorem centralSymmetryRoundingObjective_isMaxOn_iff
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    IsMaxOn (centralSymmetryRoundingObjective n σ) (Set.Ico (0 : ℝ) 1) α ↔
      α = centralSymmetryRoundingAlphaStar n σ := sorry

-- Proof sketch: substitute `α* = σ / (n (1 + σ) - 1)` into the two logarithmic factors,
-- simplify `1 + α* (n (1 + σ) - 1) = 1 + σ` and
-- `1 - α* = ((n - 1) (1 + σ)) / (n (1 + σ) - 1)`, then evaluate `V(α*)`. Only the
-- nondegeneracy of `n (1 + σ) - 1` is needed for the substitution.
/-- The scalar objective evaluated at `α*` has the closed form stated in the proposition. -/
theorem centralSymmetryRoundingObjective_alphaStar_value
    {n : ℕ} {σ : ℝ} (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) :
    centralSymmetryRoundingObjective n σ (centralSymmetryRoundingAlphaStar n σ) =
      Real.log (1 + σ) +
        ((n : ℝ) - 1) *
          Real.log
            (((n : ℝ) - 1) * (1 + σ) / ((n : ℝ) * (1 + σ) - 1)) := sorry
