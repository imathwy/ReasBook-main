import Mathlib
import BauschkeLean.Chap15.Definition_15_10
import BauschkeLean.Chap15.Proposition_15_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: Proposition 15.9 (2) is already the indexed-infimum inequality for the canonical
-- primal and dual objectives. Rewrite those indexed infima as `primalOptimalValue f g` and
-- `dualOptimalValue f g` using the owner API from Definition 15.10.
/-- Proposition 15 12 (1): the primal optimal value `μ` is at least the negative of the dual
optimal value `μ*`. -/
theorem primalOptimalValue_ge_neg_dualOptimalValue
    (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g ≥ -dualOptimalValue f g := by
  simpa [primalOptimalValue_eq_iInf_primalObjective,
    dualOptimalValue_eq_iInf_fenchelDualObjective] using
    iInf_primalObjective_ge_neg_iInf_dualObjective f g

/-- Helper for Proposition 15 12: in the nonexceptional branch, the primal optimal value cannot be
`⊥` when the dual optimal value is `⊤`. -/
lemma primal_ne_bot_of_not_exceptional_of_dual_eq_top
    (f g : H → Set.Ioi (⊥ : EReal))
    (hExceptional :
      ¬ (primalOptimalValue f g = -dualOptimalValue f g ∧
        (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤)))
    (hDualTop : dualOptimalValue f g = ⊤) :
    primalOptimalValue f g ≠ ⊥ := by
  -- If the primal value were `⊥`, the exceptional branch would be active as well.
  intro hPrimalBot
  apply hExceptional
  constructor
  · simp [hDualTop, hPrimalBot]
  · exact Or.inl hPrimalBot

/-- Helper for Proposition 15 12: in the nonexceptional branch, the dual optimal value cannot be
`⊥` unless it is already `⊤`. -/
lemma dual_ne_bot_of_not_exceptional_of_dual_ne_top
    (f g : H → Set.Ioi (⊥ : EReal))
    (hExceptional :
      ¬ (primalOptimalValue f g = -dualOptimalValue f g ∧
        (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤)))
    (_hDualTop : dualOptimalValue f g ≠ ⊤) :
    dualOptimalValue f g ≠ ⊥ := by
  -- Weak duality forces the primal value to be `⊤` if the dual value were `⊥`.
  intro hDualBot
  have hPrimalTop : primalOptimalValue f g = ⊤ := by
    apply top_unique
    simpa [hDualBot] using primalOptimalValue_ge_neg_dualOptimalValue f g
  -- That would put us back in the exceptional branch, contradicting the hypothesis.
  apply hExceptional
  constructor
  · simp [hDualBot, hPrimalTop]
  · exact Or.inr hPrimalTop

/-- Helper for Proposition 15 12: outside the exceptional branch, the primal and dual optimal
values have nonnegative sum. -/
lemma primal_add_dual_nonnegative_of_not_exceptional
    (f g : H → Set.Ioi (⊥ : EReal))
    (hExceptional :
      ¬ (primalOptimalValue f g = -dualOptimalValue f g ∧
        (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤))) :
    0 ≤ primalOptimalValue f g + dualOptimalValue f g := by
  -- Split on whether the dual optimal value is `⊤`, since the `EReal` API branches there.
  by_cases hDualTop : dualOptimalValue f g = ⊤
  · have hPrimalNeBot :=
      primal_ne_bot_of_not_exceptional_of_dual_eq_top f g hExceptional hDualTop
    simp [hDualTop, EReal.add_top_of_ne_bot hPrimalNeBot]
  · have hDualNeBot :=
      dual_ne_bot_of_not_exceptional_of_dual_ne_top f g hExceptional hDualTop
    have hSubNonneg : 0 ≤ primalOptimalValue f g - (-dualOptimalValue f g) := by
      -- Weak duality becomes a subtraction inequality once the infinite edge cases are excluded.
      exact (EReal.sub_nonneg
        (x := primalOptimalValue f g) (y := -dualOptimalValue f g)
        (Or.inr (by simpa using hDualNeBot))
        (Or.inr (by simpa using hDualTop))).2
        (primalOptimalValue_ge_neg_dualOptimalValue f g)
    simpa [sub_eq_add_neg, neg_neg] using hSubNonneg

/-- Helper for Proposition 15 12: away from the exceptional branch, the equality `μ = -μ*`
is equivalent to the vanishing of the sum `μ + μ*`. -/
lemma primal_eq_neg_dual_iff_sum_eq_zero_of_not_exceptional
    (f g : H → Set.Ioi (⊥ : EReal))
    (hExceptional :
      ¬ (primalOptimalValue f g = -dualOptimalValue f g ∧
        (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤))) :
    primalOptimalValue f g = -dualOptimalValue f g ↔
      primalOptimalValue f g + dualOptimalValue f g = 0 := by
  constructor
  · intro hEq
    have hPrimalNeBot : primalOptimalValue f g ≠ ⊥ := by
      -- The exceptional branch is exactly the equality case at `-∞`.
      intro hPrimalBot
      exact hExceptional ⟨hEq, Or.inl hPrimalBot⟩
    have hPrimalNeTop : primalOptimalValue f g ≠ ⊤ := by
      -- The exceptional branch is also the equality case at `+∞`.
      intro hPrimalTop
      exact hExceptional ⟨hEq, Or.inr hPrimalTop⟩
    have hSub : primalOptimalValue f g - (-dualOptimalValue f g) = 0 := by
      -- Rewriting the right-hand side with `hEq` reduces the claim to `μ - μ = 0`.
      rw [← hEq]
      exact EReal.sub_self hPrimalNeTop hPrimalNeBot
    simpa [sub_eq_add_neg, neg_neg] using hSub
  · intro hGap
    have hLe : primalOptimalValue f g ≤ -dualOptimalValue f g := by
      -- A vanishing sum gives the reverse inequality via `EReal.sub_nonpos`.
      exact (EReal.sub_nonpos).1 <| by
        simpa [sub_eq_add_neg, neg_neg] using hGap.le
    exact le_antisymm hLe (primalOptimalValue_ge_neg_dualOptimalValue f g)

-- Proof sketch: unfold `dualityGap`; in the exceptional branch the gap is `0`, and otherwise it is
-- `primalOptimalValue f g + dualOptimalValue f g`, which is nonnegative by clause (1).
/-- Proposition 15.12 (2): the duality gap `Δ(f, g)` lies in `[0, +∞]`, equivalently it is
nonnegative. -/
theorem dualityGap_nonnegative
    (f g : H → Set.Ioi (⊥ : EReal)) :
    0 ≤ dualityGap f g := by
  by_cases hExceptional : primalOptimalValue f g = -dualOptimalValue f g ∧
      (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤)
  · -- In the exceptional branch the gap is definitionally zero.
    rw [dualityGap_def, if_pos hExceptional]
  · -- Outside the exceptional branch the gap is the sum handled by the helper lemma.
    rw [dualityGap_def, if_neg hExceptional]
    exact
      primal_add_dual_nonnegative_of_not_exceptional f g hExceptional

-- Proof sketch: unfold `dualityGap` and split on the exceptional case from Definition 15.10; in
-- the non-exceptional branch, clause (1) shows that `primalOptimalValue f g + dualOptimalValue f g`
-- vanishes exactly when `primalOptimalValue f g = -dualOptimalValue f g`.
/-- Proposition 15.12 (3): the primal-dual equality `μ = -μ*` holds exactly when the duality gap
vanishes. -/
theorem primalOptimalValue_eq_neg_dualOptimalValue_iff_dualityGap_eq_zero
    (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g = -dualOptimalValue f g ↔ dualityGap f g = 0 := by
  by_cases hExceptional : primalOptimalValue f g = -dualOptimalValue f g ∧
      (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤)
  · -- In the exceptional branch the gap is definitionally zero and the equality is already known.
    constructor
    · intro _hEq
      rw [dualityGap_def, if_pos hExceptional]
    · intro _hGap
      exact hExceptional.1
  · -- Outside the exceptional branch the gap is exactly the sum `μ + μ*`.
    rw [dualityGap_def, if_neg hExceptional]
    exact
      primal_eq_neg_dual_iff_sum_eq_zero_of_not_exceptional f g hExceptional

end FenchelDuality

end ERealFunction
