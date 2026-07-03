import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_3_3_1 (from Chap03) -/
noncomputable section

universe u

/- Lemma 3.3.1 lies in the chapter's level-method scalar-history domain.

Best owner abstraction:
* the primitive scalar history `(\hat f_k^*, f_k^*)` is `LevelMethodHistory`

Primitive data:
* `approximateOptimalValue`
* `optimalValue`

Derived API:
* `gap`
* `levelValue`
* `valueInterval`
* `shouldStop`

This file keeps only the two scalar sequences as primitive data. The gap, the level value, and
the stopping test `δ_k ≤ ε` are all derived from that owner history rather than repeated later as
parallel sequence-level wrappers.
-/

/-- The scalar data from a level-method model needed for the monotonicity and gap estimates:
the approximate optimal values `\hat f_k^*` and the record values `f_k^*`. -/
structure LevelMethodHistory where
  /-- The approximate optimal values `\hat f_k^*`. -/
  approximateOptimalValue : ℕ → ℝ
  /-- The record values `f_k^* = min_{0 ≤ i ≤ k} f(x_i)`. -/
  optimalValue : ℕ → ℝ

namespace LevelMethodNotation

scoped notation:max "fhat(" history:arg ", " k:arg ")" =>
  LevelMethodHistory.approximateOptimalValue history k

scoped notation:max "fstar(" history:arg ", " k:arg ")" =>
  LevelMethodHistory.optimalValue history k

end LevelMethodNotation

namespace LevelMethodHistory

/-- The model gap `δ_k = f_k^* - \hat f_k^*` at iteration `k`. -/
def gap (history : LevelMethodHistory) (k : ℕ) : ℝ :=
  history.optimalValue k - history.approximateOptimalValue k

/-- The model gap is the difference between the exact and approximate optimal values. -/
-- Proof sketch: unfold `LevelMethodHistory.gap`.
theorem gap_eq_sub (history : LevelMethodHistory) (k : ℕ) :
    history.gap k = history.optimalValue k - history.approximateOptimalValue k :=
  rfl

/-- The level value `ℓ_k(α) = (1 - α) \hat f_k^* + α f_k^*`. -/
def levelValue (history : LevelMethodHistory) (α : ℝ) (k : ℕ) : ℝ :=
  (1 - α) * history.approximateOptimalValue k + α * history.optimalValue k

/-- The level value can be rewritten as `f_k^* - (1 - α) δ_k`. -/
-- Proof sketch: unfold `LevelMethodHistory.levelValue` and `LevelMethodHistory.gap`, then
-- expand the products and collect terms.
theorem levelValue_eq_optimal_sub_one_sub_alpha_mul_gap
    (history : LevelMethodHistory) (α : ℝ) (k : ℕ) :
    history.levelValue α k = history.optimalValue k - (1 - α) * history.gap k := by
  rw [levelValue, gap_eq_sub]
  ring

/-- The interval `Δ_k = [\hat f_k^*, f_k^*]` attached to a level-method history. -/
def valueInterval (history : LevelMethodHistory) (k : ℕ) : Set ℝ :=
  Set.Icc (history.approximateOptimalValue k) (history.optimalValue k)

/-- Membership in `history.valueInterval k` is the pair of inequalities
`\hat f_k^* ≤ t ≤ f_k^*`. -/
theorem mem_valueInterval_iff
    (history : LevelMethodHistory) (k : ℕ) (t : ℝ) :
    t ∈ history.valueInterval k ↔
      history.approximateOptimalValue k ≤ t ∧ t ≤ history.optimalValue k :=
  Iff.rfl

end LevelMethodHistory

namespace LevelMethodNotation

scoped notation:max "δ[" history:arg "](" k:arg ")" =>
  LevelMethodHistory.gap history k

scoped notation:max "ℓ[" history:arg "](" α:arg ", " k:arg ")" =>
  LevelMethodHistory.levelValue history α k

scoped notation:max "Δ[" history:arg "](" k:arg ")" =>
  LevelMethodHistory.valueInterval history k

end LevelMethodNotation

open scoped LevelMethodNotation

namespace LevelMethodHistory

/-- The textbook stopping test `δ_k ≤ ε` for a scalar level-method history. -/
def shouldStop (history : LevelMethodHistory) (ε : ℝ) (k : ℕ) : Prop :=
  history.gap k ≤ ε

/-- The stopping test is exactly the inequality `δ_k ≤ ε`. -/
-- Proof sketch: unfold `LevelMethodHistory.shouldStop`.
theorem shouldStop_iff (history : LevelMethodHistory) (ε : ℝ) (k : ℕ) :
    history.shouldStop ε k ↔ history.gap k ≤ ε :=
  Iff.rfl

/-- If `\hat f_k^*` is a lower bound for the optimum value `f^*`, then the stopping test
`δ_k ≤ ε` implies `f_k^* - f^* ≤ ε`. -/
-- Proof sketch: combine the single-index lower-bound estimate
-- `history.approximateOptimalValue k ≤ fStar` with the identity
-- `δ_k = history.optimalValue k - history.approximateOptimalValue k`, then use the stopping
-- inequality `δ_k ≤ ε`.
theorem optimalValue_sub_fStar_le_epsilon_of_shouldStop
    (history : LevelMethodHistory) {fStar ε : ℝ} (k : ℕ)
    (hvalidLower : history.approximateOptimalValue k ≤ fStar)
    (hstop : history.shouldStop ε k) :
    history.optimalValue k - fStar ≤ ε := by
  rw [shouldStop_iff, gap_eq_sub] at hstop
  linarith

/-- Bridge/view: if on the interval `[k, p]` the record values are bounded below by the terminal
record value, the gaps are bounded above by the initial gap, and `δ_p ≥ (1 - α) δ_k`, then every
intermediate level value `ℓ_i(α)` is at least `\hat f_p^*`. -/
theorem levelValue_ge_approximateOptimalValue_of_intervalMonotonicity
    (history : LevelMethodHistory) {α : ℝ} {k p : ℕ}
    (hα : α ≤ 1)
    (hoptimal_mono :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → fstar(history, p) ≤ fstar(history, i))
    (hgap_mono :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → δ[history](i) ≤ δ[history](k))
    (hgap_large : δ[history](p) ≥ (1 - α) * δ[history](k)) :
    ∀ {i : ℕ}, k ≤ i → i ≤ p → ℓ[history](α, i) ≥ fhat(history, p) := by
  intro i hki hip
  have hOneSubAlpha_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα
  have hoptimal : history.optimalValue p ≤ history.optimalValue i := hoptimal_mono hki hip
  have hgap_i : history.gap i ≤ history.gap k := hgap_mono hki hip
  have hscaled_gap_i : (1 - α) * history.gap i ≤ (1 - α) * history.gap k :=
    mul_le_mul_of_nonneg_left hgap_i hOneSubAlpha_nonneg
  have hscaled_gap_p : (1 - α) * history.gap i ≤ history.gap p :=
    hscaled_gap_i.trans hgap_large
  rw [history.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap α i]
  linarith [history.gap_eq_sub p]

/-- Lemma 3.3.1: if the record values satisfy `f_{j+1}^* ≤ f_j^*`, the model gaps satisfy
`δ_{j+1} ≤ δ_j`, and the gap still obeys `δ_p ≥ (1 - α) δ_k`, then every
intermediate level value `ℓ_i(α)` with `k ≤ i ≤ p` is at least `\hat f_p^*`. -/
-- Proof sketch: since `α ≤ 1`, the factor `1 - α` is nonnegative. Use the stepwise monotonicity
-- of the gaps to show `δ_i ≤ δ_k` for `k ≤ i ≤ p`, hence
-- `(1 - α) * δ_i ≤ (1 - α) * δ_k ≤ δ_p`. Rewrite `ℓ_i(α)` as
-- `f_i^* - (1 - α) * δ_i`, compare `f_i^*` with `f_p^*` using the monotonicity of the record
-- values, and finish by expanding `δ_p = f_p^* - \hat f_p^*`.
theorem levelValue_ge_approximateOptimalValue_of_gap_large_enough
    (history : LevelMethodHistory) {α : ℝ} {k p : ℕ}
    (hα : α ≤ 1)
    (hoptimal_succ : ∀ j : ℕ, history.optimalValue (j + 1) ≤ history.optimalValue j)
    (hgap_succ : ∀ j : ℕ, history.gap (j + 1) ≤ history.gap j)
    (hgap_large : δ[history](p) ≥ (1 - α) * δ[history](k)) :
    ∀ {i : ℕ}, k ≤ i → i ≤ p → ℓ[history](α, i) ≥ fhat(history, p) := by
  have hoptimal_antitone : Antitone history.optimalValue :=
    antitone_nat_of_succ_le hoptimal_succ
  have hgap_antitone : Antitone history.gap :=
    antitone_nat_of_succ_le hgap_succ
  intro i hki hip
  exact
    history.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity hα
    (fun {_i} _hki hip' ↦ hoptimal_antitone hip')
    (fun {_i} hki' _hip ↦ hgap_antitone hki')
    hgap_large
    hki
    hip

end LevelMethodHistory

/-! ### Theorem_3_3_1 (from Chap03) -/
noncomputable section

open scoped LevelMethodNotation

/- Theorem 3.3.1 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner bundle for `(\hat f_k^*, f_k^*)`
* `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
* `LevelMethodHistory.shouldStop` in `Lemma_3_3_1`, the canonical stopping predicate `δ_k ≤ ε`
* `LevelMethodHistory.optimalValue_sub_fStar_le_epsilon_of_shouldStop` in `Lemma_3_3_1`, the
  owner consequence of the stopping test

Best owner abstraction:
* `LevelMethodHistory`

Primitive data:
* `history.approximateOptimalValue`
* `history.optimalValue`

Derived API:
* `history.gap`
* `history.shouldStop`

This file therefore keeps only the iteration-cap statement and reuses the scalar-history owner API
instead of repeating separate global definitions for the gap and stopping rule.
-/

/-- The textbook worst-case iteration cap
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` for the Level Method. -/
def levelMethodIterationCap (M_f D ε α : ℝ) : ℕ :=
  Nat.floor
      (M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
        (ε ^ (2 : ℕ) * levelParameterObjective α)) +
    1

/-- Helper for Theorem 3.3.1: a positive terminal gap determines the minimal start of the last
block whose terminal gap is still at least `(1 - α)` times the block-start gap. -/
private theorem minimal_block_start_of_gap_pos
    (history : LevelMethodHistory) {α : ℝ} {p : ℕ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hgap_pos : 0 < δ[history](p)) :
    ∃ k ≤ p,
      δ[history](p) ≥ (1 - α) * δ[history](k) ∧
      ∀ ⦃i : ℕ⦄, i < k → δ[history](p) < (1 - α) * δ[history](i) := by
  rcases hα with ⟨hα0, hα1⟩
  let P : ℕ → Prop := fun k ↦
    k ≤ p ∧ δ[history](p) ≥ (1 - α) * δ[history](k)
  have hP : ∃ k, P k := by
    refine ⟨p, le_rfl, ?_⟩
    -- The terminal index itself is admissible because `α * δ_p > 0`.
    have hscaled_lt : (1 - α) * δ[history](p) < δ[history](p) := by
      nlinarith [mul_pos hα0 hgap_pos]
    exact hscaled_lt.le
  refine ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2, ?_⟩
  intro i hik
  have hnot : ¬ P i := Nat.find_min hP hik
  have hnot_large : ¬ δ[history](p) ≥ (1 - α) * δ[history](i) := by
    intro hlarge
    have hip : i ≤ p := (Nat.le_of_lt hik).trans (Nat.find_spec hP).1
    exact hnot ⟨hip, hlarge⟩
  exact lt_of_not_ge hnot_large

/-- Helper for Theorem 3.3.1: the scaled-threshold prefix contribution and the terminal-block
contribution add up to the full iteration-cap denominator. -/
private theorem scaled_tolerance_prefix_denominator_eq
    {α τ C : ℝ}
    (hτ : 0 < τ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    C / (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) +
      C / ((1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ)) =
      C / (τ ^ (2 : ℕ) * levelParameterObjective α) := by
  rcases hα with ⟨hα0, hα1⟩
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ
  have hOneSub_ne : 1 - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα1)
  have hTwoSub_ne : 2 - α ≠ 0 := sub_ne_zero.mpr (by linarith)
  -- Clear the denominators once and reduce the claim to a polynomial identity.
  have hlevel_pos : 0 < levelParameterObjective α := levelParameterObjective_pos ⟨hα0, hα1⟩
  unfold levelParameterObjective
  field_simp [hτ_ne, hOneSub_ne, hTwoSub_ne, ne_of_gt hlevel_pos]
  ring

/-- Helper for Theorem 3.3.1: if every gap on a prefix stays above a threshold `τ`, then the
prefix length is controlled by the chapter's iteration-cap quotient. -/
private theorem prefix_length_le_div_of_forall_lt_gap
    (history : LevelMethodHistory) {M_f D α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    ∀ p : ℕ, ∀ τ : ℝ,
      0 < τ →
      (∀ i ≤ p, τ < δ[history](i)) →
      ((p + 1 : ℕ) : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          (τ ^ (2 : ℕ) * levelParameterObjective α) := by
  intro p
  refine Nat.strong_induction_on p ?_
  intro p ih τ hτ hgap_gt
  have hOneSub_pos : 0 < 1 - α := sub_pos.mpr hα.2
  have hnum_nonneg : 0 ≤ M_f ^ (2 : ℕ) * D ^ (2 : ℕ) := by
    positivity
  have hgap_p : τ < δ[history](p) := hgap_gt p le_rfl
  have hgap_p_pos : 0 < δ[history](p) := lt_trans hτ hgap_p
  -- Pick the minimal start of the last block ending at `p`.
  obtain ⟨k, hkp, hgap_large, hminimal⟩ :=
    minimal_block_start_of_gap_pos history hα hgap_p_pos
  have hlast_raw :
      ((p + 1 - k : ℕ) : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ)) :=
    hblock hkp hgap_large hgap_p_pos
  have hsq_le : τ ^ (2 : ℕ) ≤ δ[history](p) ^ (2 : ℕ) := by
    nlinarith
  have hden_le :
      (1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ) ≤
        (1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq_le (by positivity)
  have hden_pos : 0 < (1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ) := by
    positivity
  have hlast :
      ((p + 1 - k : ℕ) : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          ((1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ)) :=
    hlast_raw.trans <|
      div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  have hprefix :
      (k : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) := by
    by_cases hk : k = 0
    · -- No earlier prefix remains when the last block starts at zero.
      have hscaled_den_pos :
          0 <
            ((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α := by
        have hτ_scaled : 0 < τ / (1 - α) := div_pos hτ hOneSub_pos
        exact mul_pos (by positivity) (levelParameterObjective_pos hα)
      have hzero_bound :
          (0 : ℝ) ≤
            (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
              (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) :=
        div_nonneg hnum_nonneg hscaled_den_pos.le
      simpa [hk] using hzero_bound
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      have hτ_scaled : 0 < τ / (1 - α) := div_pos hτ hOneSub_pos
      have hscaled_gap_gt :
          ∀ i ≤ k - 1, τ / (1 - α) < δ[history](i) := by
        intro i hik
        have hik_lt : i < k := lt_of_le_of_lt hik (Nat.sub_one_lt hk)
        have hlt_scaled : τ < (1 - α) * δ[history](i) :=
          (hgap_gt p le_rfl).trans (hminimal hik_lt)
        -- Minimality of `k` forces the previous block-start gaps to grow by `(1 - α)⁻¹`.
        rw [div_lt_iff₀ hOneSub_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hlt_scaled
      have hprefix_raw :
          ((k - 1 + 1 : ℕ) : ℝ) ≤
            (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
              (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) :=
        ih (k - 1) (lt_of_lt_of_le (Nat.sub_one_lt hk) hkp) (τ / (1 - α)) hτ_scaled
          hscaled_gap_gt
      have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)
      simpa [hk_eq] using hprefix_raw
  have hdecomp_nat : k + (p + 1 - k) = p + 1 :=
    Nat.add_sub_of_le (hkp.trans (Nat.le_succ p))
  have hdecomp_real : (k : ℝ) + ((p + 1 - k : ℕ) : ℝ) = ((p + 1 : ℕ) : ℝ) := by
    exact_mod_cast hdecomp_nat
  -- Add the prefix estimate and the last-block estimate, then collapse the scalar identity.
  calc
    ((p + 1 : ℕ) : ℝ) = (k : ℝ) + ((p + 1 - k : ℕ) : ℝ) := by
      symm
      exact hdecomp_real
    _ ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) +
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ)) :=
      add_le_add hprefix hlast
    _ =
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          (τ ^ (2 : ℕ) * levelParameterObjective α) :=
      scaled_tolerance_prefix_denominator_eq hτ hα

/-- Theorem 3.3.1 (iteration-cap part): if each level-method block `[k, p]` that is still in the
positive-gap regime and satisfies `δ_p ≥ (1 - α) δ_k` obeys the interval bound from
Lemma `3.3.3`, then the Level Method reaches the canonical stopping predicate `δ_k ≤ ε` after at
most
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` iterations. -/
-- Proof sketch: argue by contradiction and assume `history.gap k > ε` for every
-- `k ≤ levelMethodIterationCap M_f D ε α`. Partition the indices into maximal consecutive blocks
-- on which the terminal gap stays at least `(1 - α)` times the initial gap. The block bound
-- `hblock` controls the length of each block, while the block-start gaps grow geometrically by
-- the factor `(1 - α)⁻¹`; summing the resulting geometric series yields the displayed iteration
-- cap.
theorem exists_stopping_index_le_levelMethodIterationCap
    (history : LevelMethodHistory) {M_f D ε α : ℝ}
    (hε : 0 < ε)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    ∃ k ≤ levelMethodIterationCap M_f D ε α,
      history.shouldStop ε k := by
  let R :=
    (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
      (ε ^ (2 : ℕ) * levelParameterObjective α)
  let p := Nat.floor R
  by_contra hnostop
  push Not at hnostop
  have hgap_gt :
      ∀ i ≤ p, ε < δ[history](i) := by
    intro i hip
    have hi_cap : i ≤ levelMethodIterationCap M_f D ε α := by
      -- The contradiction uses the whole floor-prefix `[0, p]`.
      dsimp [p, R]
      unfold levelMethodIterationCap
      exact hip.trans (Nat.le_succ _)
    have hi_not_stop : ¬ history.shouldStop ε i := hnostop i hi_cap
    rw [LevelMethodHistory.shouldStop_iff] at hi_not_stop
    exact lt_of_not_ge hi_not_stop
  have hprefix :
      ((p + 1 : ℕ) : ℝ) ≤ R := by
    dsimp [R]
    exact prefix_length_le_div_of_forall_lt_gap history hα hblock p ε hε hgap_gt
  have hprefix' : (p : ℝ) + 1 ≤ R := by
    simpa [Nat.cast_add] using hprefix
  have hfloor : R < (p : ℝ) + 1 := by
    simpa [p, Nat.cast_add] using Nat.lt_floor_add_one R
  -- The prefix bound contradicts the universal property of `Nat.floor`.
  linarith

/-- Theorem 3.3.1: if each level-method block `[k, p]` that is still in the positive-gap regime
and satisfies `δ_p ≥ (1 - α) δ_k` obeys the interval bound from Lemma `3.3.3`, then the Level
Method terminates after at most
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` iterations. Moreover, the stopping criterion
guarantees `f_k^* - f^* ≤ ε`. -/
-- Proof sketch: argue by contradiction and assume `history.gap k > ε` for every
-- `k ≤ levelMethodIterationCap M_f D ε α`. Partition the indices into maximal consecutive blocks
-- on which the terminal gap stays at least `(1 - α)` times the initial gap. The block bound
-- `hblock` controls the length of each block, while the block-start gaps grow geometrically by
-- the factor `(1 - α)⁻¹`; summing the resulting geometric series yields the displayed iteration
-- cap, yielding `exists_stopping_index_le_levelMethodIterationCap`. For the optimality-gap claim,
-- apply
-- `history.optimalValue_sub_fStar_le_epsilon_of_shouldStop`.
theorem exists_stopping_index_le_levelMethodIterationCap_and_optimalValue_sub_fStar_le_epsilon
    (history : LevelMethodHistory) {fStar M_f D ε α : ℝ}
    (hε : 0 < ε)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hvalidLower : ∀ k : ℕ, history.approximateOptimalValue k ≤ fStar)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    (∃ k ≤ levelMethodIterationCap M_f D ε α,
      history.shouldStop ε k) ∧
      ∀ k : ℕ,
        history.shouldStop ε k →
          history.optimalValue k - fStar ≤ ε := by
  refine ⟨exists_stopping_index_le_levelMethodIterationCap history hε hα hblock, ?_⟩
  intro k hk
  exact history.optimalValue_sub_fStar_le_epsilon_of_shouldStop k (hvalidLower k) hk

/-! ### Lemma_3_3_2 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 3.3.2 lies in the chapter's level-method one-step cutting-plane domain.

Sampled owner declarations:
* `maxTypeObjective` in `Chap02/Lemma_2_18`, the project owner for finite maxima of a nonempty
  finite family of real-valued functions
* `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the canonical evaluation bridge for that owner
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner scalar history
* `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
* `LevelMethodHistory.levelValue` in `Lemma_3_3_1`, the canonical level value `ℓ_k(α)`
* `LevelMethodHistory.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap` in `Lemma_3_3_1`, the
  owner scalar rewrite used below

Best owner abstraction:
* the generic finite-max owner `maxTypeObjective`
* the scalar side of the one-step estimate is organized by `LevelMethodHistory`

Primitive data:
* the sampled points `x k`, `x (k + 1)` and chosen slopes `g k`
* the owner scalar history `history`

Derived API:
* `history.gap k`
* `history.levelValue α k`
* the source-facing Kelley specialization `nonsmoothModel f x g k` of `maxTypeObjective`

Accordingly, this file keeps `nonsmoothModel` only as the source-facing Kelley specialization of
the existing finite-max owner `maxTypeObjective`, and states the one-step norm estimate directly
over the scalar-history owner instead of repeating separate sequence-level gap and level-value
definitions.
-/

/-- The nonsmooth model `\hat f_k` is the finite maximum of the sampled affine minorants built
from `x₀, …, x_k` and the chosen subgradients `g₀, …, g_k` in the ambient real inner-product
space. This is the direct Kelley specialization of the project owner `maxTypeObjective`. -/
abbrev nonsmoothModel (f : E → ℝ) (x g : ℕ → E) (k : ℕ) : E → ℝ :=
  maxTypeObjective
    (fun i : Fin (k + 1) ↦ fun y ↦ f (x i) + inner ℝ (g i) (y - x i))

namespace NonsmoothModelNotation

scoped notation:max "f̂[" X:arg "; " f:arg "; " g:arg "](" k:arg ")" =>
  nonsmoothModel f X g k

end NonsmoothModelNotation

open scoped NonsmoothModelNotation

/-- Evaluating `f̂[X; f; g](k)` at `y` gives the finite maximum over the first `k + 1` sampled
affine minorants. -/
-- Proof sketch: unfold `nonsmoothModel`; the displayed `Finset.sup'` expression is exactly the
-- defining finite maximum.
theorem nonsmoothModel_apply
    (f : E → ℝ) (X g : ℕ → E) (k : ℕ) (y : E) :
    f̂[X; f; g](k) y =
      Finset.univ.sup' Finset.univ_nonempty fun i : Fin (k + 1) ↦
        f (X i) + inner ℝ (g i) (y - X i) := by
  simpa using
    (maxTypeObjective_apply
      (fun i : Fin (k + 1) ↦ fun z ↦ f (X i) + inner ℝ (g i) (z - X i))
      y)

/-- Lemma 3.3.2: if the level value at iteration `k` dominates the sampled model at `x_{k+1}`,
the record value satisfies `f_k^* ≤ f(x_k)`, and the selected subgradient norm is bounded by
`M_f`, then the step length satisfies
`‖x_{k+1} - x_k‖ ≥ ((1 - α) δ_k) / M_f`. -/
-- Proof sketch: rewrite `history.levelValue α k` as
-- `history.optimalValue k - (1 - α) * history.gap k`, compare `history.optimalValue k` with
-- `f(x k)`, and use `nonsmoothModel_apply` with the `Fin.last k` term of the finite supremum to get
-- `(1 - α) * δ_k ≤ -⟪g_k, x_{k+1} - x_k⟫`. Then bound the inner product by
-- `‖g_k‖ * ‖x_{k+1} - x_k‖ ≤ M_f * ‖x_{k+1} - x_k‖` and divide by `M_f > 0`.
lemma step_norm_lower_bound_of_level_method_assumptions
    {f : E → ℝ} {X g : ℕ → E} {history : LevelMethodHistory}
    (α Mf : ℝ) {k : ℕ}
    (hrecord_le_current : history.optimalValue k ≤ f (X k))
    (hlevel_ge_model :
      history.levelValue α k ≥
        f̂[X; f; g](k) (X (k + 1)))
    (hsubgradient_bound : ‖g k‖ ≤ Mf)
    (hMf_pos : 0 < Mf) :
    ‖X (k + 1) - X k‖ ≥
      ((1 - α) * history.gap k) / Mf := by
  let step := X (k + 1) - X k
  have hterm_le_model :
      f (X k) + inner ℝ (g k) step ≤
        f̂[X; f; g](k) (X (k + 1)) := by
    rw [nonsmoothModel_apply]
    simpa [step] using
      (Finset.le_sup'
        (fun i : Fin (k + 1) ↦ f (X i) + inner ℝ (g i) (X (k + 1) - X i))
        (by simp : Fin.last k ∈ Finset.univ))
  have hmodel_le_level :
      f (X k) + inner ℝ (g k) step ≤ history.levelValue α k :=
    hterm_le_model.trans hlevel_ge_model
  rw [history.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap α k] at hmodel_le_level
  have hgap_le_neg_inner :
      (1 - α) * history.gap k ≤ -inner ℝ (g k) step := by
    linarith
  have hinner_abs :
      |inner ℝ (g k) step| ≤ ‖g k‖ * ‖step‖ := by
    simpa using abs_real_inner_le_norm (g k) step
  have hgap_le_step_mul :
      (1 - α) * history.gap k ≤ Mf * ‖step‖ := by
    calc
      (1 - α) * history.gap k ≤ -inner ℝ (g k) step := hgap_le_neg_inner
      _ ≤ |inner ℝ (g k) step| := neg_le_abs _
      _ ≤ ‖g k‖ * ‖step‖ := hinner_abs
      _ ≤ Mf * ‖step‖ :=
        mul_le_mul_of_nonneg_right hsubgradient_bound (norm_nonneg _)
  have hdiv :
      ((1 - α) * history.gap k) / Mf ≤ ‖step‖ :=
    (div_le_iff₀ hMf_pos).2 (by simpa [mul_comm] using hgap_le_step_mul)
  simpa [ge_iff_le, step] using hdiv

end

/-! ### Theorem_3_3_2 (from Chap03) -/
noncomputable section

open HasGeometricRateOfConvergence

universe u v

/-
Primary domain: scalar geometric-decay thresholds for the complete-data selected exact values.

Owner declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.iterationThreshold` in `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le` in
  `Chap01/Definition_1_2_6.lean`
* `HasGeometricRateOfConvergence.le_target_at_natCeil_iterationThreshold` in
  `Chap01/Definition_1_2_6.lean`

Best owner abstraction:
* `HasGeometricRateOfConvergence` on the scalar sequence
  `k ↦ exactValue (j k) X (t k)`

Primitive data:
* the selector sequence `j` and threshold sequence `t`
* the exact-value family
* the pointwise geometric upper bound from Lemma `3.3.7`

Derived API:
* the explicit logarithmic threshold consequence in Theorem `3.3.2`

Source/core/bridge triage:
* source-facing: Theorem `3.3.2`, stated with the textbook logarithmic formula and the direct
  contraction hypothesis `1 < 2 * (1 - ε)`
* core/canonical: `HasGeometricRateOfConvergence` and its threshold API
* bridge/view: the conversion from the displayed geometric bound to the owner predicate

The former file duplicated the owner threshold as a local abbreviation
`completeDataMasterIterationCountBound` and duplicated the owner threshold theorem in a second
public helper specialization. The refined file removes those parallel declarations and keeps only
the source-facing theorem specialized to the explicit textbook formula. The contraction input is
kept in the direct scalar form `1 < 2 * (1 - ε)` rather than the derived logarithmic reformulation
`0 < log (2 * (1 - ε))`.
-/

section

variable {χ : Type u} {ι : Type v}

/-- Theorem 3.3.2: in view of Lemma `3.3.7`, the master process reaches the global-stop threshold,
and hence the estimate `(3.3.9)`, after at most
`log ((t₀ - t^*) / ((1 - ε) ε)) / log (2 (1 - ε))` full iterations. -/
-- Proof sketch: reinterpret the geometric estimate from Lemma `3.3.7` as the canonical owner
-- statement `HasGeometricRateOfConvergence` for the selected exact-value sequence, then apply
-- `HasGeometricRateOfConvergence.le_target_at_natCeil_iterationThreshold` and simplify the owner
-- threshold to the displayed logarithmic formula. The canonical contraction input is the direct
-- scalar inequality `1 < 2 * (1 - ε)`, not the derived positivity of `log (2 * (1 - ε))`.
theorem selected_exactValue_le_epsilon_at_natCeil_masterIterationCountBound
    {ε tStar : ℝ} {X : χ} {t : ℕ → ℝ} {j : ℕ → ι}
    {exactValue : ι → χ → ℝ → ℝ}
    (hε : 0 < ε)
    (hε_contract : 1 < 2 * (1 - ε))
    (hgeom :
      ∀ k : ℕ,
        exactValue (j k) X (t k) ≤
          ((t 0 - tStar) / (1 - ε)) * ((1 / (2 * (1 - ε))) ^ k)) :
    exactValue
        (j ⌈Real.log ((t 0 - tStar) / ((1 - ε) * ε)) / Real.log (2 * (1 - ε))⌉₊)
        X
        (t ⌈Real.log ((t 0 - tStar) / ((1 - ε) * ε)) / Real.log (2 * (1 - ε))⌉₊) ≤
      ε := by
  let base : ℝ := 2 * (1 - ε)
  have hrate :
      HasGeometricRateOfConvergence
        (fun k ↦ exactValue (j k) X (t k))
        (1 - (2 * (1 - ε))⁻¹)
        ((t 0 - tStar) / (1 - ε)) := by
    intro k
    simpa [div_eq_mul_inv] using hgeom k
  have hbase_pos : 0 < base := by
    simpa [base] using (lt_trans zero_lt_one hε_contract)
  have hbase_ne : base ≠ 0 := ne_of_gt hbase_pos
  have howner_contract : 1 < (1 - (1 - base⁻¹))⁻¹ := by
    calc
      1 < base := by simpa [base] using hε_contract
      _ = (1 - (1 - base⁻¹))⁻¹ := by
        field_simp [hbase_ne]
        simp
  simpa [base, iterationThreshold, Real.logb, hbase_ne, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using
    HasGeometricRateOfConvergence.le_target_at_natCeil_iterationThreshold
      hrate howner_contract hε

end

end

/-! ### Definition_3_3 (from Chap03) -/
universe u

/- Definition 3.3 is the chapter's `WithTop`-valued convex-analysis bridge.

Sampled owner-style declarations:
- mathlib `WithTop.untop₀`
- mathlib `ConvexOn`
- mathlib `StrictConvexOn`
- mathlib `ConcaveOn`

Best owner abstraction:
- primitive bridge data: `withTopEffectiveDomain`, `withTopToEReal`, `withTopRealPart`,
  `constrainedSublevelSet`, `constrainedEpigraph`, and the source-facing owner
  `WithTopConvexAnalysis.effectiveEpigraph`
- core/canonical convexity owners:
  `ConvexOn ℝ (dom f) (withTopRealPart f)`,
  `StrictConvexOn ℝ (dom f) (withTopRealPart f)`, and
  `ConcaveOn ℝ (dom f) (withTopRealPart f)`

Primitive data:
- the finite-value domain `dom f`
- the canonical `EReal` image `withTopToEReal`
- the finite real representative `withTopRealPart f`
- the constrained real sublevel set `constrainedSublevelSet Q f β`
- the constrained epigraph `constrainedEpigraph Q f`
- the effective epigraph owner `WithTopConvexAnalysis.effectiveEpigraph f`

Derived API:
- `mem_withTopEffectiveDomain_iff`
- `withTopToEReal`
- `coe_withTopRealPart`
- `withTopRealPart_eq_untop`
- `withTopRealPart_le_iff`
- `le_withTopRealPart_iff`
- `mem_constrainedSublevelSet_iff`
- `mem_constrainedEpigraph_iff`
- `WithTopConvexAnalysis.mem_effectiveEpigraph_iff`
- `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`
- `constrainedEpigraph_eq_prod_univ_inter_of_subset`

Source/core/bridge triage:
- source-facing: the chapter's `WithTop`-valued convexity vocabulary from Definition 3.3
- core/canonical: mathlib `ConvexOn`, `StrictConvexOn`, `ConcaveOn`
- bridge/view: `withTopEffectiveDomain`, `withTopRealPart`, `constrainedEpigraph`, and
  `WithTopConvexAnalysis.effectiveEpigraph`

The textbook states these notions on `ℝⁿ`, but the bridge data itself does not use any Euclidean
structure. This file therefore keeps the same semantics while exposing the owner bridge on an
arbitrary domain type, with the textbook notation `dom f` on the theorem surface, while the three
convexity clauses are recalled directly from the canonical mathlib owners instead of being
repackaged as new predicate names.
-/

/-- The effective domain of an `ℝ ∪ {+∞}`-valued function, i.e. the points where the value is
finite. -/
abbrev withTopEffectiveDomain {X : Type u} (f : X → WithTop ℝ) : Set X :=
  {x | f x < ⊤}

/-- Textbook notation for the effective domain of an `ℝ ∪ {+∞}`-valued function. -/
scoped[WithTopConvexAnalysis] notation "dom " f:arg => withTopEffectiveDomain f

open scoped WithTopConvexAnalysis

/-- The canonical embedding of `ℝ ∪ {+∞}` into `[-∞, +∞]`. -/
abbrev withTopToEReal : WithTop ℝ → EReal := ((↑) : WithTop ℝ → WithBot (WithTop ℝ))

/-- The real-valued representative of an `ℝ ∪ {+∞}`-valued function, obtained by reading off its
finite value on the effective domain and extending by `0` outside that domain. -/
abbrev withTopRealPart {X : Type u} (f : X → WithTop ℝ) : X → ℝ :=
  WithTop.untop₀ ∘ f

/-- A point lies in the effective domain exactly when the function value is finite there. -/
@[simp] theorem mem_withTopEffectiveDomain_iff {X : Type u} {f : X → WithTop ℝ} {x : X} :
    x ∈ dom f ↔ f x < ⊤ :=
  Iff.rfl

/-- On the effective domain, the real-valued representative agrees with the underlying finite
real value of the function. -/
theorem withTopRealPart_eq_untop {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) :
    withTopRealPart f x = (f x).untop (ne_of_lt hx) := by
  have hne : f x ≠ ⊤ := ne_of_lt hx
  apply WithTop.coe_injective
  simpa [withTopRealPart] using WithTop.coe_untop₀_of_ne_top hne

/-- On the effective domain, coercing the finite real part back to `WithTop ℝ` recovers the
original function value. -/
@[simp] theorem coe_withTopRealPart {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) :
    ((withTopRealPart f x : ℝ) : WithTop ℝ) = f x := by
  simpa [withTopRealPart] using WithTop.coe_untop₀_of_ne_top (ne_of_lt hx)

/-- On the effective domain, a real upper bound on `withTopRealPart f x` is exactly an upper
bound on `f x` by the corresponding real point of `WithTop ℝ`. -/
theorem withTopRealPart_le_iff {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    withTopRealPart f x ≤ r ↔ f x ≤ (r : WithTop ℝ) := by
  rw [← coe_withTopRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- On the effective domain, a real lower bound by `withTopRealPart f x` is exactly a lower bound
by the corresponding real point of `WithTop ℝ`. -/
theorem le_withTopRealPart_iff {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    r ≤ withTopRealPart f x ↔ (r : WithTop ℝ) ≤ f x := by
  rw [← coe_withTopRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- The epigraph of an `ℝ ∪ {+∞}`-valued function constrained to a feasible set `Q`. -/
abbrev constrainedEpigraph {X : Type u} (Q : Set X) (f : X → WithTop ℝ) : Set (X × ℝ) :=
  {p | p.1 ∈ Q ∧ f p.1 ≤ p.2}

/-- The constrained real sublevel set of an `ℝ ∪ {+∞}`-valued function over a feasible set `Q`.
-/
abbrev constrainedSublevelSet {X : Type u}
    (Q : Set X) (f : X → WithTop ℝ) (β : ℝ) : Set X :=
  {x | x ∈ Q ∧ f x ≤ β}

/-- Membership in `constrainedSublevelSet Q f β` means belonging to `Q` and satisfying the
sublevel inequality `f x ≤ β`. -/
@[simp] theorem mem_constrainedSublevelSet_iff
    {X : Type u} {Q : Set X} {f : X → WithTop ℝ} {β : ℝ} {x : X} :
    x ∈ constrainedSublevelSet Q f β ↔ x ∈ Q ∧ f x ≤ β :=
  Iff.rfl

/-- Membership in the constrained epigraph means lying in `Q` and being above the function
value. -/
@[simp] theorem mem_constrainedEpigraph_iff
    {X : Type u} {Q : Set X} {f : X → WithTop ℝ} {p : X × ℝ} :
    p ∈ constrainedEpigraph Q f ↔ p.1 ∈ Q ∧ f p.1 ≤ p.2 :=
  Iff.rfl

namespace WithTopConvexAnalysis

/-- The effective epigraph of an `ℝ ∪ {+∞}`-valued function. -/
abbrev effectiveEpigraph {X : Type u} (f : X → WithTop ℝ) : Set (X × ℝ) :=
  constrainedEpigraph (dom f) f

/-- Membership in `effectiveEpigraph f` means belonging to the effective domain and lying above
the original `WithTop ℝ`-valued function. -/
@[simp] theorem mem_effectiveEpigraph_iff
    {X : Type u} {f : X → WithTop ℝ} {p : X × ℝ} :
    p ∈ effectiveEpigraph f ↔ p.1 ∈ dom f ∧ f p.1 ≤ p.2 :=
  Iff.rfl

/-- The effective epigraph of `f` is exactly the ordinary epigraph of its finite real part over
`dom f`. -/
theorem effectiveEpigraph_eq_epigraph_withTopRealPart
    {X : Type u} (f : X → WithTop ℝ) :
    effectiveEpigraph f = {p : X × ℝ | p.1 ∈ dom f ∧ withTopRealPart f p.1 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (withTopRealPart_le_iff hp).2 hp₂⟩
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (withTopRealPart_le_iff hp).1 hp₂⟩

end WithTopConvexAnalysis

/-- Restricting the feasible set from `Q` to a subset `Q₁` cuts the constrained epigraph by the
corresponding base cylinder. -/
theorem constrainedEpigraph_eq_prod_univ_inter_of_subset
    {X : Type u} {Q Q₁ : Set X} {f : X → WithTop ℝ} (hQ₁Q : Q₁ ⊆ Q) :
    constrainedEpigraph Q₁ f = (Q₁ ×ˢ (Set.univ : Set ℝ)) ∩ constrainedEpigraph Q f := by
  ext p
  constructor
  · rintro ⟨hpQ₁, hfp⟩
    refine ⟨?_, ?_⟩
    · simpa [Set.mem_prod] using And.intro hpQ₁ (Set.mem_univ p.2)
    · exact mem_constrainedEpigraph_iff.2 ⟨hQ₁Q hpQ₁, hfp⟩
  · rintro ⟨hpQ₁, hp⟩
    rw [Set.mem_prod] at hpQ₁
    exact mem_constrainedEpigraph_iff.2 ⟨hpQ₁.1, (mem_constrainedEpigraph_iff.1 hp).2⟩

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → WithTop ℝ)

/- Definition 3.3 (1), generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is convex when its effective domain is convex and its finite-value part satisfies the
Jensen inequality there. -/
#check ConvexOn ℝ (dom f) (withTopRealPart f)

/- Definition 3.3 (2), generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is strictly convex when its effective domain is convex and its finite-value part
satisfies the strict Jensen inequality there. -/
#check StrictConvexOn ℝ (dom f) (withTopRealPart f)

/- Definition 3.3 (3), generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is concave when its finite-value part is concave on the same effective domain. -/
#check ConcaveOn ℝ (dom f) (withTopRealPart f)

end Convexity

/-! ### Lemma_3_3 (from Chap03) -/
universe u

noncomputable section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/- Lemma 3.3 lies in the chapter's support-function / convex-hull domain.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_eq`
- mathlib `sSup_union`

Best owner abstraction:
- the chapter owner `supportFunction` together with its canonical convex-hull invariance theorem
  `supportFunction_convexHull_eq`

Primitive data:
- two sets `Q₁ Q₂ : Set E`

Derived API:
- the textbook pointwise specialization
  `ξ[convexHull ℝ (Q₁ ∪ Q₂)] x = max (ξ[Q₁] x) (ξ[Q₂] x)`

Source/core/bridge triage:
- source-facing: `supportFunction_convexHull_union_eq_max`
- core/canonical: `supportFunction` and `supportFunction_convexHull_eq`
- bridge/view: `supportFunction_apply` and `sSup_union`
-/

recall supportFunction

recall supportFunction_apply

recall supportFunction_convexHull_eq

/-- Lemma 3.3: in a real inner-product space, the support function of the convex hull of
`Q₁ ∪ Q₂` is the pointwise maximum of the support functions of `Q₁` and `Q₂`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: rewrite away the convex hull by `supportFunction_convexHull_eq`, then expand the
-- support function of the union with `supportFunction_apply` and `sSup_union`.
theorem supportFunction_convexHull_union_eq_max
    (Q₁ Q₂ : Set E) (x : E) :
    ξ[convexHull ℝ (Q₁ ∪ Q₂)] x = max (ξ[Q₁] x) (ξ[Q₂] x) := by
  rw [supportFunction_convexHull_eq]
  simp [supportFunction_apply, Set.image_union, sSup_union]

end

/-! ### Lemma_3_3_3 (from Chap03) -/
noncomputable section

universe u

open scoped LevelMethodNotation

/- Lemma 3.3.3 lies in the level-method history / real-inner-product projection domain.

Sampled owner declarations:
* `LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity` in
  `Lemma_3_3_1`
* `constrainedSublevelSet` in `Definition_3_3`, recalled in `Definition_3_68`
* `IsProjectionPointOn.iff_isMinOn` in `Definition_2_33`
* `IsProjectionPointOn.pythagorean_ineq` in `Lemma_2_14`
* `Bornology.IsBounded`, `Metric.diam`, and `Metric.dist_le_diam_of_mem` in mathlib's metric
  boundedness API
* the notation `δ[history](k)`, `ℓ[history](α, k)`, and `𝓛[Q, model, history](α, k)` in
  `Lemma_3_3_1` and `Definition_3_68`

Best owner abstractions:
* the scalar level-method data are organized by `LevelMethodHistory`
* the projection step is organized by `IsProjectionPointOn`

Primitive data:
* the iterate sequence `x`
* the terminal comparison point `xStar`
* the bounded feasible set `Q`
* the model family `model`
* the boundedness witness for `Q` and the diameter bound `Metric.diam Q ≤ D`

Derived API:
* the terminal level-set membership is obtained from the owner interval-monotonicity comparison
  together with `𝓛[Q, model, history](α, i)`
* the one-step squared-distance drop is obtained from `IsProjectionPointOn.pythagorean_ineq`
* the initial-distance estimate `‖x k - xStar‖ ≤ D` is derived from `Metric.dist_le_diam_of_mem`
  and `Metric.diam Q ≤ D`

Source/core/bridge triage:
* source-facing: the step-count estimate and the final block-length bound for bounded feasible
  sets
* core/canonical: `LevelMethodHistory`, `constrainedSublevelSet`, and `IsProjectionPointOn`
* bridge/view: converting a projection hypothesis to `IsMinOn` if needed via
  `IsProjectionPointOn.iff_isMinOn`

Accordingly, this file keeps only the genuinely new counting estimate and the source-facing
bounded-feasible-set block bound. The helper level-set and projection facts are reused directly
from their owners rather than repeated here as parallel public declarations.
-/

section Count

variable {E : Type u} [SeminormedAddCommGroup E]

/-- A uniform positive lower bound on the step lengths together with a telescoping squared-distance
estimate bounds the number of indices in the step range. -/
-- Proof sketch: square the step lower bound to get a uniform lower bound on every
-- `‖x (i + 1) - x i‖ ^ 2`. Sum the distance-drop inequalities for `i = k, …, p`; the middle
-- squared-distance terms telescope, leaving
-- `((p + 1 - k : ℕ) : ℝ) * c^2 ≤ ‖x k - xStar‖^2 ≤ D^2`. The truncated subtraction already makes
-- the bound vacuous when `p < k`, so no separate order hypothesis is needed. Divide by the
-- positive number `c^2`.
theorem count_le_sqdist_ratio_of_uniform_step_lower_bound
    {x : ℕ → E} {xStar : E} {c D : ℝ} {k p : ℕ}
    (hc_pos : 0 < c)
    (hstep_drop :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ‖x (i + 1) - xStar‖ ^ (2 : ℕ) + ‖x (i + 1) - x i‖ ^ (2 : ℕ) ≤
          ‖x i - xStar‖ ^ (2 : ℕ))
    (hstep_lower :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → c ≤ ‖x (i + 1) - x i‖)
    (hstart_dist : ‖x k - xStar‖ ≤ D) :
    ((p + 1 - k : ℕ) : ℝ) ≤ D ^ (2 : ℕ) / c ^ (2 : ℕ) := by
  by_cases hkp : k ≤ p
  · have hc_sq_pos : 0 < c ^ (2 : ℕ) := by
      nlinarith [hc_pos]
    have htelescoping :
        ∀ n : ℕ, k + n ≤ p + 1 →
          (n : ℝ) * c ^ (2 : ℕ) + ‖x (k + n) - xStar‖ ^ (2 : ℕ) ≤
            ‖x k - xStar‖ ^ (2 : ℕ) := by
      intro n
      induction n with
      | zero =>
          intro _
          simp
      | succ n ihn =>
          intro hkn_succ
          have hkn : k + n ≤ p + 1 := by
            omega
          have hik : k ≤ k + n := Nat.le_add_right _ _
          have hip : k + n ≤ p := by
            omega
          have hdrop := hstep_drop hik hip
          have hstep_sq : c ^ (2 : ℕ) ≤ ‖x (k + n + 1) - x (k + n)‖ ^ (2 : ℕ) := by
            nlinarith [hstep_lower hik hip]
          have hi := ihn hkn
          have hdrop' :
              ‖x (k + n + 1) - xStar‖ ^ (2 : ℕ) + c ^ (2 : ℕ) ≤
                ‖x (k + n) - xStar‖ ^ (2 : ℕ) := by
            nlinarith
          have hnext :
              ((n + 1 : ℕ) : ℝ) * c ^ (2 : ℕ) + ‖x (k + n + 1) - xStar‖ ^ (2 : ℕ) ≤
                ‖x k - xStar‖ ^ (2 : ℕ) := by
            have hnext' :
                (n : ℝ) * c ^ (2 : ℕ) +
                    (‖x (k + n + 1) - xStar‖ ^ (2 : ℕ) + c ^ (2 : ℕ)) ≤
                  ‖x k - xStar‖ ^ (2 : ℕ) := by
              nlinarith
            simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, add_left_comm, add_comm,
              mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hnext'
          simpa [Nat.add_assoc] using hnext
    have hcount_sq :
        (((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ)) ≤ ‖x k - xStar‖ ^ (2 : ℕ) := by
      have hmain := htelescoping (p + 1 - k) (by omega)
      have hnonneg : 0 ≤ ‖x (k + (p + 1 - k)) - xStar‖ ^ (2 : ℕ) := by positivity
      have hbound :
          ((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ) ≤
            ((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ) +
              ‖x (k + (p + 1 - k)) - xStar‖ ^ (2 : ℕ) := by
        linarith
      exact hbound.trans hmain
    have hstart_sq : ‖x k - xStar‖ ^ (2 : ℕ) ≤ D ^ (2 : ℕ) := by
      have hD_nonneg : 0 ≤ D := le_trans (norm_nonneg _) hstart_dist
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hD_nonneg] using hstart_dist)
    have hcount : ((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ) ≤ D ^ (2 : ℕ) :=
      hcount_sq.trans hstart_sq
    exact (le_div_iff₀ hc_sq_pos).2 hcount
  · have hpk : p + 1 ≤ k := by omega
    have : p + 1 - k = 0 := Nat.sub_eq_zero_of_le hpk
    have hnonneg : 0 ≤ D ^ (2 : ℕ) / c ^ (2 : ℕ) := by
      positivity
    simpa [this] using hnonneg

end Count

section Projection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 3.3.3: let `Q` be the bounded feasible set from problem `(3.3.1)` with
`diam Q ≤ D`. If the gap satisfies `δ_p ≥ (1 - α) δ_k`, and if the iterates are generated by
projections onto the level sets
`𝓛_i(α) = {x ∈ Q | \hat f_i(X; x) ≤ (1 - α)\hat f_i^* + α f_i^*}` with the step-size lower bound
coming from Lemma `3.3.2`, then
`p + 1 - k ≤ M_f^2 D^2 / ((1 - α)^2 δ_p^2)`. -/
-- Proof sketch: combine
-- `history.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity`
-- with the assumptions `model p xStar = fhat(history, p)` and
-- `model i xStar ≤ model p xStar` for `k ≤ i ≤ p` to place `xStar` in every intermediate level
-- set `𝓛[Q, model, history](α, i)`.
-- Then apply
-- `IsProjectionPointOn.pythagorean_ineq` to each projection step to get
-- `‖x (i + 1) - xStar‖^2 + ‖x (i + 1) - x i‖^2 ≤ ‖x i - xStar‖^2`. The step-size hypothesis gives
-- `‖x (i + 1) - x i‖ ≥ ((1 - α) δ[history](i)) / M_f`, and the antitonicity
-- `δ[history](p) ≤ δ[history](i)` on the block upgrades this to the uniform bound
-- `((1 - α) δ[history](p)) / M_f`. Finally use
-- `Metric.dist_le_diam_of_mem` with `x k ∈ Q`, `xStar ∈ Q`, and `Metric.diam Q ≤ D` to bound
-- `‖x k - xStar‖ ≤ D` and invoke
-- `count_le_sqdist_ratio_of_uniform_step_lower_bound`.
theorem iteration_count_bound_of_bounded_feasible_set
    (history : LevelMethodHistory) (Q : Set E) (model : ℕ → E → ℝ)
    (x : ℕ → E) {α Mf D : ℝ} {k p : ℕ} {xStar : E}
    (hα : α < 1)
    (hoptimal_mono :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → fstar(history, p) ≤ fstar(history, i))
    (hgap_antitone :
      ∀ ⦃i j : ℕ⦄, k ≤ i → i ≤ j → j ≤ p → δ[history](j) ≤ δ[history](i))
    (hgap_large : δ[history](p) ≥ (1 - α) * δ[history](k))
    (hgap_pos : 0 < δ[history](p))
    (hMf_pos : 0 < Mf)
    (hQ_bounded : Bornology.IsBounded Q)
    (hdiam : Metric.diam Q ≤ D)
    (hxk_mem : x k ∈ Q)
    (hxStar_mem : xStar ∈ Q)
    (hxStar_terminal : model p xStar = fhat(history, p))
    (hmodel_le_terminal :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → model i xStar ≤ model p xStar)
    (hconvex :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        Convex ℝ (𝓛[Q, model, history](α, i)))
    (hprojection :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        IsProjectionPointOn (𝓛[Q, model, history](α, i)) (x i) (x (i + 1)))
    (hstep_lower :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ‖x (i + 1) - x i‖ ≥
          ((1 - α) * δ[history](i)) / Mf) :
    ((p + 1 - k : ℕ) : ℝ) ≤
      (Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) /
        ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ)) := by
  have hOneSubAlpha_pos : 0 < 1 - α := sub_pos.mpr hα
  have hOneSubAlpha_nonneg : 0 ≤ 1 - α := le_of_lt hOneSubAlpha_pos
  have hxStar_mem_level :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → xStar ∈ 𝓛[Q, model, history](α, i) := by
    intro i hki hip
    refine mem_constrainedSublevelSet_iff.2 ⟨hxStar_mem, ?_⟩
    have hlevel :=
      history.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity
        (le_of_lt hα)
        hoptimal_mono
        (fun {_} hki' hip' ↦ hgap_antitone (Nat.le_refl k) hki' hip')
        hgap_large
        hki
        hip
    have hmodel : model i xStar ≤ fhat(history, p) := by
      rw [← hxStar_terminal]
      exact hmodel_le_terminal hki hip
    exact_mod_cast le_trans hmodel hlevel
  have hstep_drop_sq :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ‖x (i + 1) - xStar‖ ^ (2 : ℕ) + ‖x (i + 1) - x i‖ ^ (2 : ℕ) ≤
          ‖x i - xStar‖ ^ (2 : ℕ) := by
    intro i hki hip
    simpa [norm_sub_rev, add_comm] using
      IsProjectionPointOn.pythagorean_ineq
        (hconvex hki hip) (hprojection hki hip) (hxStar_mem_level hki hip)
  have hstep_uniform :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ((1 - α) * δ[history](p)) / Mf ≤ ‖x (i + 1) - x i‖ := by
    intro i hki hip
    have hterminal_le : δ[history](p) ≤ δ[history](i) :=
      hgap_antitone hki hip (Nat.le_refl p)
    have hscaled :
        ((1 - α) * δ[history](p)) / Mf ≤ ((1 - α) * δ[history](i)) / Mf := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hterminal_le hOneSubAlpha_nonneg)
        (le_of_lt hMf_pos)
    exact hscaled.trans (hstep_lower hki hip)
  have hstart_dist : ‖x k - xStar‖ ≤ D := by
    have hdist : dist (x k) xStar ≤ Metric.diam Q :=
      Metric.dist_le_diam_of_mem hQ_bounded hxk_mem hxStar_mem
    simpa [dist_eq_norm] using hdist.trans hdiam
  have hc_pos : 0 < ((1 - α) * δ[history](p)) / Mf := by
    positivity
  have hcount :=
    count_le_sqdist_ratio_of_uniform_step_lower_bound
      hc_pos hstep_drop_sq hstep_uniform hstart_dist
  have hMf_ne : Mf ≠ 0 := ne_of_gt hMf_pos
  have hgap_ne : δ[history](p) ≠ 0 := ne_of_gt hgap_pos
  have hOneSubAlpha_ne : 1 - α ≠ 0 := ne_of_gt hOneSubAlpha_pos
  calc
    ((p + 1 - k : ℕ) : ℝ)
        ≤ D ^ (2 : ℕ) / ((((1 - α) * δ[history](p)) / Mf) ^ (2 : ℕ)) := hcount
    _ = (Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ)) := by
          field_simp [hMf_ne, hgap_ne, hOneSubAlpha_ne]

end Projection

/-! ### Proposition_3_3 (from Chap03) -/
/- Proposition 3.3 lies in the chapter's real convex-analysis / epigraph domain.

Primary domain:
- convexity of the absolute value function on `ℝ`;
- the epigraph of `x ↦ |x|` as a closed subset of `ℝ × ℝ`;
- the half-space presentation of that epigraph.

Sampled owner-style declarations:
- mathlib `convexOn_univ_norm`, the canonical convexity owner for norms on real normed spaces;
- mathlib `IsClosed.epigraph`, the canonical closed-epigraph owner for continuous real-valued
  functions on closed domains;
- mathlib `abs_le`, the canonical order-theoretic characterization of `|x| ≤ t`.

Best owner abstraction:
- core/canonical: `ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|)` and the standard epigraph subset
  `{p : ℝ × ℝ | |p.1| ≤ p.2}`;
- bridge/view: the half-space presentation
  `{p : ℝ × ℝ | p.2 ≥ p.1} ∩ {p : ℝ × ℝ | p.2 ≥ -p.1}`.

Primitive data:
- the function `x ↦ |x|`.

Derived API:
- the closedness of its epigraph;
- the half-space description of the same epigraph.

Source/core/bridge triage:
- source-facing: the three statements of Proposition 3.3;
- core/canonical: mathlib `ConvexOn`, continuity, and epigraph closedness;
- bridge/view: the half-space equality translating the epigraph inequality into two affine
  inequalities.

The file therefore keeps the three textbook statements as the public surface, but avoids any local
wrapper definition for the epigraph because the standard mathlib epigraph set is already the right
owner expression in this domain.
-/

/-- Proposition 3.3 (1): the absolute value function on `ℝ` is convex on all of `ℝ`. -/
-- Proof sketch: identify `|x|` with the norm on `ℝ` and use the standard convexity of the norm.
theorem abs_convexOn_univ :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
  simpa [Real.norm_eq_abs] using
    (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))

/-- Proposition 3.3 (2): the epigraph of the absolute value function on `ℝ` is closed in
`ℝ × ℝ`. -/
-- Proof sketch: `x ↦ |x|` is continuous on the closed domain `Set.univ`; apply the canonical
-- `IsClosed.epigraph` theorem.
theorem abs_epigraph_isClosed :
    IsClosed {p : ℝ × ℝ | |p.1| ≤ p.2} := by
  simpa using IsClosed.epigraph isClosed_univ continuous_abs.continuousOn

/-- Proposition 3.3 (3): the epigraph of the absolute value function on `ℝ` is exactly the
intersection of the half-spaces `t ≥ x` and `t ≥ -x`. -/
-- Proof sketch: rewrite `|x|` as `max x (-x)`. Then `|x| ≤ t` is equivalent to the pair of
-- inequalities `x ≤ t` and `-x ≤ t`.
theorem abs_epigraph_eq_inter_halfspaces :
    {p : ℝ × ℝ | |p.1| ≤ p.2} = {p : ℝ × ℝ | p.2 ≥ p.1} ∩ {p : ℝ × ℝ | p.2 ≥ -p.1} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [abs_le]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂, by simpa using neg_le_neg h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by simpa using neg_le_neg h₂, h₁⟩

/-! ### Theorem_3_3 (from Chap03) -/
universe u

/-
Theorem 3.3 lies in the chapter's `WithTop`-valued convex-analysis / effective-epigraph domain.

Sampled owner-style declarations:
- `WithTopConvexAnalysis.effectiveEpigraph`,
  `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`,
  `dom`, and `withTopRealPart` in `Definition_3_3`, the chapter owner surface and bridge from an
  `ℝ ∪ {+∞}`-valued function to its finite real part and effective epigraph;
- mathlib `convexOn_iff_convex_epigraph`, the core owner equivalence between `ConvexOn` and
  convexity of the ordinary epigraph.

Best owner abstraction:
- source-facing: the effective-epigraph convexity criterion below on
  `WithTopConvexAnalysis.effectiveEpigraph f`;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- bridge/view: `WithTopConvexAnalysis.effectiveEpigraph f`.

Primitive data:
- the chapter owner `dom f`;
- the chapter owner `withTopRealPart f`.

Derived API:
- `WithTopConvexAnalysis.effectiveEpigraph f`;
- `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`;
- the equivalence below, obtained by reusing `convexOn_iff_convex_epigraph`.

The previous statement duplicated the owner effective-domain set `{x | f x < ⊤}` and the finite
real-part map `x ↦ (f x).untopD 0`. These are already owned upstream by `dom f` and
`withTopRealPart f`. The remaining noncanonical surface was the raw composite
`constrainedEpigraph (dom f) f`, so this file now uses the dedicated owner
`WithTopConvexAnalysis.effectiveEpigraph f` and its upstream bridge to the ordinary epigraph of
`withTopRealPart f`.
-/

open scoped WithTopConvexAnalysis

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-- Theorem 3.3: an `ℝ ∪ {+∞}`-valued function is convex on its effective domain exactly when its
epigraph over that domain is a convex subset of the ambient product space. -/
-- Proof sketch: apply mathlib's `convexOn_iff_convex_epigraph` to the owner finite real part
-- `withTopRealPart f` on the owner effective domain `dom f`, then rewrite the resulting ordinary
-- epigraph using `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`.
theorem convexOn_iff_convex_effective_epigraph
    (f : X → WithTop ℝ) :
    ConvexOn ℝ (dom f) (withTopRealPart f) ↔
      Convex ℝ (WithTopConvexAnalysis.effectiveEpigraph f) := by
  simpa [WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart] using
    (convexOn_iff_convex_epigraph :
      ConvexOn ℝ (dom f) (withTopRealPart f) ↔
        Convex ℝ {p : X × ℝ | p.1 ∈ dom f ∧ withTopRealPart f p.1 ≤ p.2})

/-! ### Theorem_3_3_3 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

open ConstrainedLevelMethod
open scoped BigOperators

local instance
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative) :
    DecidablePred (globallyStopsAt method hrelative hfinite) := by
  classical
  exact Classical.decPred _

/- Theorem 3.3.3 lies in the constrained level-method total internal-complexity domain.

Relevant owner declarations sampled before refining:
- `HasGeometricRateOfConvergence.iterationThreshold` in `Chap01/Definition_1_2_6`, the canonical
  owner of the logarithmic outer-iteration threshold;
- `selected_exactValue_le_epsilon_at_natCeil_masterIterationCountBound` in `Theorem_3_3_2`, the
  chapter source-facing threshold theorem for the displayed logarithmic bound;
- `levelMethodIterationCap` in `Theorem_3_3_1`, the canonical floor-plus-one cap for one inner
  level-method run at tolerance `χ ε`;
- `ConstrainedLevelMethod.stoppingIndex` in `Algorithm_3_11`, the canonical full-step internal
  iteration count at one master step;
- `ConstrainedLevelMethod.globalStopIndex` in `Algorithm_3_11`, the canonical terminal-step
  internal iteration count at the first globally stopping master step;
- `levelParameterObjective` in `Definition_3_71`, the owner of the `α`-dependent scalar factor
  `α * (1 - α)^2 * (2 - α)`;

Best owner abstraction:
- source-facing: the total internal iteration count of a constrained level method up to the first
  globally stopping master step;
- core/canonical: the geometric-rate threshold owner for `N(ε)` together with the method-owned
  full-step and terminal-step internal counters;
- bridge/view: the arithmetic comparison that combines the outer-step bound with the summed
  full-step and terminal-step contributions.

Primitive data:
- the natural-ceiling outer-step cap from Theorem `3.3.2`,
  `⌈Real.log ((t0 - tStar) / ((1 - χ) * ε)) / Real.log (2 * (1 - χ))⌉₊`;
- the canonical one-run full-step cap
  `levelMethodIterationCap M_f D (χ * ε) α = ⌊K⌋ + 1`;
- the actual full-step iteration counts `stoppingIndex method hrelative hfinite i`;
- the first globally stopping master step `k`, recorded by
  `IsLeast {i : ℕ | globallyStopsAt method hrelative hfinite i} k`,
  together with its actual terminal-step iteration count
  `globalStopIndex method hrelative hfinite k hfirst.1`;
- the per-step cost owner `constrainedLevelMethodInternalIterationBound M_f D χ ε α`.

Derived API:
- the expanded rational form of the per-step factor;
- the bridge from the raw real-valued bound `K` to the owner cap `⌊K⌋ + 1`;
- the arithmetic helper that compares the summed full-step and terminal-step contributions with the
  natural-ceiling bound `(N(ε) + 1) levelMethodIterationCap ...`.

Source/core/bridge triage:
- source-facing: the constrained level method and its actual internal iteration counts;
- core/canonical: `levelMethodIterationCap`, `ConstrainedLevelMethod.stoppingIndex`,
  `ConstrainedLevelMethod.globalStopIndex`,
  `HasGeometricRateOfConvergence.iterationThreshold`, and `levelParameterObjective`;
- bridge/view: the scalar arithmetic comparison used internally once the actual iteration counts
  have already been assembled.
-/

/-- The uniform bound on the number of internal iterations contributed by one master step of the
constrained level method. -/
abbrev constrainedLevelMethodInternalIterationBound (M_f D χ ε α : ℝ) : ℝ :=
  M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
    (χ ^ (2 : ℕ) * ε ^ (2 : ℕ) * levelParameterObjective α)

/-- Unfolding `constrainedLevelMethodInternalIterationBound` recovers the displayed rational
expression for the per-step complexity bound. -/
-- Proof sketch: unfold `constrainedLevelMethodInternalIterationBound`.
theorem constrainedLevelMethodInternalIterationBound_eq
    (M_f D χ ε α : ℝ) :
    constrainedLevelMethodInternalIterationBound M_f D χ ε α =
      M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
        (χ ^ (2 : ℕ) * ε ^ (2 : ℕ) * α * (1 - α) ^ (2 : ℕ) * (2 - α)) := by
  simp [constrainedLevelMethodInternalIterationBound, levelParameterObjective, mul_assoc,
    mul_left_comm, mul_comm]

/-- The per-step constrained level-method internal-iteration bound is nonnegative for admissible
level parameters `α ∈ [0, 1]`. -/
theorem constrainedLevelMethodInternalIterationBound_nonneg
    (M_f D χ ε α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ constrainedLevelMethodInternalIterationBound M_f D χ ε α := by
  rw [constrainedLevelMethodInternalIterationBound_eq]
  have htwo_sub_nonneg : 0 ≤ 2 - α := by
    linarith [hα.2]
  have hden_nonneg :
      0 ≤ χ ^ (2 : ℕ) * ε ^ (2 : ℕ) * α * (1 - α) ^ (2 : ℕ) * (2 - α) := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (sq_nonneg χ) (sq_nonneg ε))
            hα.1)
          (sq_nonneg (1 - α)))
        htwo_sub_nonneg
  exact div_nonneg (mul_nonneg (sq_nonneg M_f) (sq_nonneg D)) hden_nonneg

/-- The displayed real-valued internal-iteration bound is dominated by the canonical floor-plus-one
one-run cap from Theorem `3.3.1` at tolerance `χ ε`. -/
theorem constrainedLevelMethodInternalIterationBound_le_levelMethodIterationCap
    (M_f D χ ε α : ℝ) :
    constrainedLevelMethodInternalIterationBound M_f D χ ε α ≤
      (levelMethodIterationCap M_f D (χ * ε) α : ℝ) := by
  simpa [constrainedLevelMethodInternalIterationBound, levelMethodIterationCap, mul_assoc,
      mul_left_comm, mul_comm, mul_pow] using
    (Nat.lt_floor_add_one
      (M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
        ((χ * ε) ^ (2 : ℕ) * levelParameterObjective α))).le

-- Arithmetic helper used by the source-facing total-complexity theorem below.
private theorem totalComplexity_le_of_natOuterCap_and_internalCostBound
    {fullMasterSteps outerCap stepCap : ℕ} {fullStepComplexity finalStepComplexity : ℝ}
    (houter : fullMasterSteps ≤ outerCap)
    (hfull : fullStepComplexity ≤ (fullMasterSteps : ℝ) * stepCap)
    (hfinal : finalStepComplexity ≤ stepCap) :
    fullStepComplexity + finalStepComplexity ≤ ((outerCap : ℝ) + 1) * stepCap := by
  have hfull' : fullStepComplexity ≤ (outerCap : ℝ) * stepCap := by
    exact hfull.trans <|
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr houter) (show 0 ≤ (stepCap : ℝ) by positivity)
  nlinarith

/-- Theorem 3.3.3: if a constrained level method has a globally stopping master step, if each
preceding full master step before the first globally stopping one is bounded by the canonical
one-run cap `levelMethodIterationCap M_f D (χ ε) α`, if the terminal globally stopping master
step satisfies the raw bound `constrainedLevelMethodInternalIterationBound M_f D χ ε α`, and if
the number of preceding full master steps is bounded by the natural ceiling of the logarithmic
threshold from Theorem `3.3.2`, then the total number of internal iterations executed up to that
first globally stopping step is bounded by `(N(ε) + 1)` copies of the canonical cap
`levelMethodIterationCap M_f D (χ ε) α`. -/
theorem constrained_level_total_internal_iterations_le
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hfirst : IsLeast {i : ℕ | globallyStopsAt method hrelative hfinite i} k)
    {M_f D tStar : ℝ}
    (houter :
      k ≤
        ⌈Real.log
            ((method.initialParameter - tStar) /
              ((1 - method.chi) * method.epsilon)) /
          Real.log (2 * (1 - method.chi))⌉₊)
    (hfull_internal :
      ∀ i < k,
        stoppingIndex method hrelative hfinite i ≤
          levelMethodIterationCap
            M_f D (method.chi * method.epsilon) method.levelCoefficient)
    (hterminal_internal :
      (globalStopIndex method hrelative hfinite k hfirst.1 : ℝ) ≤
        constrainedLevelMethodInternalIterationBound
          M_f D method.chi method.epsilon method.levelCoefficient) :
    (∑ i ∈ Finset.range k, (stoppingIndex method hrelative hfinite i : ℝ)) +
        (globalStopIndex method hrelative hfinite k hfirst.1 : ℝ) ≤
      (((⌈Real.log
              ((method.initialParameter - tStar) /
                ((1 - method.chi) * method.epsilon)) /
            Real.log (2 * (1 - method.chi))⌉₊ : ℕ) : ℝ) + 1) *
        levelMethodIterationCap
          M_f D (method.chi * method.epsilon) method.levelCoefficient := by
  let N :=
    ⌈Real.log
        ((method.initialParameter - tStar) /
          ((1 - method.chi) * method.epsilon)) /
      Real.log (2 * (1 - method.chi))⌉₊
  let J :=
    levelMethodIterationCap
      M_f D (method.chi * method.epsilon) method.levelCoefficient
  have hfull_sum :
      (∑ i ∈ Finset.range k, (stoppingIndex method hrelative hfinite i : ℝ)) ≤ (k : ℝ) * J := by
    calc
      ∑ i ∈ Finset.range k, (stoppingIndex method hrelative hfinite i : ℝ)
        ≤ ∑ _i ∈ Finset.range k, (J : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact_mod_cast hfull_internal i (Finset.mem_range.mp hi)
      _ = (k : ℝ) * J := by
            simp [J]
  have hterminal_internal' :
      (globalStopIndex method hrelative hfinite k hfirst.1 : ℝ) ≤ J := by
    exact hterminal_internal.trans <| by
      simpa [J] using
        constrainedLevelMethodInternalIterationBound_le_levelMethodIterationCap
          M_f D method.chi method.epsilon method.levelCoefficient
  exact
    totalComplexity_le_of_natOuterCap_and_internalCostBound
      (by simpa [N] using houter)
      hfull_sum
      (by simpa [J] using hterminal_internal')

end
