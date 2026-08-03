module

public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.Instances.Irrational
public import Mathlib.Topology.Instances.Rat

public section

/-- The real function equal to its input on rational inputs and zero otherwise. -/
noncomputable def rationalPart : ℝ → ℝ :=
  (Set.range (fun q : ℚ ↦ (q : ℝ))).indicator id

/-- On rational inputs, `rationalPart` is the identity. -/
@[simp]
theorem rationalPart_ratCast (q : ℚ) : rationalPart q = q := by
  simp [rationalPart]

/-- Away from the rational numbers, `rationalPart` vanishes. -/
@[simp]
theorem rationalPart_of_not_mem_range (x : ℝ)
    (hx : x ∉ Set.range (fun q : ℚ ↦ (q : ℝ))) : rationalPart x = 0 := by
  simp [rationalPart, hx]

/-- Helper for Exercise 18.6: the rational part is no farther from zero than its input. -/
private lemma dist_rationalPart_zero_le (x : ℝ) :
    dist (rationalPart x) 0 ≤ dist x 0 := by
  classical
  -- On rational inputs the two distances agree; otherwise the left side vanishes.
  by_cases hx : x ∈ Set.range (fun q : ℚ ↦ (q : ℝ))
  · obtain ⟨q, rfl⟩ := hx
    rw [rationalPart_ratCast]
  · rw [rationalPart_of_not_mem_range x hx, dist_self]
    exact dist_nonneg

/-- Helper for Exercise 18.6: `rationalPart` is continuous at zero. -/
private lemma continuousAt_rationalPart_zero : ContinuousAt rationalPart 0 := by
  -- Use the input distance itself as the epsilon-delta radius.
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hzero : rationalPart 0 = 0 := by
    simpa using rationalPart_ratCast 0
  rw [hzero]
  exact lt_of_le_of_lt (dist_rationalPart_zero_le y) hy

/-- Helper for Exercise 18.6: continuity forces the rational part to equal its input. -/
private lemma rationalPart_eq_self_of_continuousAt (x : ℝ)
    (h : ContinuousAt rationalPart x) : rationalPart x = x := by
  -- The difference from the identity is continuous at `x` and vanishes on dense rational inputs.
  have hsub : ContinuousAt (fun y : ℝ ↦ rationalPart y - y) x :=
    h.sub continuousAt_id
  have hvanish : ∀ y ∈ Set.range (fun q : ℚ ↦ (q : ℝ)), rationalPart y - y = 0 := by
    intro y hy
    obtain ⟨q, rfl⟩ := hy
    rw [rationalPart_ratCast, sub_self]
  have hzero : rationalPart x - x = 0 :=
    hsub.continuousWithinAt.eq_const_of_mem_closure (Rat.denseRange_cast x) hvanish
  exact sub_eq_zero.mp hzero

/-- Helper for Exercise 18.6: continuity forces the rational part to vanish. -/
private lemma rationalPart_eq_zero_of_continuousAt (x : ℝ)
    (h : ContinuousAt rationalPart x) : rationalPart x = 0 := by
  -- Restrict continuity to the dense irrational inputs, where `rationalPart` is identically zero.
  have hvanish : ∀ y ∈ {y : ℝ | Irrational y}, rationalPart y = 0 := by
    intro y hy
    exact rationalPart_of_not_mem_range y hy
  exact h.continuousWithinAt.eq_const_of_mem_closure (dense_irrational x) hvanish

/-- Exercise 18.6: `rationalPart` is continuous at precisely the point `0`. -/
theorem continuousAt_rationalPart_iff (x : ℝ) :
    ContinuousAt rationalPart x ↔ x = 0 := by
  constructor
  · intro h
    -- The two dense branches give the same continuous value, hence the input is zero.
    calc
      x = rationalPart x := (rationalPart_eq_self_of_continuousAt x h).symm
      _ = 0 := rationalPart_eq_zero_of_continuousAt x h
  · intro hx
    -- At the sole candidate point, use the direct metric estimate proved above.
    subst x
    exact continuousAt_rationalPart_zero
