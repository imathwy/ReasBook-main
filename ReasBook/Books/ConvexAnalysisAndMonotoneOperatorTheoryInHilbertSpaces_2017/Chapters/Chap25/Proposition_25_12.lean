import BauschkeLean.Chap22.Definition_22_13
import BauschkeLean.Chap25.Definition_25_10

open scoped BigOperators InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 25.12 states that `3`-cyclic monotonicity implies `3*`
  monotonicity for a set-valued operator.
- `core/canonical`: the Chapter 22 and Chapter 25 owners are
  `IsNCyclicallyMonotone A 3` and `A.IsThreeStarMonotone`.
- `bridge/view`: the theorem below is kept as the hypothesis-namespace implication
  `IsNCyclicallyMonotone.isThreeStarMonotone`, so downstream files can use it directly as
  `hA.isThreeStarMonotone` without introducing a duplicate wrapper theorem. -/

/-- Helper for Proposition 25.12: the defining `3`-cycle inequality specialized to fixed graph
points `(x, u)` and `(z, w)` bounds the source expression at every graph point `p`. -/
private lemma three_cycle_inequality_at_graph_point
    {A : SetValuedOperator H H} (hA : IsNCyclicallyMonotone A 3)
    {x z u w : H} (hu : u ∈ A x) (hw : w ∈ A z) :
    ∀ p : gra A, ⟪p.1.1 - x, u⟫_ℝ + ⟪z - p.1.1, p.1.2⟫_ℝ + ⟪x - z, w⟫_ℝ ≤ 0 := by
  intro p
  let xCycle : ℕ → H := fun i ↦
    if i = 0 then x else if i = 1 then p.1.1 else if i = 2 then z else x
  let uCycle : ℕ → H := fun i ↦ if i = 0 then u else if i = 1 then p.1.2 else w
  have huCycle : ∀ i, i < 3 → uCycle i ∈ A (xCycle i) := by
    intro i hi
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    rcases hi_cases with rfl | rfl | rfl
    · -- Insert the graph point `(x, u)` at the first slot of the 3-cycle.
      simpa [xCycle, uCycle] using hu
    · -- Insert the arbitrary graph point `p` at the middle slot.
      have hp : p.1.2 ∈ A p.1.1 :=
        p.property
      simpa [xCycle, uCycle] using hp
    · -- Insert the graph point `(z, w)` at the last active slot.
      simpa [xCycle, uCycle] using hw
  have hxCycle : xCycle 3 = xCycle 0 := by
    -- Close the cycle by repeating the base point `x` at index `3`.
    simp [xCycle]
  have hineq :=
    hA.ineq xCycle uCycle huCycle hxCycle
  -- Evaluate the three-term cyclic sum explicitly.
  simpa [xCycle, uCycle, Finset.sum_range_succ] using hineq

/-- Helper for Proposition 25.12: the specialized 3-cycle inequality rewrites to a uniform upper
bound on each Fitzpatrick supremand at `(z, u)`. -/
private lemma fitzpatrick_supremand_le_of_three_cycle
    {A : SetValuedOperator H H} {x z u w : H}
    (hcycle :
      ∀ p : gra A, ⟪p.1.1 - x, u⟫_ℝ + ⟪z - p.1.1, p.1.2⟫_ℝ + ⟪x - z, w⟫_ℝ ≤ 0) :
    ∀ p : gra A,
      ((⟪p.1.1, u⟫_ℝ + ⟪z, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) ≤
        ((⟪x, u⟫_ℝ - ⟪x - z, w⟫_ℝ : ℝ) : EReal) := by
  intro p
  have hrewrite :
      ⟪p.1.1 - x, u⟫_ℝ + ⟪z - p.1.1, p.1.2⟫_ℝ + ⟪x - z, w⟫_ℝ =
        (⟪p.1.1, u⟫_ℝ + ⟪z, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ) -
          (⟪x, u⟫_ℝ - ⟪x - z, w⟫_ℝ) := by
    -- Expand the two difference pairings and normalize the resulting real expression.
    rw [inner_sub_left, inner_sub_left]
    ring
  have hreal :
      ⟪p.1.1, u⟫_ℝ + ⟪z, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ ≤
        ⟪x, u⟫_ℝ - ⟪x - z, w⟫_ℝ := by
    -- Move the normalized cycle defect to the right-hand side.
    have hp_cycle := hcycle p
    rw [hrewrite] at hp_cycle
    linarith
  exact_mod_cast hreal

/-- Helper for Proposition 25.12: a finite real upper bound on every Fitzpatrick supremand at
`(z, u)` forces `(z, u)` to lie in the effective domain of `F[A]`. -/
private lemma mem_dom_fitzpatrick_of_supremand_le
    {A : SetValuedOperator H H} {z u : H} {r : ℝ}
    (hbound :
      ∀ p : gra A,
        ((⟪p.1.1, u⟫_ℝ + ⟪z, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) ≤
          (r : EReal)) :
    (z, u) ∈ ERealFunction.dom (F[A]) := by
  rw [ERealFunction.mem_dom_iff, fitzpatrickFunction]
  -- Bound the supremum defining `F[A] (z, u)` by the same finite real constant.
  exact lt_of_le_of_lt (iSup_le hbound) (EReal.coe_lt_top r)

/-- Proposition 25.12: every `3`-cyclically monotone set-valued operator is `3*` monotone. -/
theorem IsNCyclicallyMonotone.isThreeStarMonotone
    {A : SetValuedOperator H H} (hA : IsNCyclicallyMonotone A 3) :
    A.IsThreeStarMonotone := by
  rw [isThreeStarMonotone_iff]
  rintro ⟨z, u⟩ ⟨hz_dom, hu_range⟩
  rcases (SetValuedOperator.mem_dom_iff A z).1 hz_dom with ⟨w, hw⟩
  rcases (SetValuedOperator.mem_range_iff A u).1 hu_range with ⟨x, hu⟩
  -- Follow the source proof: fix graph witnesses for `z ∈ dom A` and `u ∈ range A`.
  have hcycle :
      ∀ p : gra A, ⟪p.1.1 - x, u⟫_ℝ + ⟪z - p.1.1, p.1.2⟫_ℝ + ⟪x - z, w⟫_ℝ ≤ 0 :=
    three_cycle_inequality_at_graph_point (A := A) hA hu hw
  -- Convert the cycle inequality into a uniform finite upper bound on the Fitzpatrick supremand.
  refine mem_dom_fitzpatrick_of_supremand_le (A := A) (z := z) (u := u)
    (r := ⟪x, u⟫_ℝ - ⟪x - z, w⟫_ℝ) ?_
  intro p
  exact fitzpatrick_supremand_le_of_three_cycle (x := x) (z := z) (u := u) (w := w) hcycle p

end SetValuedOperator
