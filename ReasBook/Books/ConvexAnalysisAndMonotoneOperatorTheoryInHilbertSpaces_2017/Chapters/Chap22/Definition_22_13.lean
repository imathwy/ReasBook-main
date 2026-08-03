import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Definition 22.13 introduces `n`-cyclic monotonicity, cyclic monotonicity, and
  maximal cyclic monotonicity for set-valued operators.
- `core/canonical`: the maximality clause is the order-theoretic owner `Maximal` specialized to the
  cyclic-monotonicity predicate.
- `bridge/view`: low-arity consequences such as ordinary monotonicity are companion theorems, not
  separate owners. -/
/-- Owner for Definition 22.13 (1): a set-valued operator on a real Hilbert space is
`n`-cyclically monotone
when `n ≥ 2` and every cyclic family of `n` graph points satisfies
`∑ i = 0, ..., n - 1, ⟪x (i + 1) - x i, u i⟫_ℝ ≤ 0`. -/
class IsNCyclicallyMonotone (A : SetValuedOperator H H) (n : ℕ) : Prop where
  /-- The cyclic-monotonicity index is at least `2`, as required in Definition 22.13. -/
  two_le : 2 ≤ n
  /-- The defining cyclic inequality for `n` graph points with `x n = x 0`. -/
  ineq :
    ∀ (x u : ℕ → H),
      (∀ i, i < n → u i ∈ A (x i)) →
      x n = x 0 →
      Finset.sum (Finset.range n) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) ≤ 0

/-- Owner for Definition 22.13 (2): a set-valued operator is cyclically monotone when it is
`n`-cyclically monotone for every integer `n ≥ 2`. -/
class IsCyclicallyMonotone (A : SetValuedOperator H H) : Prop where
  /-- Every admissible finite cycle satisfies the defining cyclic-monotonicity inequality. -/
  isNCyclicallyMonotone : ∀ ⦃n : ℕ⦄, 2 ≤ n → IsNCyclicallyMonotone A n

/-- A cyclically monotone operator is `n`-cyclically monotone for each admissible index. -/
instance instIsNCyclicallyMonotoneOfIsCyclicallyMonotone
    (A : SetValuedOperator H H) (n : ℕ) [Fact (2 ≤ n)] [hA : IsCyclicallyMonotone A] :
    IsNCyclicallyMonotone A n :=
  hA.isNCyclicallyMonotone ‹Fact (2 ≤ n)›.1

/-- Owner for Definition 22.13 (3): a set-valued operator is maximally cyclically monotone
when it is maximal, for the pointwise order on set-valued operators, among cyclically
monotone extensions. -/
abbrev IsMaximallyCyclicallyMonotone (A : SetValuedOperator H H) : Prop :=
  Maximal IsCyclicallyMonotone A

/-- A maximally cyclically monotone operator is cyclically monotone. -/
theorem Maximal.isCyclicallyMonotone
    {A : SetValuedOperator H H} (hA : Maximal IsCyclicallyMonotone A) :
    IsCyclicallyMonotone A :=
  hA.1

/-- Typeclass-friendly access to cyclic monotonicity from maximal cyclic monotonicity. -/
instance instIsCyclicallyMonotoneOfFactIsMaximallyCyclicallyMonotone
    (A : SetValuedOperator H H) [hA : Fact (IsMaximallyCyclicallyMonotone A)] :
    IsCyclicallyMonotone A :=
  Maximal.isCyclicallyMonotone hA.1

/-- Helper for Definition 22.13: the two-term cyclic sum is the negative of the usual
monotonicity pairing. -/
lemma twoCycleSum_eq_neg_monotonicityPairing
    (x₀ x₁ u₀ u₁ : H) :
    ⟪x₁ - x₀, u₀⟫_ℝ + ⟪x₀ - x₁, u₁⟫_ℝ = -⟪x₀ - x₁, u₀ - u₁⟫_ℝ := by
  -- Rewrite the first displacement as the negative of `x₀ - x₁`.
  calc
    ⟪x₁ - x₀, u₀⟫_ℝ + ⟪x₀ - x₁, u₁⟫_ℝ
        = ⟪-(x₀ - x₁), u₀⟫_ℝ + ⟪x₀ - x₁, u₁⟫_ℝ := by
            congr 1
            abel_nf
    _ = -⟪x₀ - x₁, u₀⟫_ℝ + ⟪x₀ - x₁, u₁⟫_ℝ := by
          rw [inner_neg_left]
    _ = -(⟪x₀ - x₁, u₀⟫_ℝ - ⟪x₀ - x₁, u₁⟫_ℝ) := by
          ring
    _ = -⟪x₀ - x₁, u₀ - u₁⟫_ℝ := by
          rw [inner_sub_right]

/-- Definition 22.13 (4): monotonicity and `2`-cyclic monotonicity coincide. -/
theorem isMonotone_iff_isNCyclicallyMonotone_two (A : SetValuedOperator H H) :
    A.IsMonotone ↔ IsNCyclicallyMonotone A 2 := by
  constructor
  · intro hA
    refine ⟨by decide, ?_⟩
    intro x u hu hx2
    -- Apply ordinary monotonicity to the two graph points in the cycle.
    have hpair : 0 ≤ ⟪x 0 - x 1, u 0 - u 1⟫_ℝ :=
      (SetValuedOperator.isMonotone_iff A).1 hA (hu 0 (by omega)) (hu 1 (by omega))
    -- Normalize the two-cycle sum to the negative monotonicity pairing.
    have hsum :
        Finset.sum (Finset.range 2) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) =
          -⟪x 0 - x 1, u 0 - u 1⟫_ℝ := by
      simp [Finset.sum_range_succ, hx2, twoCycleSum_eq_neg_monotonicityPairing]
    rw [hsum]
    linarith
  · intro hA
    rw [SetValuedOperator.isMonotone_iff]
    intro x u y v hxu hyv
    let xCycle : ℕ → H := fun i ↦
      if i = 0 then x else if i = 1 then y else x
    let uCycle : ℕ → H := fun i ↦ if i = 0 then u else v
    -- Feed the graph points `(x, u)` and `(y, v)` into the defining two-cycle inequality.
    have hcycle :
        Finset.sum (Finset.range 2) (fun i ↦ ⟪xCycle (i + 1) - xCycle i, uCycle i⟫_ℝ) ≤ 0 := by
      apply hA.ineq xCycle uCycle
      · intro i hi
        have hi' : i = 0 ∨ i = 1 := by
          omega
        rcases hi' with rfl | rfl
        · simpa [xCycle, uCycle] using hxu
        · simpa [xCycle, uCycle] using hyv
      · simp [xCycle]
    -- The same normalization turns the cycle inequality back into monotonicity.
    have hneg : -⟪x - y, u - v⟫_ℝ ≤ 0 := by
      simpa [xCycle, uCycle, Finset.sum_range_succ, twoCycleSum_eq_neg_monotonicityPairing] using
        hcycle
    linarith

/-- Helper for Definition 22.13: extending a cycle by a constant tail does not change its cyclic
sum. -/
lemma constantTailExtension_sum_eq
    {m n : ℕ} (hmn : m ≤ n) (x u : ℕ → H) (hxm : x m = x 0) :
    let xExt : ℕ → H := fun i ↦ if i < m then x i else x 0
    let uExt : ℕ → H := fun i ↦ if i < m then u i else u 0
    Finset.sum (Finset.range n) (fun i ↦ ⟪xExt (i + 1) - xExt i, uExt i⟫_ℝ) =
      Finset.sum (Finset.range m) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) := by
  dsimp
  let f : ℕ → ℝ := fun i ↦
    ⟪(if i + 1 < m then x (i + 1) else x 0) - (if i < m then x i else x 0),
      if i < m then u i else u 0⟫_ℝ
  have htail : Finset.sum (Finset.Ico m n) f = 0 := by
    -- Every term in the added tail is zero because both endpoints are frozen at `x 0`.
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hmi : m ≤ i := (Finset.mem_Ico.mp hi).1
    have hmi_succ : m ≤ i + 1 := by
      omega
    simp [Nat.not_lt_of_ge hmi, Nat.not_lt_of_ge hmi_succ]
  -- Split the extended `n`-sum into the original `m`-prefix and the constant tail.
  calc
    Finset.sum (Finset.range n) f
        = Finset.sum (Finset.range m) f + Finset.sum (Finset.Ico m n) f := by
            rw [← Finset.sum_range_add_sum_Ico _ hmn]
    _ = Finset.sum (Finset.range m) f := by
          rw [htail, add_zero]
    _ = Finset.sum (Finset.range m) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_lt : i < m := Finset.mem_range.mp hi
          by_cases hnext : i + 1 < m
          · simp [f, hi_lt, hnext]
          · have him : i + 1 = m := by
              omega
            simp [f, hi_lt, him, hxm]

/-- A cyclically monotone operator is monotone. -/
theorem IsCyclicallyMonotone.isMonotone
    {A : SetValuedOperator H H} (hA : IsCyclicallyMonotone A) :
    A.IsMonotone :=
  (isMonotone_iff_isNCyclicallyMonotone_two A).2 <|
    hA.isNCyclicallyMonotone (by decide)

/-- Consequence of Definition 22.13 (5): if `2 ≤ m ≤ n`, then `n`-cyclic monotonicity implies
`m`-cyclic monotonicity. -/
theorem IsNCyclicallyMonotone.of_le
    {A : SetValuedOperator H H} {m n : ℕ} (hA : IsNCyclicallyMonotone A n)
    (hm : 2 ≤ m) (hmn : m ≤ n) :
    IsNCyclicallyMonotone A m := by
  refine ⟨hm, ?_⟩
  intro x u hu hxm
  have hm_pos : 0 < m := by
    omega
  let xExt : ℕ → H := fun i ↦ if i < m then x i else x 0
  let uExt : ℕ → H := fun i ↦ if i < m then u i else u 0
  have hu0 : u 0 ∈ A (x 0) := hu 0 hm_pos
  have huExt : ∀ i, i < n → uExt i ∈ A (xExt i) := by
    intro i hi
    by_cases him : i < m
    · simpa [xExt, uExt, him] using hu i him
    · simpa [xExt, uExt, him] using hu0
  have hxExt : xExt n = xExt 0 := by
    -- The extension is frozen at `x 0` at the terminal index `n`, and also at index `0`
    -- after unfolding the `0 < m` side condition.
    simp [xExt, Nat.not_lt_of_ge hmn]
  have hineqExt :
      Finset.sum (Finset.range n) (fun i ↦ ⟪xExt (i + 1) - xExt i, uExt i⟫_ℝ) ≤ 0 :=
    hA.ineq xExt uExt huExt hxExt
  -- Replace the extended sum by the original `m`-cycle sum.
  have hsum :
      Finset.sum (Finset.range n) (fun i ↦ ⟪xExt (i + 1) - xExt i, uExt i⟫_ℝ) =
        Finset.sum (Finset.range m) (fun i ↦ ⟪x (i + 1) - x i, u i⟫_ℝ) := by
    simpa [xExt, uExt] using constantTailExtension_sum_eq hmn x u hxm
  rw [hsum] at hineqExt
  exact hineqExt

/-- Consequence of Definition 22.13 (6): a maximally monotone cyclically monotone operator is
maximally
cyclically monotone. -/
theorem isMaximallyCyclicallyMonotone_of_isMaximalMonotone
    {A : SetValuedOperator H H} (hmono : Maximal IsMonotone A) (hcyc : IsCyclicallyMonotone A) :
    IsMaximallyCyclicallyMonotone A := by
  refine ⟨hcyc, ?_⟩
  intro B hB hAB
  exact hmono.2 hB.isMonotone hAB

end SetValuedOperator
