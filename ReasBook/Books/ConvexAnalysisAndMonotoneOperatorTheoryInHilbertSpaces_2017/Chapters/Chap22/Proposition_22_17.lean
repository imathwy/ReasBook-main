import BauschkeLean.Chap22.Definition_22_13
import BauschkeLean.Chap22.Definition_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 22.17: vanishing of the monotonicity pairing is preserved when the two
graph points are swapped. -/
private lemma zero_pairing_symm {x y u v : H}
    (hzero : ⟪x - y, u - v⟫_ℝ = 0) :
    ⟪y - x, v - u⟫_ℝ = 0 := by
  -- Rewrite both differences as negatives of the original ones.
  have hxy : y - x = -(x - y) := by
    abel_nf
  have hvu : v - u = -(u - v) := by
    abel_nf
  rw [hxy, hvu, inner_neg_left, inner_neg_right]
  simpa using hzero

/-- Helper for Proposition 22.17: under the vanishing-pairing hypothesis, the three-cycle sum from
the source proof is exactly the negative swapped monotonicity pairing. -/
private lemma three_cycle_sum_eq_neg_swapped_value_pairing {x y z u v w : H}
    (hzero : ⟪x - y, u - v⟫_ℝ = 0) :
    ⟪y - x, u⟫_ℝ + ⟪z - y, v⟫_ℝ + ⟪x - z, w⟫_ℝ = -⟪x - z, v - w⟫_ℝ := by
  -- First isolate the equality of the two pairings against `u` and `v`.
  have hzero' : ⟪x - y, u⟫_ℝ = ⟪x - y, v⟫_ℝ := by
    rw [inner_sub_right] at hzero
    linarith
  have hyx : y - x = -(x - y) := by
    abel_nf
  have hzx : z - x = -(x - z) := by
    abel_nf
  have hpair : -⟪x - y, v⟫_ℝ + ⟪z - y, v⟫_ℝ = ⟪z - x, v⟫_ℝ := by
    -- Collapse the two `v`-pairings into the single displacement `z - x`.
    have hxy_pair : ⟪x - y, v⟫_ℝ = ⟪x, v⟫_ℝ - ⟪y, v⟫_ℝ := by
      rw [inner_sub_left]
    have hzy_pair : ⟪z - y, v⟫_ℝ = ⟪z, v⟫_ℝ - ⟪y, v⟫_ℝ := by
      rw [inner_sub_left]
    calc
      -⟪x - y, v⟫_ℝ + ⟪z - y, v⟫_ℝ
          = -(⟪x, v⟫_ℝ - ⟪y, v⟫_ℝ) + (⟪z, v⟫_ℝ - ⟪y, v⟫_ℝ) := by
              rw [hxy_pair, hzy_pair]
      _ = ⟪z, v⟫_ℝ - ⟪x, v⟫_ℝ := by
            ring
      _ = ⟪z - x, v⟫_ℝ := by
        rw [inner_sub_left]
  -- Normalize the source sum until only the swapped pairing remains.
  calc
    ⟪y - x, u⟫_ℝ + ⟪z - y, v⟫_ℝ + ⟪x - z, w⟫_ℝ
        = -⟪x - y, u⟫_ℝ + ⟪z - y, v⟫_ℝ + ⟪x - z, w⟫_ℝ := by
            rw [hyx, inner_neg_left]
    _ = -⟪x - y, v⟫_ℝ + ⟪z - y, v⟫_ℝ + ⟪x - z, w⟫_ℝ := by
          rw [hzero']
    _ = ⟪z - x, v⟫_ℝ + ⟪x - z, w⟫_ℝ := by
          rw [hpair]
    _ = -⟪x - z, v⟫_ℝ + ⟪x - z, w⟫_ℝ := by
          rw [hzx, inner_neg_left]
    _ = -⟪x - z, v - w⟫_ℝ := by
          rw [inner_sub_right]
          ring

/-- Helper for Proposition 22.17: if a `3`-cycle starts from two graph points whose monotonicity
pairing vanishes, then the swapped candidate `(x, v)` is monotonically related to every graph
point of `A`. -/
private lemma swapped_value_monotone_related_of_three_cyclic_zero_pairing
    {A : SetValuedOperator H H} (hcyc : IsNCyclicallyMonotone A 3)
    {x y u v : H} (hu : u ∈ A x) (hv : v ∈ A y)
    (hzero : ⟪x - y, u - v⟫_ℝ = 0) :
    ∀ ⦃z w : H⦄, w ∈ A z → 0 ≤ ⟪x - z, v - w⟫_ℝ := by
  intro z w hw
  let xCycle : ℕ → H := fun i ↦
    if i = 0 then x else if i = 1 then y else if i = 2 then z else x
  let uCycle : ℕ → H := fun i ↦ if i = 0 then u else if i = 1 then v else w
  -- Feed the concrete three-cycle `(x, u), (y, v), (z, w), (x, -)` into cyclic monotonicity.
  have hcycle :
      Finset.sum (Finset.range 3) (fun i ↦ ⟪xCycle (i + 1) - xCycle i, uCycle i⟫_ℝ) ≤ 0 := by
    apply hcyc.ineq xCycle uCycle
    · intro i hi
      have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
        omega
      rcases hi_cases with rfl | rfl | rfl
      · simpa [xCycle, uCycle] using hu
      · simpa [xCycle, uCycle] using hv
      · simpa [xCycle, uCycle] using hw
    · simp [xCycle]
  -- Expand the three-term sum and rewrite it with the source algebraic identity.
  have hsum :
      Finset.sum (Finset.range 3) (fun i ↦ ⟪xCycle (i + 1) - xCycle i, uCycle i⟫_ℝ) =
        -⟪x - z, v - w⟫_ℝ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [xCycle, uCycle, three_cycle_sum_eq_neg_swapped_value_pairing, hzero]
  have hneg : -⟪x - z, v - w⟫_ℝ ≤ 0 := by
    rw [hsum] at hcycle
    exact hcycle
  linarith

/-- Helper for Proposition 22.17: maximal monotonicity converts the universal monotonicity
relation for the swapped candidate `(x, v)` into graph membership. -/
private lemma swapped_value_mem_of_three_cyclic_zero_pairing
    {A : SetValuedOperator H H} (hcyc : IsNCyclicallyMonotone A 3)
    (hmax : Maximal IsMonotone A)
    {x y u v : H} (hu : u ∈ A x) (hv : v ∈ A y)
    (hzero : ⟪x - y, u - v⟫_ℝ = 0) :
    v ∈ A x := by
  -- The previous helper verifies the Minty relation required by `Maximal.mem_iff`.
  refine (SetValuedOperator.Maximal.mem_iff hmax x v).2 ?_
  intro z w hw
  exact swapped_value_monotone_related_of_three_cyclic_zero_pairing hcyc hu hv hzero hw

-- Semantic recall: `lean_leansearch` did not return a matching canonical theorem for this
-- implication. The Chapter 22 owner for `3`-cyclic monotonicity is
-- `SetValuedOperator.IsNCyclicallyMonotone A 3`, so this proposition uses that canonical
-- hypothesis together with the Chapter 22/20 owners `IsParamonotone` and `Maximal IsMonotone`.
/-- Proposition 22.17: if `A : H → 2^H` is `3`-cyclically monotone and maximally monotone, then
`A` is paramonotone. -/
theorem isParamonotone_of_isThreeCyclicallyMonotone_of_isMaximalMonotone
    {A : SetValuedOperator H H}
    (hcyc : IsNCyclicallyMonotone A 3)
    (hmax : Maximal IsMonotone A) :
    A.IsParamonotone := by
  refine ⟨hmax.1, ?_⟩
  intro x u y v hu hv hzero
  -- Apply the source argument once to obtain membership of the swapped pair `(x, v)`.
  have hvx : v ∈ A x :=
    swapped_value_mem_of_three_cyclic_zero_pairing hcyc hmax hu hv hzero
  -- Reuse the same argument with the two graph points exchanged to get `(y, u)`.
  have huy : u ∈ A y :=
    swapped_value_mem_of_three_cyclic_zero_pairing
      (x := y) (y := x) (u := v) (v := u) hcyc hmax hv hu (zero_pairing_symm hzero)
  exact ⟨hvx, huy⟩

end SetValuedOperator
