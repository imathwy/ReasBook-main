import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Lemma 4.21: if `x ∈ [0, 1)`, then `⌊N * x⌋` is one of the `N` bucket indices
`0, …, N - 1`. -/
lemma fractional_bucket_lt {N : ℕ} (hN : 0 < N) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ⌊(N : ℝ) * x⌋₊ < N := by
  have hN_real : (0 : ℝ) < N := by
    exact_mod_cast hN
  -- The source proof partitions `[0, 1)` into `N` half-open intervals of width `1 / N`.
  have hNx0 : 0 ≤ (N : ℝ) * x := by
    exact mul_nonneg hN_real.le hx0
  have hNx1 : (N : ℝ) * x < N := by
    simpa using mul_lt_mul_of_pos_left hx1 hN_real
  -- Taking the natural floor records which interval contains `x`.
  exact (Nat.floor_lt hNx0).2 hNx1

/-- Helper for Lemma 4.21: among the `N + 1` fractional parts `fract(i * α)`, two fall in the
same bucket of the partition of `[0, 1)` into `N` intervals. -/
lemma exists_distinct_indices_same_fractional_bucket (α : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ i ∈ Finset.range (N + 1), ∃ j ∈ Finset.range (N + 1), i ≠ j ∧
      ⌊(N : ℝ) * Int.fract ((i : ℝ) * α)⌋₊ = ⌊(N : ℝ) * Int.fract ((j : ℝ) * α)⌋₊ := by
  classical
  let bucket : ℕ → ℕ := fun i ↦ ⌊(N : ℝ) * Int.fract ((i : ℝ) * α)⌋₊
  have hmaps : Set.MapsTo bucket (Finset.range (N + 1)) (Finset.range N) := by
    intro i hi
    -- Each fractional part lies in `[0, 1)`, so its bucket index lies in `range N`.
    rw [Finset.mem_coe, Finset.mem_range]
    exact fractional_bucket_lt hN (Int.fract_nonneg _) (Int.fract_lt_one _)
  -- The pigeonhole principle now produces two distinct indices with the same bucket.
  obtain ⟨i, hi, j, hj, hij, hEq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (N + 1))
      (t := Finset.range N)
      (by simp [Finset.card_range])
      hmaps
  dsimp [bucket] at hEq
  exact ⟨i, hi, j, hj, hij, hEq⟩

/-- Helper for Lemma 4.21: points of `[0, 1)` with the same `⌊N * -⌋` bucket differ by less than
`1 / N`. -/
lemma abs_sub_lt_inv_of_same_bucket {N : ℕ} (hN : 0 < N) {x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : ⌊(N : ℝ) * x⌋₊ = ⌊(N : ℝ) * y⌋₊) :
    |x - y| < (1 : ℝ) / N := by
  have hN_real : (0 : ℝ) < N := by
    exact_mod_cast hN
  let k : ℕ := ⌊(N : ℝ) * x⌋₊
  have hNx0 : 0 ≤ (N : ℝ) * x := by
    exact mul_nonneg hN_real.le hx0
  have hNy0 : 0 ≤ (N : ℝ) * y := by
    exact mul_nonneg hN_real.le hy0
  have hkx : (k : ℝ) ≤ (N : ℝ) * x ∧ (N : ℝ) * x < k + 1 := by
    -- Expanding the bucket equality locates `x` in one half-open interval.
    exact (Nat.floor_eq_iff hNx0).1 (by simp [k])
  have hky : (k : ℝ) ≤ (N : ℝ) * y ∧ (N : ℝ) * y < k + 1 := by
    -- The same bucket equality puts `y` in the same interval.
    exact (Nat.floor_eq_iff hNy0).1 (by simpa [k] using hxy.symm)
  -- Two points in the same interval of width `1 / N` differ by less than `1 / N`.
  have hxy_scaled : (N : ℝ) * x - (N : ℝ) * y < 1 := by
    nlinarith [hkx.2, hky.1]
  have hyx_scaled : (N : ℝ) * y - (N : ℝ) * x < 1 := by
    nlinarith [hky.2, hkx.1]
  have hxy_lt : x - y < (1 : ℝ) / N := by
    rw [lt_div_iff₀ hN_real]
    simpa [sub_mul, mul_comm, mul_left_comm, mul_assoc] using hxy_scaled
  have hyx_lt : y - x < (1 : ℝ) / N := by
    rw [lt_div_iff₀ hN_real]
    simpa [sub_mul, mul_comm, mul_left_comm, mul_assoc] using hyx_scaled
  exact abs_sub_lt_iff.2 ⟨hxy_lt, hyx_lt⟩

/-- Helper for Lemma 4.21: subtracting integer floors rewrites a difference as a difference of
fractional parts. -/
lemma sub_sub_int_floor_sub_eq_fract_sub_fract (x y : ℝ) :
    (x - y) - ((((⌊x⌋ : ℤ) - ⌊y⌋ : ℤ) : ℝ)) = Int.fract x - Int.fract y := by
  -- This is the algebraic bridge from the source proof's floor choice to fractional parts.
  rw [Int.cast_sub]
  simp only [Int.fract, sub_eq_add_neg]
  ring

/-- Helper for Lemma 4.21: once two indices have the same fractional bucket, their difference
produces the desired integer approximation. -/
lemma exists_integer_approximation_of_same_fractional_bucket (α : ℝ) {N i j : ℕ} (hN : 0 < N)
    (hj : j ∈ Finset.range (N + 1)) (hij : i < j)
    (hbucket : ⌊(N : ℝ) * Int.fract ((i : ℝ) * α)⌋₊ = ⌊(N : ℝ) * Int.fract ((j : ℝ) * α)⌋₊) :
    ∃ n m : ℤ,
      1 ≤ n ∧ n ≤ (N : ℤ) ∧ |(n : ℝ) * α - (m : ℝ)| < (1 : ℝ) / N := by
  let n : ℤ := (j : ℤ) - i
  let m : ℤ := ⌊(j : ℝ) * α⌋ - ⌊(i : ℝ) * α⌋
  have hj_le : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hij_int : (i : ℤ) < j := by
    exact_mod_cast hij
  have hi_nonneg : (0 : ℤ) ≤ i := by
    exact_mod_cast Nat.zero_le i
  have hj_le_int : (j : ℤ) ≤ N := by
    exact_mod_cast hj_le
  have hn_pos : 1 ≤ n := by
    -- Since `i < j`, their integer difference is at least `1`.
    dsimp [n]
    linarith
  have hn_le : n ≤ (N : ℤ) := by
    -- Since `j ≤ N` and `i ≥ 0`, the difference is at most `N`.
    dsimp [n]
    linarith
  have hfract :
      |Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α)| < (1 : ℝ) / N := by
    -- Equal buckets force the two fractional parts to lie within one interval of width `1 / N`.
    exact abs_sub_lt_inv_of_same_bucket hN (Int.fract_nonneg _) (Int.fract_nonneg _) hbucket.symm
  have hrewrite :
      (n : ℝ) * α - (m : ℝ) = Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α) := by
    -- Rewrite the chosen integers `n, m` into the source proof's difference of fractional parts.
    calc
      (n : ℝ) * α - (m : ℝ)
          = ((((j : ℝ) - i) * α) -
              ((((⌊(j : ℝ) * α⌋ : ℤ) - ⌊(i : ℝ) * α⌋ : ℤ) : ℝ))) := by
              simp [n, m]
      _ = ((((j : ℝ) * α) - ((i : ℝ) * α)) -
            ((((⌊(j : ℝ) * α⌋ : ℤ) - ⌊(i : ℝ) * α⌋ : ℤ) : ℝ))) := by
            ring
      _ = Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α) := by
            simpa using
              sub_sub_int_floor_sub_eq_fract_sub_fract ((j : ℝ) * α) ((i : ℝ) * α)
  refine ⟨n, m, hn_pos, hn_le, ?_⟩
  -- The final estimate is exactly the same-bucket bound after the floor/fract rewrite.
  simpa [hrewrite] using hfract

/-- Lemma 4.21 (Dirichlet's Approximation Theorem): for any real number `α` and positive
integer `N`, there are integers `n, m` with `1 ≤ n ≤ N` and `|n * α - m| < 1 / N`. -/
theorem dirichlet_approximation_theorem
    (α : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ n m : ℤ,
      1 ≤ n ∧ n ≤ (N : ℤ) ∧ |(n : ℝ) * α - (m : ℝ)| < (1 : ℝ) / N := by
  obtain ⟨i, hi, j, hj, hij_ne, hbucket⟩ :=
    exists_distinct_indices_same_fractional_bucket α hN
  -- Reorder the colliding indices so that their difference is a positive integer.
  rcases lt_or_gt_of_ne hij_ne with hij | hji
  · exact exists_integer_approximation_of_same_fractional_bucket α hN hj hij hbucket
  · exact exists_integer_approximation_of_same_fractional_bucket α hN hi hji hbucket.symm
