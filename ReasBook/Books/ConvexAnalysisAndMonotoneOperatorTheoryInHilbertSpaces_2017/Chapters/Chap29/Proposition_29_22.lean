import BauschkeLean.Chap29.Example_29_20
import BauschkeLean.Chap29.Example_29_21

open scoped InnerProductSpace

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` only surfaced generic halfspace/intersection owners, while
-- the verified Chapter 29 source-facing API for this item is the pair of owners
-- `innerProductClosedSublevelSet` and `innerProductStrip` from Examples 29.20 and 29.21.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (u₁ u₂ : H) (η₁ η₂ : ℝ)

local notation "C" =>
  innerProductClosedSublevelSet u₁ η₁ ∩ innerProductClosedSublevelSet u₂ η₂

local notation "Case1" =>
  u₁ = 0 ∧ u₂ = 0 ∧ 0 ≤ min η₁ η₂

local notation "Case2" =>
  u₁ = 0 ∧ u₂ = 0 ∧ min η₁ η₂ < 0

local notation "Case3" =>
  u₁ ≠ 0 ∧ u₂ = 0 ∧ 0 ≤ η₂

local notation "Case4" =>
  u₁ ≠ 0 ∧ u₂ = 0 ∧ η₂ < 0

local notation "Case5" =>
  u₁ = 0 ∧ u₂ ≠ 0 ∧ 0 ≤ η₁

local notation "Case6" =>
  u₁ = 0 ∧ u₂ ≠ 0 ∧ η₁ < 0

local notation "Case7" =>
  u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ 0 < ⟪u₁, u₂⟫_ℝ

local notation "Case8" =>
  u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ ⟪u₁, u₂⟫_ℝ < 0 ∧ η₁ * ‖u₂‖ + η₂ * ‖u₁‖ < 0

local notation "Case9" =>
  u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ ⟪u₁, u₂⟫_ℝ < 0 ∧ 0 ≤ η₁ * ‖u₂‖ + η₂ * ‖u₁‖

section Helpers

variable {u₁ u₂ : H} {η₁ η₂ : ℝ}

/-- Helper for Proposition 29.22: the squared Cauchy--Schwarz equality implies the unsquared
equality `|⟪u₁, u₂⟫_ℝ| = ‖u₁‖ * ‖u₂‖`. -/
theorem absRealInner_eq_norm_mul_of_cauchySchwarzEq
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2) :
    |⟪u₁, u₂⟫_ℝ| = ‖u₁‖ * ‖u₂‖ := by
  have hnonneg : 0 ≤ ‖u₁‖ * ‖u₂‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hdep' : (‖u₁‖ * ‖u₂‖) ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hdep
  -- The norm product is already the Cauchy--Schwarz upper bound, so equality of squares forces
  -- equality itself.
  calc
    |⟪u₁, u₂⟫_ℝ| = Real.sqrt (|⟪u₁, u₂⟫_ℝ| ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
    _ = Real.sqrt ((‖u₁‖ * ‖u₂‖) ^ 2) := by
      rw [← hdep']
    _ = ‖u₁‖ * ‖u₂‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

/-- Helper for Proposition 29.22: in the positive-inner-product equality case, the two normals
point in the same direction. -/
theorem normSmul_eq_normSmul_of_cauchySchwarzEq_of_inner_pos
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (_hu₁ : u₁ ≠ 0) (_hu₂ : u₂ ≠ 0) (hinner : 0 < ⟪u₁, u₂⟫_ℝ) :
    ‖u₂‖ • u₁ = ‖u₁‖ • u₂ := by
  have habs : |⟪u₁, u₂⟫_ℝ| = ‖u₁‖ * ‖u₂‖ :=
    absRealInner_eq_norm_mul_of_cauchySchwarzEq hdep
  have hEq : ⟪u₁, u₂⟫_ℝ = ‖u₁‖ * ‖u₂‖ := by
    -- Positive sign removes the absolute value from the equality case.
    rw [abs_of_pos hinner] at habs
    exact habs
  exact (inner_eq_norm_mul_iff_real).1 hEq

/-- Helper for Proposition 29.22: in the negative-inner-product equality case, the two normals
point in opposite directions. -/
theorem normSmul_eq_negNormSmul_of_cauchySchwarzEq_of_inner_neg
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (_hu₁ : u₁ ≠ 0) (_hu₂ : u₂ ≠ 0) (hinner : ⟪u₁, u₂⟫_ℝ < 0) :
    ‖u₂‖ • u₁ = - (‖u₁‖ • u₂) := by
  have habs : |⟪u₁, u₂⟫_ℝ| = ‖u₁‖ * ‖u₂‖ :=
    absRealInner_eq_norm_mul_of_cauchySchwarzEq hdep
  have hEq : ⟪u₁, -u₂⟫_ℝ = ‖u₁‖ * ‖-u₂‖ := by
    -- Passing to `-u₂` turns the negative inner product into the positive equality case.
    calc
      ⟪u₁, -u₂⟫_ℝ = -⟪u₁, u₂⟫_ℝ := by
        rw [inner_neg_right]
      _ = |⟪u₁, u₂⟫_ℝ| := by
        rw [abs_of_neg hinner]
      _ = ‖u₁‖ * ‖u₂‖ := habs
      _ = ‖u₁‖ * ‖-u₂‖ := by
        rw [norm_neg]
  have hsmul : ‖-u₂‖ • u₁ = ‖u₁‖ • (-u₂) := (inner_eq_norm_mul_iff_real).1 hEq
  simpa [norm_neg, neg_smul] using hsmul

/-- Helper for Proposition 29.22: in the positive-inner-product equality case, the intersection of
the two dependent halfspaces is a single halfspace with normal `‖u₂‖ • u₁`. -/
theorem innerProductClosedSublevelSetInter_eq_halfspace_of_cauchySchwarzEq_of_inner_pos
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hinner : 0 < ⟪u₁, u₂⟫_ℝ) :
    innerProductClosedSublevelSet u₁ η₁ ∩ innerProductClosedSublevelSet u₂ η₂ =
      innerProductClosedSublevelSet (‖u₂‖ • u₁) (min (η₁ * ‖u₂‖) (η₂ * ‖u₁‖)) := by
  have hnorm₁_pos : 0 < ‖u₁‖ := norm_pos_iff.mpr hu₁
  have hnorm₂_pos : 0 < ‖u₂‖ := norm_pos_iff.mpr hu₂
  have hdir :
      ‖u₂‖ • u₁ = ‖u₁‖ • u₂ :=
    normSmul_eq_normSmul_of_cauchySchwarzEq_of_inner_pos hdep hu₁ hu₂ hinner
  have hinner_left (x : H) :
      ⟪x, ‖u₂‖ • u₁⟫_ℝ = ‖u₂‖ * ⟪x, u₁⟫_ℝ := by
    rw [real_inner_smul_right]
  have hinner_right (x : H) :
      ⟪x, ‖u₂‖ • u₁⟫_ℝ = ‖u₁‖ * ⟪x, u₂⟫_ℝ := by
    calc
      ⟪x, ‖u₂‖ • u₁⟫_ℝ = ⟪x, ‖u₁‖ • u₂⟫_ℝ := by
        rw [hdir]
      _ = ‖u₁‖ * ⟪x, u₂⟫_ℝ := by
        rw [real_inner_smul_right]
  ext x
  simp only [Set.mem_inter_iff, mem_innerProductClosedSublevelSet_iff]
  constructor
  · rintro ⟨hx₁, hx₂⟩
    refine le_min ?_ ?_
    · have hx₁' : ‖u₂‖ * ⟪x, u₁⟫_ℝ ≤ ‖u₂‖ * η₁ :=
        mul_le_mul_of_nonneg_left hx₁ hnorm₂_pos.le
      simpa [hinner_left x, mul_comm, mul_left_comm, mul_assoc] using hx₁'
    · have hx₂' : ‖u₁‖ * ⟪x, u₂⟫_ℝ ≤ ‖u₁‖ * η₂ :=
        mul_le_mul_of_nonneg_left hx₂ hnorm₁_pos.le
      simpa [hinner_right x, mul_comm, mul_left_comm, mul_assoc] using hx₂'
  · intro hx
    refine ⟨?_, ?_⟩
    · have hx₁' : ⟪x, ‖u₂‖ • u₁⟫_ℝ ≤ η₁ * ‖u₂‖ := le_trans hx (min_le_left _ _)
      have hx₁'' : ‖u₂‖ * ⟪x, u₁⟫_ℝ ≤ ‖u₂‖ * η₁ := by
        simpa [hinner_left x, mul_comm, mul_left_comm, mul_assoc] using hx₁'
      nlinarith [hx₁'', hnorm₂_pos]
    · have hx₂' : ⟪x, ‖u₂‖ • u₁⟫_ℝ ≤ η₂ * ‖u₁‖ := le_trans hx (min_le_right _ _)
      have hx₂'' : ‖u₁‖ * ⟪x, u₂⟫_ℝ ≤ ‖u₁‖ * η₂ := by
        simpa [hinner_right x, mul_comm, mul_left_comm, mul_assoc] using hx₂'
      nlinarith [hx₂'', hnorm₁_pos]

/-- Helper for Proposition 29.22: in the negative-inner-product equality case, the intersection of
the two dependent halfspaces is a strip with normal `‖u₂‖ • u₁`. -/
theorem innerProductClosedSublevelSetInter_eq_strip_of_cauchySchwarzEq_of_inner_neg
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hinner : ⟪u₁, u₂⟫_ℝ < 0) :
    innerProductClosedSublevelSet u₁ η₁ ∩ innerProductClosedSublevelSet u₂ η₂ =
      innerProductStrip (‖u₂‖ • u₁) (-η₂ * ‖u₁‖) (η₁ * ‖u₂‖) := by
  have hnorm₁_pos : 0 < ‖u₁‖ := norm_pos_iff.mpr hu₁
  have hnorm₂_pos : 0 < ‖u₂‖ := norm_pos_iff.mpr hu₂
  have hdir :
      ‖u₂‖ • u₁ = - (‖u₁‖ • u₂) :=
    normSmul_eq_negNormSmul_of_cauchySchwarzEq_of_inner_neg hdep hu₁ hu₂ hinner
  have hinner_left (x : H) :
      ⟪x, ‖u₂‖ • u₁⟫_ℝ = ‖u₂‖ * ⟪x, u₁⟫_ℝ := by
    rw [real_inner_smul_right]
  have hinner_right (x : H) :
      ⟪x, ‖u₂‖ • u₁⟫_ℝ = -(‖u₁‖ * ⟪x, u₂⟫_ℝ) := by
    calc
      ⟪x, ‖u₂‖ • u₁⟫_ℝ = ⟪x, -(‖u₁‖ • u₂)⟫_ℝ := by
        rw [hdir]
      _ = -⟪x, ‖u₁‖ • u₂⟫_ℝ := by
        rw [inner_neg_right]
      _ = -(‖u₁‖ * ⟪x, u₂⟫_ℝ) := by
        rw [real_inner_smul_right]
  ext x
  simp only [Set.mem_inter_iff, mem_innerProductClosedSublevelSet_iff, mem_innerProductStrip_iff]
  constructor
  · rintro ⟨hx₁, hx₂⟩
    refine ⟨?_, ?_⟩
    · have hx₂' : ‖u₁‖ * ⟪x, u₂⟫_ℝ ≤ ‖u₁‖ * η₂ :=
        mul_le_mul_of_nonneg_left hx₂ hnorm₁_pos.le
      calc
        -η₂ * ‖u₁‖ = -(‖u₁‖ * η₂) := by
          ring
        _ ≤ -(‖u₁‖ * ⟪x, u₂⟫_ℝ) := by
          exact neg_le_neg hx₂'
        _ = ⟪x, ‖u₂‖ • u₁⟫_ℝ := by
          rw [hinner_right x]
    · have hx₁' : ‖u₂‖ * ⟪x, u₁⟫_ℝ ≤ ‖u₂‖ * η₁ :=
        mul_le_mul_of_nonneg_left hx₁ hnorm₂_pos.le
      simpa [hinner_left x, mul_comm, mul_left_comm, mul_assoc] using hx₁'
  · rintro ⟨hx₁, hx₂⟩
    refine ⟨?_, ?_⟩
    · have hx₁' : ‖u₂‖ * ⟪x, u₁⟫_ℝ ≤ ‖u₂‖ * η₁ := by
        simpa [hinner_left x, mul_comm, mul_left_comm, mul_assoc] using hx₂
      nlinarith [hx₁', hnorm₂_pos]
    · have hx₂' : ‖u₁‖ * ⟪x, u₂⟫_ℝ ≤ ‖u₁‖ * η₂ :=
        neg_le_neg_iff.mp <| by
          simpa [hinner_right x, mul_comm, mul_left_comm, mul_assoc] using hx₁
      nlinarith [hx₂', hnorm₁_pos]

end Helpers

/-- Proposition 29.22: under the equality case
`‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2` of the Cauchy--Schwarz inequality, exactly one of the
nine source case hypotheses `(i)`--`(ix)` occurs for
`C = {x | ⟪x, u₁⟫_ℝ ≤ η₁} ∩ {x | ⟪x, u₂⟫_ℝ ≤ η₂}`; the numbered theorems below record the
corresponding conclusion in each case. -/
theorem innerProductClosedSublevelSetInter_case_partition_of_cauchySchwarz_eq
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2) :
    Xor' Case1
      (Xor' Case2
        (Xor' Case3
          (Xor' Case4
            (Xor' Case5
              (Xor' Case6
                (Xor' Case7
                  (Xor' Case8 Case9))))))) := by
  by_cases hu₁_zero : u₁ = 0
  · by_cases hu₂_zero : u₂ = 0
    · by_cases hη : 0 ≤ min η₁ η₂
      · -- When both normals vanish and the minimum level is nonnegative, only Case (i) survives.
        simpa [Xor', hu₁_zero, hu₂_zero, hη, not_lt_of_ge hη]
      · have hη' : min η₁ η₂ < 0 := lt_of_not_ge hη
        -- The complementary zero-normal branch is exactly Case (ii).
        simpa [Xor', hu₁_zero, hu₂_zero, hη', not_le_of_gt hη']
    · have hu₂_ne : u₂ ≠ 0 := hu₂_zero
      by_cases hη₁ : 0 ≤ η₁
      · -- With `u₁ = 0` and `u₂ ≠ 0`, feasibility is decided solely by the left scalar level.
        simpa [Xor', hu₁_zero, hu₂_ne, hη₁, not_lt_of_ge hη₁]
      · have hη₁' : η₁ < 0 := lt_of_not_ge hη₁
        simpa [Xor', hu₁_zero, hu₂_ne, hη₁', not_le_of_gt hη₁']
  · have hu₁_ne : u₁ ≠ 0 := hu₁_zero
    by_cases hu₂_zero : u₂ = 0
    · by_cases hη₂ : 0 ≤ η₂
      · -- With `u₁ ≠ 0` and `u₂ = 0`, feasibility is decided solely by the right scalar level.
        simpa [Xor', hu₁_ne, hu₂_zero, hη₂, not_lt_of_ge hη₂]
      · have hη₂' : η₂ < 0 := lt_of_not_ge hη₂
        simpa [Xor', hu₁_ne, hu₂_zero, hη₂', not_le_of_gt hη₂']
    · have hu₂_ne : u₂ ≠ 0 := hu₂_zero
      have habs :
          |⟪u₁, u₂⟫_ℝ| = ‖u₁‖ * ‖u₂‖ :=
        absRealInner_eq_norm_mul_of_cauchySchwarzEq hdep
      have hinner_ne : ⟪u₁, u₂⟫_ℝ ≠ 0 := by
        intro hzero
        have hnorm_pos : 0 < ‖u₁‖ * ‖u₂‖ :=
          mul_pos (norm_pos_iff.mpr hu₁_ne) (norm_pos_iff.mpr hu₂_ne)
        rw [hzero, abs_zero] at habs
        linarith
      rcases lt_or_gt_of_ne hinner_ne with hinner | hinner
      · by_cases hη : 0 ≤ η₁ * ‖u₂‖ + η₂ * ‖u₁‖
        · -- In the negative-inner branch, the remaining split is the strip feasibility inequality.
          simpa [Xor', hu₁_ne, hu₂_ne, hinner, hinner.le, hη, not_lt_of_ge hη]
        · have hη' : η₁ * ‖u₂‖ + η₂ * ‖u₁‖ < 0 := lt_of_not_ge hη
          simpa [Xor', hu₁_ne, hu₂_ne, hinner, hinner.le, hη', not_le_of_gt hη']
      · -- Positive inner product puts the intersection in the halfspace branch.
        simpa [Xor', hu₁_ne, hu₂_ne, hinner, not_lt_of_gt hinner]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {u₁ u₂ : H} {η₁ η₂ : ℝ}

local notation "C" =>
  innerProductClosedSublevelSet u₁ η₁ ∩ innerProductClosedSublevelSet u₂ η₂

/-- In the feasible `u₁ = u₂ = 0` case, the intersection `(29.21)` is Chebyshev because it is the
whole space. -/
theorem innerProductClosedSublevelSetInter_isChebyshev_of_eq_zero_of_eq_zero_of_nonneg_min
    (hu₁ : u₁ = 0) (hu₂ : u₂ = 0) (hη : 0 ≤ min η₁ η₂) :
    IsChebyshev C := by
  have hη₁ : 0 ≤ η₁ := le_trans hη (min_le_left _ _)
  have hη₂ : 0 ≤ η₂ := le_trans hη (min_le_right _ _)
  have hC_eq : C = Set.univ := by
    -- Both halfspaces become the whole space once the zero-normal inequalities are feasible.
    rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₁ hη₁]
    rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₂ hη₂]
    simp
  rw [hC_eq]
  exact isChebyshev_of_nonempty_isClosed_convex ⟨0, Set.mem_univ 0⟩ isClosed_univ convex_univ

/-- In the case `u₁ ≠ 0`, `u₂ = 0`, and `0 ≤ η₂`, the intersection `(29.21)` is Chebyshev because
it reduces to the left halfspace from Example 29.20. -/
theorem innerProductClosedSublevelSetInter_isChebyshev_of_left_ne_zero_of_right_eq_zero_of_nonneg
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ = 0) (hη₂ : 0 ≤ η₂) :
    IsChebyshev C := by
  -- The zero right factor is `univ`, so the intersection is exactly the left halfspace.
  rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₂ hη₂, Set.inter_univ]
  exact innerProductClosedSublevelSet_isChebyshev_of_ne_zero hu₁

/-- In the case `u₁ = 0`, `u₂ ≠ 0`, and `0 ≤ η₁`, the intersection `(29.21)` is Chebyshev because
it reduces to the right halfspace from Example 29.20. -/
theorem innerProductClosedSublevelSetInter_isChebyshev_of_left_eq_zero_of_right_ne_zero_of_nonneg
    (hu₁ : u₁ = 0) (hu₂ : u₂ ≠ 0) (hη₁ : 0 ≤ η₁) :
    IsChebyshev C := by
  -- The zero left factor is `univ`, so the intersection is exactly the right halfspace.
  rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₁ hη₁, Set.univ_inter]
  exact innerProductClosedSublevelSet_isChebyshev_of_ne_zero hu₂

/-- In the positive-inner-product dependent case, the intersection `(29.21)` is Chebyshev because
it reduces to a single halfspace from Example 29.20. -/
theorem innerProductClosedSublevelSetInter_isChebyshev_of_cauchySchwarz_eq_of_inner_pos
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hinner : 0 < ⟪u₁, u₂⟫_ℝ) :
    IsChebyshev C := by
  have hu : ‖u₂‖ • u₁ ≠ 0 := smul_ne_zero (norm_ne_zero_iff.mpr hu₂) hu₁
  -- The dependent positive-inner branch collapses to a single nonzero halfspace.
  rw [innerProductClosedSublevelSetInter_eq_halfspace_of_cauchySchwarzEq_of_inner_pos
    hdep hu₁ hu₂ hinner]
  exact innerProductClosedSublevelSet_isChebyshev_of_ne_zero hu

/-- In the feasible negative-inner-product dependent case, the intersection `(29.21)` is
Chebyshev because it reduces to the strip from Example 29.21. -/
theorem innerProductClosedSublevelSetInter_isChebyshev_of_cauchySchwarz_eq_of_inner_neg_of_nonneg
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hinner : ⟪u₁, u₂⟫_ℝ < 0)
    (hη : 0 ≤ η₁ * ‖u₂‖ + η₂ * ‖u₁‖) :
    IsChebyshev C := by
  have hu : ‖u₂‖ • u₁ ≠ 0 := smul_ne_zero (norm_ne_zero_iff.mpr hu₂) hu₁
  have hγ : -η₂ * ‖u₁‖ ≤ η₁ * ‖u₂‖ := by
    -- The strip is feasible exactly when the left endpoint does not exceed the right endpoint.
    linarith
  rw [innerProductClosedSublevelSetInter_eq_strip_of_cauchySchwarzEq_of_inner_neg
    hdep hu₁ hu₂ hinner]
  exact innerProductStrip_isChebyshev_of_ne_zero_of_le hu hγ

/-- Case (1) companion: if `u₁ = u₂ = 0` and `0 ≤ min η₁ η₂`, then
`C = {x | ⟪x, u₁⟫_ℝ ≤ η₁} ∩ {x | ⟪x, u₂⟫_ℝ ≤ η₂} = univ` and `P_C = Id`. -/
theorem innerProductClosedSublevelSetInter_eq_univ_and_proj_eq_self_of_all_zero_of_nonneg_min
    (hu₁ : u₁ = 0) (hu₂ : u₂ = 0) (hη : 0 ≤ min η₁ η₂) :
    C = Set.univ ∧
      ∀ x : H,
        P[C,
          innerProductClosedSublevelSetInter_isChebyshev_of_eq_zero_of_eq_zero_of_nonneg_min
            hu₁ hu₂ hη] x = x := by
  have hη₁ : 0 ≤ η₁ := le_trans hη (min_le_left _ _)
  have hη₂ : 0 ≤ η₂ := le_trans hη (min_le_right _ _)
  have hC_eq : C = Set.univ := by
    -- Both factors are `univ`, so the intersection is `univ`.
    rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₁ hη₁]
    rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₂ hη₂]
    simp
  refine ⟨hC_eq, ?_⟩
  intro x
  have hx_mem : x ∈ C := by
    rw [hC_eq]
    simp
  have hx_best : IsBestApproximation x C x := by
    -- In the whole space, the point itself already realizes zero distance.
    refine ⟨hx_mem, ?_⟩
    simp [Metric.infDist_zero_of_mem hx_mem]
  exact
    (eq_projectionPoint_of_isBestApproximation C
      (innerProductClosedSublevelSetInter_isChebyshev_of_eq_zero_of_eq_zero_of_nonneg_min
        hu₁ hu₂ hη)
      hx_best).symm

/-- Case (2) companion: if `u₁ = u₂ = 0` and `min η₁ η₂ < 0`, then
`C = {x | ⟪x, u₁⟫_ℝ ≤ η₁} ∩ {x | ⟪x, u₂⟫_ℝ ≤ η₂} = ∅`. -/
theorem innerProductClosedSublevelSetInter_eq_empty_of_eq_zero_of_eq_zero_of_neg_min
    (hu₁ : u₁ = 0) (hu₂ : u₂ = 0) (hη : min η₁ η₂ < 0) :
    C = ∅ := by
  rcases min_lt_iff.mp hη with hη₁ | hη₂
  · -- A single empty factor already forces the whole intersection to be empty.
    rw [innerProductClosedSublevelSet_eq_empty_of_eq_zero_of_neg hu₁ hη₁, Set.empty_inter]
  · rw [innerProductClosedSublevelSet_eq_empty_of_eq_zero_of_neg hu₂ hη₂, Set.inter_empty]

/-- Case (3) companion: if `u₁ ≠ 0`, `u₂ = 0`, and `0 ≤ η₂`, then
`C = {x | ⟪x, u₁⟫_ℝ ≤ η₁}` and the metric projection onto `C` is the halfspace projector from
Example 29.20. -/
theorem innerProductClosedSublevelSetInter_eq_left_and_proj_eq_piecewise_of_right_eq_zero_of_nonneg
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ = 0) (hη₂ : 0 ≤ η₂) :
    C = innerProductClosedSublevelSet u₁ η₁ ∧
      ∀ x : H,
        P[C,
          innerProductClosedSublevelSetInter_isChebyshev_of_left_ne_zero_of_right_eq_zero_of_nonneg
            hu₁ hu₂ hη₂] x =
          if ⟪x, u₁⟫_ℝ ≤ η₁ then
            x
          else
            x + ((η₁ - ⟪x, u₁⟫_ℝ) / ‖u₁‖ ^ 2) • u₁ := by
  have hC_eq : C = innerProductClosedSublevelSet u₁ η₁ := by
    -- The feasible zero right factor contributes no additional constraint.
    rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₂ hη₂]
    simp
  refine ⟨hC_eq, ?_⟩
  intro x
  simpa [hC_eq] using projectionPoint_innerProductClosedSublevelSet_eq_piecewise_of_ne_zero hu₁ x

/-- Case (4) companion: if `u₁ ≠ 0`, `u₂ = 0`, and `η₂ < 0`, then
`C = {x | ⟪x, u₁⟫_ℝ ≤ η₁} ∩ {x | ⟪x, u₂⟫_ℝ ≤ η₂} = ∅`. -/
theorem innerProductClosedSublevelSetInter_eq_empty_of_left_ne_zero_of_right_eq_zero_of_neg
    (_hu₁ : u₁ ≠ 0) (hu₂ : u₂ = 0) (hη₂ : η₂ < 0) :
    C = ∅ := by
  -- The right factor is already empty, so the whole intersection is empty.
  rw [innerProductClosedSublevelSet_eq_empty_of_eq_zero_of_neg hu₂ hη₂, Set.inter_empty]

/-- Case (5) companion: if `u₁ = 0`, `u₂ ≠ 0`, and `0 ≤ η₁`, then
`C = {x | ⟪x, u₂⟫_ℝ ≤ η₂}` and the metric projection onto `C` is the halfspace projector from
Example 29.20. -/
theorem innerProductClosedSublevelSetInter_eq_right_and_proj_eq_piecewise_of_left_eq_zero_of_nonneg
    (hu₁ : u₁ = 0) (hu₂ : u₂ ≠ 0) (hη₁ : 0 ≤ η₁) :
    C = innerProductClosedSublevelSet u₂ η₂ ∧
      ∀ x : H,
        P[C,
          innerProductClosedSublevelSetInter_isChebyshev_of_left_eq_zero_of_right_ne_zero_of_nonneg
            hu₁ hu₂ hη₁] x =
          if ⟪x, u₂⟫_ℝ ≤ η₂ then
            x
          else
            x + ((η₂ - ⟪x, u₂⟫_ℝ) / ‖u₂‖ ^ 2) • u₂ := by
  have hC_eq : C = innerProductClosedSublevelSet u₂ η₂ := by
    -- The feasible zero left factor contributes no additional constraint.
    rw [innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu₁ hη₁]
    simp
  refine ⟨hC_eq, ?_⟩
  intro x
  simpa [hC_eq] using projectionPoint_innerProductClosedSublevelSet_eq_piecewise_of_ne_zero hu₂ x

/-- Case (6) companion: if `u₁ = 0`, `u₂ ≠ 0`, and `η₁ < 0`, then
`C = {x | ⟪x, u₁⟫_ℝ ≤ η₁} ∩ {x | ⟪x, u₂⟫_ℝ ≤ η₂} = ∅`. -/
theorem innerProductClosedSublevelSetInter_eq_empty_of_left_eq_zero_of_right_ne_zero_of_neg
    (hu₁ : u₁ = 0) (_hu₂ : u₂ ≠ 0) (hη₁ : η₁ < 0) :
    C = ∅ := by
  -- The left factor is already empty, so the whole intersection is empty.
  rw [innerProductClosedSublevelSet_eq_empty_of_eq_zero_of_neg hu₁ hη₁, Set.empty_inter]

section PositiveInner

local notation "u" => ‖u₂‖ • u₁
local notation "η" => min (η₁ * ‖u₂‖) (η₂ * ‖u₁‖)

/-- Case (7) companion: if
`‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2`, if `u₁ ≠ 0`, if `u₂ ≠ 0`, and if
`0 < ⟪u₁, u₂⟫_ℝ`, then `C = {x | ⟪x, u⟫_ℝ ≤ η}` with `u = ‖u₂‖ • u₁` and
`η = min (η₁ * ‖u₂‖) (η₂ * ‖u₁‖)`, and the metric projection onto `C` is the corresponding
halfspace projector. -/
theorem innerProductClosedSublevelSetInter_eq_halfspace_and_proj_eq_piecewise_of_inner_pos
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hinner : 0 < ⟪u₁, u₂⟫_ℝ) :
    C = innerProductClosedSublevelSet u η ∧
      ∀ x : H,
        P[C,
          innerProductClosedSublevelSetInter_isChebyshev_of_cauchySchwarz_eq_of_inner_pos
            hdep hu₁ hu₂ hinner] x =
          if ⟪x, u⟫_ℝ ≤ η then
            x
          else
            x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
  have hC_eq :
      C = innerProductClosedSublevelSet u η :=
    innerProductClosedSublevelSetInter_eq_halfspace_of_cauchySchwarzEq_of_inner_pos
      hdep hu₁ hu₂ hinner
  have hu : u ≠ 0 := smul_ne_zero (norm_ne_zero_iff.mpr hu₂) hu₁
  refine ⟨hC_eq, ?_⟩
  intro x
  have hproj :
      P[innerProductClosedSublevelSet (‖u₂‖ • u₁) (min (η₁ * ‖u₂‖) (η₂ * ‖u₁‖)),
        innerProductClosedSublevelSet_isChebyshev_of_ne_zero hu] x =
        if ⟪x, ‖u₂‖ • u₁⟫_ℝ ≤ min (η₁ * ‖u₂‖) (η₂ * ‖u₁‖) then
          x
        else
          x +
            ((min (η₁ * ‖u₂‖) (η₂ * ‖u₁‖) - ⟪x, ‖u₂‖ • u₁⟫_ℝ) / ‖‖u₂‖ • u₁‖ ^ 2) •
              (‖u₂‖ • u₁) := by
    -- The positive branch projector is exactly the Example 29.20 halfspace projector.
    exact projectionPoint_innerProductClosedSublevelSet_eq_piecewise_of_ne_zero hu x
  simpa [hC_eq, le_min_iff] using hproj

end PositiveInner

/-- Case (8) companion: if
`‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2`, if `u₁ ≠ 0`, if `u₂ ≠ 0`, if
`⟪u₁, u₂⟫_ℝ < 0`, and if `η₁ * ‖u₂‖ + η₂ * ‖u₁‖ < 0`, then
`C = {x | ⟪x, u₁⟫_ℝ ≤ η₁} ∩ {x | ⟪x, u₂⟫_ℝ ≤ η₂} = ∅`. -/
theorem innerProductClosedSublevelSetInter_eq_empty_of_cauchySchwarz_eq_of_inner_neg_of_sum_neg
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hinner : ⟪u₁, u₂⟫_ℝ < 0)
    (hη : η₁ * ‖u₂‖ + η₂ * ‖u₁‖ < 0) :
    C = ∅ := by
  have hC_eq :
      C = innerProductStrip (‖u₂‖ • u₁) (-η₂ * ‖u₁‖) (η₁ * ‖u₂‖) :=
    innerProductClosedSublevelSetInter_eq_strip_of_cauchySchwarzEq_of_inner_neg
      hdep hu₁ hu₂ hinner
  have hu : ‖u₂‖ • u₁ ≠ 0 := smul_ne_zero (norm_ne_zero_iff.mpr hu₂) hu₁
  have hγ : η₁ * ‖u₂‖ < -η₂ * ‖u₁‖ := by
    -- The strip endpoints are reversed exactly when the source scalar inequality is negative.
    linarith
  rw [hC_eq]
  exact innerProductStrip_eq_empty_of_ne_zero_of_right_lt_left hu hγ

section NegativeInner

local notation "u" => ‖u₂‖ • u₁
local notation "γ₁" => -η₂ * ‖u₁‖
local notation "γ₂" => η₁ * ‖u₂‖

/-- Case (9) companion: if
`‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2`, if `u₁ ≠ 0`, if `u₂ ≠ 0`, if
`⟪u₁, u₂⟫_ℝ < 0`, and if `0 ≤ η₁ * ‖u₂‖ + η₂ * ‖u₁‖`, then
`C = {x | γ₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ γ₂}` with
`u = ‖u₂‖ • u₁`, `γ₁ = -η₂ * ‖u₁‖`, and `γ₂ = η₁ * ‖u₂‖`, and the metric projection onto `C`
is the nonempty strip from Example 29.21, with the corresponding strip projector. -/
theorem innerProductClosedSublevelSetInter_eq_strip_and_proj_eq_piecewise_of_inner_neg_of_nonneg
    (hdep : ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 = |⟪u₁, u₂⟫_ℝ| ^ 2)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hinner : ⟪u₁, u₂⟫_ℝ < 0)
    (hη : 0 ≤ η₁ * ‖u₂‖ + η₂ * ‖u₁‖) :
    C = innerProductStrip u γ₁ γ₂ ∧
      (innerProductStrip u γ₁ γ₂).Nonempty ∧
      ∀ x : H,
        P[C,
          innerProductClosedSublevelSetInter_isChebyshev_of_cauchySchwarz_eq_of_inner_neg_of_nonneg
            hdep hu₁ hu₂ hinner hη] x =
          if ⟪x, u⟫_ℝ < γ₁ then
            x + ((γ₁ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u
          else if ⟪x, u⟫_ℝ ≤ γ₂ then
            x
          else
            x + ((γ₂ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
  have hC_eq :
      C = innerProductStrip u γ₁ γ₂ :=
    innerProductClosedSublevelSetInter_eq_strip_of_cauchySchwarzEq_of_inner_neg
      hdep hu₁ hu₂ hinner
  have hu : u ≠ 0 := smul_ne_zero (norm_ne_zero_iff.mpr hu₂) hu₁
  have hγ : γ₁ ≤ γ₂ := by
    -- The source nonnegative sum inequality is exactly the strip feasibility condition.
    linarith
  refine ⟨hC_eq, ?_, ?_⟩
  · exact innerProductStrip_nonempty_of_ne_zero_of_le hu hγ
  · intro x
    simpa [hC_eq] using projectionPoint_innerProductStrip_eq_piecewise_of_ne_zero_of_le hu hγ x

end NegativeInner

end
