import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap03.Theorem_3_16_2

open scoped InnerProductSpace

universe u

noncomputable section

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall: `lean_leansearch` surfaced mathlib's scalar interval projector `Set.projIcc`.
-- This item keeps the source-facing strip owner, records its canonical `Set.Icc` preimage form,
-- and uses the Chapter 3 projector notation `P[C, hC]` in the source-facing projection formulas.

/-- The strip `{x | η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂}` cut out by the inner-product functional
`x ↦ ⟪x, u⟫_ℝ`. -/
def innerProductStrip (u : H) (η₁ η₂ : ℝ) : Set H :=
  {x | η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂}

/-- `innerProductStrip u η₁ η₂` is the preimage of the closed interval `Set.Icc η₁ η₂` under the
inner-product functional `x ↦ ⟪x, u⟫_ℝ`. -/
theorem innerProductStrip_eq_preimage_Icc (u : H) (η₁ η₂ : ℝ) :
    innerProductStrip u η₁ η₂ = (fun x : H ↦ ⟪x, u⟫_ℝ) ⁻¹' Set.Icc η₁ η₂ := by
  ext x
  rfl

/-- Membership in `innerProductStrip u η₁ η₂` is exactly the defining pair of scalar inequalities.
-/
@[simp] theorem mem_innerProductStrip_iff (u : H) (η₁ η₂ : ℝ) (x : H) :
    x ∈ innerProductStrip u η₁ η₂ ↔ η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂ :=
  Iff.rfl

/-- Helper for Example 29.21: correcting `x` along `u` so that the new inner product with `u`
equals `η` hits the prescribed scalar level exactly. -/
private theorem inner_add_div_normSq_smul_eq
    (u x : H) (η : ℝ) (hu : u ≠ 0) :
    ⟪x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u, u⟫_ℝ = η := by
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  -- Expand the inner product against `u` and simplify the correction coefficient.
  calc
    ⟪x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u, u⟫_ℝ
        = ⟪x, u⟫_ℝ + (((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ) := by
            rw [inner_add_left, real_inner_smul_left]
    _ = ⟪x, u⟫_ℝ + (((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) * (‖u‖ ^ 2)) := by
          rw [real_inner_self_eq_norm_sq]
    _ = ⟪x, u⟫_ℝ + (η - ⟪x, u⟫_ℝ) := by
          field_simp [hu_sq]
    _ = η := by
          ring

/-- Helper for Example 29.21: if `η ∈ [η₁, η₂]`, then correcting `x` to the level `η` lands in
`innerProductStrip u η₁ η₂`. -/
private theorem correctedPoint_mem_innerProductStrip
    (u x : H) {η η₁ η₂ : ℝ} (hu : u ≠ 0) (hη₁ : η₁ ≤ η) (hη₂ : η ≤ η₂) :
    x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u ∈ innerProductStrip u η₁ η₂ := by
  -- The corrected point has inner product exactly `η`, so the strip bounds reduce to `η ∈ [η₁,η₂]`.
  rw [mem_innerProductStrip_iff]
  constructor
  · simpa [inner_add_div_normSq_smul_eq u x η hu] using hη₁
  · simpa [inner_add_div_normSq_smul_eq u x η hu] using hη₂

/-- Helper for Example 29.21: the left boundary witness `((η₁ / ‖u‖ ^ 2) • u)` lies in the strip
whenever `u ≠ 0` and `η₁ ≤ η₂`. -/
private theorem leftEndpoint_mem_innerProductStrip
    (u : H) (η₁ η₂ : ℝ) (hu : u ≠ 0) (hη : η₁ ≤ η₂) :
    ((η₁ / ‖u‖ ^ 2) • u : H) ∈ innerProductStrip u η₁ η₂ := by
  -- View the witness as the correction of `0` onto the left boundary level `η₁`.
  simpa using
    correctedPoint_mem_innerProductStrip (u := u) (x := (0 : H)) (η := η₁) hu (le_rfl) hη

omit [InnerProductSpace ℝ H] in
/-- The parameters of `innerProductStrip u η₁ η₂` fall into one of the four source cases from
Example 29.21. -/
theorem innerProductStrip_case_partition (u : H) (η₁ η₂ : ℝ) :
    (u = 0 ∧ η₁ ≤ 0 ∧ 0 ≤ η₂) ∨
      (u = 0 ∧ (0 < η₁ ∨ η₂ < 0)) ∨
      (u ≠ 0 ∧ η₂ < η₁) ∨
      (u ≠ 0 ∧ η₁ ≤ η₂) := by
  -- Split first on whether the normal vector vanishes, then on the interval order.
  by_cases hu : u = 0
  · by_cases hη₁ : η₁ ≤ 0
    · by_cases hη₂ : 0 ≤ η₂
      · exact Or.inl ⟨hu, hη₁, hη₂⟩
      · exact Or.inr <| Or.inl ⟨hu, Or.inr (lt_of_not_ge hη₂)⟩
    · exact Or.inr <| Or.inl ⟨hu, Or.inl (lt_of_not_ge hη₁)⟩
  · by_cases hη : η₂ < η₁
    · exact Or.inr <| Or.inr <| Or.inl ⟨hu, hη⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨hu, le_of_not_gt hη⟩

/-- The strip `innerProductStrip u η₁ η₂` is closed. -/
theorem innerProductStrip_isClosed (u : H) (η₁ η₂ : ℝ) :
    IsClosed (innerProductStrip u η₁ η₂) := by
  -- Realize the strip as the preimage of a closed interval under the continuous evaluation map.
  rw [innerProductStrip_eq_preimage_Icc]
  have hcont : Continuous (fun x : H ↦ ⟪x, u⟫_ℝ) := by
    continuity
  exact isClosed_Icc.preimage hcont

/-- The strip `innerProductStrip u η₁ η₂` is convex. -/
theorem innerProductStrip_convex (u : H) (η₁ η₂ : ℝ) :
    Convex ℝ (innerProductStrip u η₁ η₂) := by
  -- Convex combinations preserve both scalar inequalities defining the strip.
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  rw [mem_innerProductStrip_iff]
  have hinner :
      ⟪a • x + b • y, u⟫_ℝ = a * ⟪x, u⟫_ℝ + b * ⟪y, u⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  constructor
  · rw [hinner]
    have hx₁' : a * η₁ ≤ a * ⟪x, u⟫_ℝ := mul_le_mul_of_nonneg_left hx₁ ha
    have hy₁' : b * η₁ ≤ b * ⟪y, u⟫_ℝ := mul_le_mul_of_nonneg_left hy₁ hb
    calc
      η₁ = (a + b) * η₁ := by
            rw [hab, one_mul]
      _ = a * η₁ + b * η₁ := by
            ring
      _ ≤ a * ⟪x, u⟫_ℝ + b * ⟪y, u⟫_ℝ := add_le_add hx₁' hy₁'
  · rw [hinner]
    have hx₂' : a * ⟪x, u⟫_ℝ ≤ a * η₂ := mul_le_mul_of_nonneg_left hx₂ ha
    have hy₂' : b * ⟪y, u⟫_ℝ ≤ b * η₂ := mul_le_mul_of_nonneg_left hy₂ hb
    calc
      a * ⟪x, u⟫_ℝ + b * ⟪y, u⟫_ℝ ≤ a * η₂ + b * η₂ := add_le_add hx₂' hy₂'
      _ = (a + b) * η₂ := by
            ring
      _ = η₂ := by
            rw [hab, one_mul]

section Complete

variable [CompleteSpace H]
variable {u : H} {η₁ η₂ : ℝ}

/-- If `u = 0` and `η₁ ≤ 0 ≤ η₂`, then `innerProductStrip u η₁ η₂` is a Chebyshev set. -/
theorem innerProductStrip_isChebyshev_of_eq_zero_of_le_zero_of_zero_le
    (hu : u = 0) (hη₁ : η₁ ≤ 0) (hη₂ : 0 ≤ η₂) :
    IsChebyshev (innerProductStrip u η₁ η₂) := by
  -- Under the feasible zero-normal assumptions, the strip contains every point.
  have h_nonempty : (innerProductStrip u η₁ η₂).Nonempty := by
    refine ⟨0, ?_⟩
    simp [innerProductStrip, hu, hη₁, hη₂]
  exact
    isChebyshev_of_nonempty_isClosed_convex
      h_nonempty
      (innerProductStrip_isClosed u η₁ η₂)
      (innerProductStrip_convex u η₁ η₂)

/-- If `u ≠ 0` and `η₁ ≤ η₂`, then `innerProductStrip u η₁ η₂` is a Chebyshev set. -/
theorem innerProductStrip_isChebyshev_of_ne_zero_of_le
    (hu : u ≠ 0) (hη : η₁ ≤ η₂) :
    IsChebyshev (innerProductStrip u η₁ η₂) := by
  -- The explicit left-boundary point makes the strip nonempty, so the Hilbert projection theorem
  -- applies.
  have h_nonempty : (innerProductStrip u η₁ η₂).Nonempty := by
    exact ⟨((η₁ / ‖u‖ ^ 2) • u : H), leftEndpoint_mem_innerProductStrip u η₁ η₂ hu hη⟩
  exact
    isChebyshev_of_nonempty_isClosed_convex
      h_nonempty
      (innerProductStrip_isClosed u η₁ η₂)
      (innerProductStrip_convex u η₁ η₂)

omit [CompleteSpace H] in
/-- A clause of Example 29.21: if `u = 0` and `η₁ ≤ 0 ≤ η₂`, then
`C = {x | η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂} = univ`. -/
theorem innerProductStrip_eq_univ_of_eq_zero_of_le_zero_of_zero_le
    (hu : u = 0) (hη₁ : η₁ ≤ 0) (hη₂ : 0 ≤ η₂) :
    innerProductStrip u η₁ η₂ = Set.univ := by
  -- With zero normal vector and feasible bounds, both inequalities collapse to `η₁ ≤ 0 ≤ η₂`.
  ext x
  simp [innerProductStrip, hu, hη₁, hη₂]

/-- A clause of Example 29.21: if `u = 0` and `η₁ ≤ 0 ≤ η₂`, then the projection onto
`C = {x | η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂}` fixes every point. -/
theorem projectionPoint_innerProductStrip_eq_self_of_eq_zero_of_le_zero_of_zero_le
    (hu : u = 0) (hη₁ : η₁ ≤ 0) (hη₂ : 0 ≤ η₂) (x : H) :
    P[innerProductStrip u η₁ η₂,
      innerProductStrip_isChebyshev_of_eq_zero_of_le_zero_of_zero_le hu hη₁ hη₂] x = x := by
  let hC : IsChebyshev (innerProductStrip u η₁ η₂) :=
    innerProductStrip_isChebyshev_of_eq_zero_of_le_zero_of_zero_le hu hη₁ hη₂
  have hconv : Convex ℝ (innerProductStrip u η₁ η₂) := innerProductStrip_convex u η₁ η₂
  -- In the feasible zero-normal branch, the point `x` already belongs to the strip and has zero
  -- residual.
  have hx_proj : x = projectionPoint (innerProductStrip u η₁ η₂) hC x :=
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hconv).2 <| by
      constructor
      · simp [innerProductStrip, hu, hη₁, hη₂]
      · intro y hy
        simp
  simpa [hC] using hx_proj.symm

omit [CompleteSpace H] in
/-- A clause of Example 29.21: if `u = 0` and `η₁ > 0` or `η₂ < 0`, then
`C = {x | η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂} = ∅`. -/
theorem innerProductStrip_eq_empty_of_eq_zero_of_zero_lt_left_or_right_lt_zero
    (hu : u = 0) (hη : 0 < η₁ ∨ η₂ < 0) :
    innerProductStrip u η₁ η₂ = ∅ := by
  -- With zero normal vector, one infeasible scalar bound already rules out every point.
  ext x
  constructor
  · intro hx
    rcases hη with hη | hη
    · have hleft : η₁ ≤ 0 := by
        simpa [hu] using hx.1
      exact (not_le_of_gt hη) hleft
    · have hright : 0 ≤ η₂ := by
        simpa [hu] using hx.2
      exact (not_le_of_gt hη) hright
  · intro hx
    exact False.elim hx

omit [CompleteSpace H] in
/-- A clause of Example 29.21: if `u ≠ 0` and `η₁ > η₂`, then
`C = {x | η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂} = ∅`. -/
theorem innerProductStrip_eq_empty_of_ne_zero_of_right_lt_left
    (_hu : u ≠ 0) (hη : η₂ < η₁) :
    innerProductStrip u η₁ η₂ = ∅ := by
  -- The two strip inequalities contradict the strict interval reversal.
  ext x
  constructor
  · intro hx
    linarith [hx.1, hx.2, hη]
  · intro hx
    exact False.elim hx

omit [CompleteSpace H] in
/-- A clause of Example 29.21: if `u ≠ 0` and `η₁ ≤ η₂`, then
`C = {x | η₁ ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ η₂}` is nonempty. -/
theorem innerProductStrip_nonempty_of_ne_zero_of_le
    (hu : u ≠ 0) (hη : η₁ ≤ η₂) :
    (innerProductStrip u η₁ η₂).Nonempty := by
  -- The left boundary witness already lies in the strip.
  exact ⟨((η₁ / ‖u‖ ^ 2) • u : H), leftEndpoint_mem_innerProductStrip u η₁ η₂ hu hη⟩

/-- Example 29.21 (6): if `u ≠ 0` and `η₁ ≤ η₂`, then for
`C = {y | η₁ ≤ ⟪y, u⟫_ℝ ∧ ⟪y, u⟫_ℝ ≤ η₂}`, the projection `P_C x` is given by the piecewise
formula from `(29.20)`. -/
theorem projectionPoint_innerProductStrip_eq_piecewise_of_ne_zero_of_le
    (hu : u ≠ 0) (hη : η₁ ≤ η₂) (x : H) :
    P[innerProductStrip u η₁ η₂,
      innerProductStrip_isChebyshev_of_ne_zero_of_le hu hη] x =
      if ⟪x, u⟫_ℝ < η₁ then
        x + ((η₁ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u
      else if ⟪x, u⟫_ℝ ≤ η₂ then
        x
      else
        x + ((η₂ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
  let hC : IsChebyshev (innerProductStrip u η₁ η₂) :=
    innerProductStrip_isChebyshev_of_ne_zero_of_le hu hη
  have hconv : Convex ℝ (innerProductStrip u η₁ η₂) := innerProductStrip_convex u η₁ η₂
  have hu_sq_pos : 0 < ‖u‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hu) 2
  -- Route correction: instead of transporting the scalar proximal operator from Chapter 24,
  -- characterize the projection directly by the Chapter 3 variational inequality.
  by_cases hx₁ : ⟪x, u⟫_ℝ < η₁
  · rw [if_pos hx₁]
    let a : ℝ := (η₁ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2
    let p : H := x + a • u
    have ha_nonneg : 0 ≤ a := by
      exact div_nonneg (sub_nonneg.mpr (le_of_lt hx₁)) hu_sq_pos.le
    have hp_mem : p ∈ innerProductStrip u η₁ η₂ := by
      -- The left correction lands exactly on the boundary level `η₁`.
      simpa [p, a] using
        correctedPoint_mem_innerProductStrip (u := u) (x := x) (η := η₁) hu (le_rfl) hη
    have hp_level : ⟪p, u⟫_ℝ = η₁ := by
      -- The correction coefficient was chosen so that the new inner product equals `η₁`.
      simpa [p, a] using inner_add_div_normSq_smul_eq u x η₁ hu
    have hp_proj : p = projectionPoint (innerProductStrip u η₁ η₂) hC x :=
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hconv).2 <| by
        constructor
        · exact hp_mem
        · intro y hy
          rcases hy with ⟨hy₁, hy₂⟩
          have hy_gap_nonneg : 0 ≤ ⟪y, u⟫_ℝ - η₁ := by
            linarith
          have hinner :
              ⟪y - p, x - p⟫_ℝ = (-a) * (⟪y, u⟫_ℝ - η₁) := by
            calc
              ⟪y - p, x - p⟫_ℝ = ⟪y - p, -(a • u)⟫_ℝ := by
                  simp [p, sub_eq_add_neg, add_comm]
              _ = -(a * ⟪y - p, u⟫_ℝ) := by
                  rw [inner_neg_right, real_inner_smul_right]
              _ = (-a) * ⟪y - p, u⟫_ℝ := by
                  ring
              _ = (-a) * (⟪y, u⟫_ℝ - η₁) := by
                  rw [inner_sub_left, hp_level]
          rw [hinner]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha_nonneg) hy_gap_nonneg
    simpa [hC, p, a] using hp_proj.symm
  · rw [if_neg hx₁]
    by_cases hx₂ : ⟪x, u⟫_ℝ ≤ η₂
    · rw [if_pos hx₂]
      have hx_mem : x ∈ innerProductStrip u η₁ η₂ := by
        rw [mem_innerProductStrip_iff]
        exact ⟨le_of_not_gt hx₁, hx₂⟩
      -- Points already inside the strip are fixed by the metric projection.
      have hx_proj : x = projectionPoint (innerProductStrip u η₁ η₂) hC x :=
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hconv).2 <| by
          constructor
          · exact hx_mem
          · intro y hy
            simp
      simpa [hC] using hx_proj.symm
    · rw [if_neg hx₂]
      let a : ℝ := (η₂ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2
      let p : H := x + a • u
      have ha_nonpos : a ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (le_of_not_ge hx₂))
          hu_sq_pos.le
      have hp_mem : p ∈ innerProductStrip u η₁ η₂ := by
        -- The right correction lands exactly on the boundary level `η₂`.
        simpa [p, a] using
          correctedPoint_mem_innerProductStrip (u := u) (x := x) (η := η₂) hu hη (le_rfl)
      have hp_level : ⟪p, u⟫_ℝ = η₂ := by
        -- The correction coefficient was chosen so that the new inner product equals `η₂`.
        simpa [p, a] using inner_add_div_normSq_smul_eq u x η₂ hu
      have hp_proj : p = projectionPoint (innerProductStrip u η₁ η₂) hC x :=
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hconv).2 <| by
          constructor
          · exact hp_mem
          · intro y hy
            rcases hy with ⟨hy₁, hy₂⟩
            have hy_gap_nonpos : ⟪y, u⟫_ℝ - η₂ ≤ 0 := by
              linarith
            have hinner :
                ⟪y - p, x - p⟫_ℝ = (-a) * (⟪y, u⟫_ℝ - η₂) := by
              calc
                ⟪y - p, x - p⟫_ℝ = ⟪y - p, -(a • u)⟫_ℝ := by
                    simp [p, sub_eq_add_neg, add_comm]
                _ = -(a * ⟪y - p, u⟫_ℝ) := by
                    rw [inner_neg_right, real_inner_smul_right]
                _ = (-a) * ⟪y - p, u⟫_ℝ := by
                    ring
                _ = (-a) * (⟪y, u⟫_ℝ - η₂) := by
                    rw [inner_sub_left, hp_level]
            rw [hinner]
            exact mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr ha_nonpos) hy_gap_nonpos
      simpa [hC, p, a] using hp_proj.symm

end Complete

end

end
