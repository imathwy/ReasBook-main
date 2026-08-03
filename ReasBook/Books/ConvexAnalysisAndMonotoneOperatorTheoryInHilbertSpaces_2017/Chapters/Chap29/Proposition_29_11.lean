import BauschkeLean.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]

-- Semantic recall: the verified project owner for metric projections onto nonempty closed convex
-- sets is `projectionPoint`/`P[C, hC_cheb]`; this file states the source-facing norm estimate at
-- that canonical owner level.
/-- Proposition 29.11: if `C` is a nonempty closed convex subset of a real Hilbert space, `x ∈ H`,
and `1 < γ`, then the norm of the metric projection of `γ • x` onto `C` is at most `γ` times the
norm of the metric projection of `x` onto `C`. -/
theorem norm_projectionPoint_smul_le_mul_norm_projectionPoint_of_one_lt
    (x : H) {γ : ℝ} (hγ : 1 < γ) :
    ‖P_C (γ • x)‖ ≤ γ * ‖P_C x‖ := by
  let p := P_C x
  let q := P_C (γ • x)
  let a := q - p
  have hγ_nonneg : 0 ≤ γ := le_trans (by norm_num) hγ.le
  have hγ_sub_nonneg : 0 ≤ γ - 1 := sub_nonneg.mpr hγ.le
  have hq_eq : q = p + a := by
    dsimp [a]
    abel
  have hp_mem : p ∈ C := by
    dsimp [p]
    exact projectionPoint_mem C hC_cheb x
  have hp_variational : ∀ y ∈ C, inner ℝ (y - p) (x - p) ≤ 0 := by
    exact
      ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mp (by simp [p])).2
  have hq_mem : q ∈ C := by
    dsimp [q]
    exact projectionPoint_mem C hC_cheb (γ • x)
  have hq_variational : ∀ y ∈ C, inner ℝ (y - q) (γ • x - q) ≤ 0 := by
    exact
      ((eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mp (by simp [q])).2
  have hp_nonpos := by
    simpa [a] using hp_variational q hq_mem
  have hq_nonneg : 0 ≤ inner ℝ a (γ • x - q) := by
    have hq_nonpos := hq_variational p hp_mem
    have hneg : -inner ℝ a (γ • x - q) ≤ 0 := by
      calc
        -inner ℝ a (γ • x - q) = inner ℝ (-a) (γ • x - q) := by
          rw [inner_neg_left]
        _ = inner ℝ (p - q) (γ • x - q) := by
          congr 1
          simp [a]
        _ ≤ 0 := hq_nonpos
    linarith
  have hscaled_nonpos : γ * inner ℝ a (x - p) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hγ_nonneg hp_nonpos
  have hmain : 0 ≤ inner ℝ a (γ • p - q) := by
    have hrewrite := by
      have hvec : γ • p - q = (γ • x - q) - γ • (x - p) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, smul_sub]
        abel_nf
      change
        inner ℝ a (γ • p - q) =
          inner ℝ a (γ • x - q) - γ * inner ℝ a (x - p)
      calc
        inner ℝ a (γ • p - q) = inner ℝ a ((γ • x - q) - γ • (x - p)) := by
          rw [hvec]
        _ = inner ℝ a (γ • x - q) - inner ℝ a (γ • (x - p)) := by
          rw [inner_sub_right]
        _ = inner ℝ a (γ • x - q) - γ * inner ℝ a (x - p) := by
          rw [inner_smul_right]
    rw [hrewrite]
    linarith [hq_nonneg, hscaled_nonpos]
  have ha_main : 0 ≤ (γ - 1) * inner ℝ a p - ‖a‖ ^ 2 := by
    have hrewrite :
        inner ℝ a (γ • p - q) = (γ - 1) * inner ℝ a p - ‖a‖ ^ 2 := by
      have hvec : γ • p - q = (γ - 1) • p - a := by
        rw [hq_eq]
        calc
          γ • p - (p + a) = (γ • p - p) - a := by
            abel_nf
          _ = (γ - 1) • p - a := by
            rw [sub_smul, one_smul]
      calc
        inner ℝ a (γ • p - q) = inner ℝ a ((γ - 1) • p - a) := by
          rw [hvec]
        _ = inner ℝ a ((γ - 1) • p) - inner ℝ a a := by
          rw [inner_sub_right]
        _ = (γ - 1) * inner ℝ a p - ‖a‖ ^ 2 := by
          rw [inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hrewrite] at hmain
    exact hmain
  have ha_le : ‖a‖ ≤ (γ - 1) * ‖p‖ := by
    have ha_sq_le : ‖a‖ ^ 2 ≤ (γ - 1) * (‖a‖ * ‖p‖) := by
      have haux : ‖a‖ ^ 2 ≤ (γ - 1) * inner ℝ a p := by
        linarith
      exact le_trans haux <|
        mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hγ_sub_nonneg
    by_cases ha_zero : ‖a‖ = 0
    · have hnonneg : 0 ≤ (γ - 1) * ‖p‖ := mul_nonneg hγ_sub_nonneg (norm_nonneg p)
      simpa [ha_zero] using hnonneg
    · have ha_pos : 0 < ‖a‖ := by
        refine lt_of_le_of_ne (norm_nonneg a) ?_
        intro hzero
        exact ha_zero hzero.symm
      have hmul : ‖a‖ * ‖a‖ ≤ ‖a‖ * ((γ - 1) * ‖p‖) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using ha_sq_le
      exact le_of_mul_le_mul_left hmul ha_pos
  calc
    ‖P_C (γ • x)‖ = ‖q‖ := by simp [q]
    _ = ‖p + a‖ := by rw [hq_eq]
    _ ≤ ‖p‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ‖p‖ + (γ - 1) * ‖p‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ha_le ‖p‖
    _ = γ * ‖p‖ := by ring
    _ = γ * ‖P_C x‖ := by simp [p]

end
