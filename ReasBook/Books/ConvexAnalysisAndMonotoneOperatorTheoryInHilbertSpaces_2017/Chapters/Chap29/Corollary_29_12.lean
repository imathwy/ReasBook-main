import BauschkeLean.Chap29.Proposition_29_1
import BauschkeLean.Chap29.Proposition_29_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]

-- Semantic recall: `lean_leansearch` only surfaced generic orthogonal-projection monotonicity
-- results, while the local Chapter 29 API for this corollary is the metric projector
-- `projectionPoint`/`P[C, hC_cheb]` together with Propositions 29.1 and 29.11.
/-- Corollary 29.12: let `C` be a nonempty closed convex subset of the real Hilbert space `H`,
let `x ∈ H`, and let `y ∈ H`. Then the function
`α ↦ α⁻¹ * ‖P_C (y + α • x) - y‖` is decreasing on `]0, ∞[`. -/
theorem antitoneOn_inv_mul_norm_projectionPoint_add_smul_sub
    (x y : H) :
    AntitoneOn
      (fun α : ℝ ↦ α⁻¹ * ‖P_C (y + α • x) - y‖)
      (Set.Ioi (0 : ℝ)) := by
  let D : Set H := (-y) +ᵥ C
  have hD_nonempty : D.Nonempty := by
    rcases hC_nonempty with ⟨z, hz⟩
    refine ⟨-y + z, ?_⟩
    exact Set.mem_vadd_set.2 ⟨z, hz, rfl⟩
  have hD_closed : IsClosed D := by
    simpa [D, vadd_eq_add] using hC_closed.left_addCoset (-y)
  have hD_convex : Convex ℝ D := by
    simpa [D] using hC_convex.vadd (-y)
  let hD_cheb : IsChebyshev D :=
    isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
  have htranslate (α : ℝ) :
      ‖P_C (y + α • x) - y‖ = ‖P[D, hD_cheb] (α • x)‖ := by
    have hproj :
        P[D, hD_cheb] (α • x) = P_C (y + α • x) - y := by
      simpa [D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, vadd_eq_add] using
        (projectionPoint_vadd_set_eq_add_projectionPoint
          (α • x) (-y) hC_nonempty hC_closed hC_convex)
    simp [hproj]
  intro α hα β hβ hαβ
  have hα_pos : 0 < α := hα
  rcases lt_or_eq_of_le hαβ with hlt | rfl
  · have hγ : 1 < β / α := by
      exact (one_lt_div hα_pos).2 hlt
    have hβα : (β / α) * α = β := by
      simpa using div_mul_cancel₀ β hα_pos.ne'
    have hsmul : (β / α) • (α • x) = β • x := by
      calc
        (β / α) • (α • x) = ((β / α) * α) • x := by rw [smul_smul]
        _ = β • x := by simp [hβα]
    have hproj_le :
        ‖P[D, hD_cheb] (β • x)‖ ≤ (β / α) * ‖P[D, hD_cheb] (α • x)‖ := by
      simpa [hsmul] using
        (norm_projectionPoint_smul_le_mul_norm_projectionPoint_of_one_lt
          hD_nonempty hD_closed hD_convex (α • x) hγ)
    have hβ_pos : 0 < β := lt_of_lt_of_le hα_pos hαβ
    have hfactor : β⁻¹ * (β / α) = α⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hβ_pos.ne', one_mul]
    calc
      β⁻¹ * ‖P_C (y + β • x) - y‖ = β⁻¹ * ‖P[D, hD_cheb] (β • x)‖ := by
        rw [htranslate β]
      _ ≤ β⁻¹ * ((β / α) * ‖P[D, hD_cheb] (α • x)‖) := by
        exact mul_le_mul_of_nonneg_left hproj_le (inv_nonneg.mpr hβ_pos.le)
      _ = (β⁻¹ * (β / α)) * ‖P[D, hD_cheb] (α • x)‖ := by
        rw [← mul_assoc]
      _ = α⁻¹ * ‖P[D, hD_cheb] (α • x)‖ := by rw [hfactor]
      _ = α⁻¹ * ‖P_C (y + α • x) - y‖ := by rw [htranslate α]
  · rfl

end
