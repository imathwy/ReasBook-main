import BauschkeLean.Chap01.Text_1_0_2
import BauschkeLean.Chap07.Corollary_7_19
import BauschkeLean.Chap29.Proposition_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : Set H}
variable (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
variable (hK_convex : Convex ℝ K)

local notation "hK_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex

local notation "P_K" => P[K, hK_cheb]

omit [CompleteSpace H] in
private lemma smul_mem_of_isCone (hK_cone : IsCone K) {x : H} (hx : x ∈ K) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ρ • x ∈ K := by
  rw [isCone_iff] at hK_cone
  rw [hK_cone]
  exact Set.mem_smul.mpr ⟨ρ, hρ, x, hx, rfl⟩

omit [CompleteSpace H] in
private lemma smul_set_eq_self_of_isCone (hK_cone : IsCone K) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ • K = K := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact smul_mem_of_isCone hK_cone hx hρ
  · intro y hy
    have hy' : ρ⁻¹ • y ∈ K := smul_mem_of_isCone hK_cone hy (inv_pos.mpr hρ)
    have hy'' : ρ • (ρ⁻¹ • y) ∈ ρ • K := Set.smul_mem_smul_set hy'
    simpa [smul_smul, mul_inv_cancel₀ (show ρ ≠ 0 from hρ.ne'), one_smul] using hy''

-- Semantic recall: Proposition 29.29 is the cone specialization of the Chapter 29 scaled-set
-- projection owner `projectionPoint_smul_set_eq_smul_projectionPoint`.

/-- Proposition 29.29: let `K` be a nonempty closed convex cone in `H`, let `x ∈ H`, and let
`ρ ∈ ℝ_+`. Then `P_K (ρ • x) = ρ • P_K x`. -/
theorem projectionPoint_nnnreal_smul_eq_nnnreal_smul_projectionPoint
    (hK_cone : IsCone K) (x : H) (ρ : NNReal) :
    P_K (ρ • x) = ρ • P_K x := by
  by_cases hρ : ρ = 0
  · subst hρ
    have hzero_mem : (0 : H) ∈ K :=
      Set.zero_mem_of_nonempty_of_isClosed_of_isCone hK_nonempty hK_closed hK_cone
    have hproj : P_K 0 = (0 : H) := by
      have hbest : (0 : H) = P_K 0 := by
        refine eq_projectionPoint_of_isBestApproximation K hK_cheb ?_
        exact ⟨hzero_mem, by simp [Metric.infDist_zero_of_mem hzero_mem]⟩
      exact hbest.symm
    have hzero_smul_x : (0 : NNReal) • x = (0 : H) := by
      simp [NNReal.smul_def]
    have hzero_smul_proj : (0 : NNReal) • P_K x = (0 : H) := by
      simp [NNReal.smul_def]
    rw [hzero_smul_x, hzero_smul_proj]
    exact hproj
  · have hρ_ne : (ρ : ℝ) ≠ 0 := by
      exact_mod_cast hρ
    have hρ_pos : 0 < (ρ : ℝ) := by
      exact_mod_cast (show 0 < ρ from pos_iff_ne_zero.mpr hρ)
    have hρK : ((ρ : ℝ) • K : Set H) = K := smul_set_eq_self_of_isCone hK_cone hρ_pos
    simpa [hρK, smul_smul, hρ_ne] using
      (projectionPoint_smul_set_eq_smul_projectionPoint
        ((ρ : ℝ) • x) hK_nonempty hK_closed hK_convex hρ_ne)

end
