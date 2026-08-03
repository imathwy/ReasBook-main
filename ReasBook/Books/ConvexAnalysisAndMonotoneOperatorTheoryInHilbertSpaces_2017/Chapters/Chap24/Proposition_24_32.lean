import BauschkeLean.Chap12.Proposition_12_29
import BauschkeLean.Chap24.Proposition_24_31

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

-- Semantic recall/local precedent: `lean_leansearch` only surfaced generic convex-monotonicity
-- results, so this item follows the verified local Chapter 12 proximal owner `Prox[f, hf]`, the
-- minimizer hypothesis `0 ∈ Argmin φ.asEReal`, and the canonical real-interval surface
-- `Set.uIcc 0 ξ` for the source claim “`Prox_φ ξ ∈ conv {0, ξ}`”.

/-- Proposition 24.32: if `φ ∈ Γ₀(ℝ)` and `0` is a minimizer of `φ`,
then for every `ξ : ℝ`, the proximal point `Prox[φ, hφ] ξ`
lies in the closed interval between `0` and `ξ`;
equivalently, it belongs to the real segment joining `0` and `ξ`. -/
theorem prox_mem_uIcc_zero_self_of_zero_mem_argmin
    {φ : ℝ → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(ℝ))
    (hmin : (0 : ℝ) ∈ Argmin φ.asEReal) (ξ : ℝ) :
    Prox[φ, hφ] ξ ∈ Set.uIcc (0 : ℝ) ξ := by
  rcases
      (exists_eq_proximityOperator_iff_lipschitzWith_one_and_monotone_real (Prox[φ, hφ])).1
        ⟨φ, hφ, rfl⟩ with
    ⟨hLip, hmono⟩
  have hzero_mem : (0 : ℝ) ∈ Function.fixedPoints (Prox[φ, hφ]) := by
    rw [fixedPoints_proximityOperator_eq_argmin_of_mem_gammaZero φ hφ]
    exact hmin
  have hzero : Prox[φ, hφ] 0 = 0 := Function.mem_fixedPoints_iff.mp hzero_mem
  have habs : |Prox[φ, hφ] ξ| ≤ |ξ| := by
    simpa [Real.dist_eq, hzero] using hLip.dist_le_mul 0 ξ
  rcases le_total 0 ξ with hξ | hξ
  · have hnonneg : 0 ≤ Prox[φ, hφ] ξ := by
      simpa [hzero] using hmono hξ
    have hupper : Prox[φ, hφ] ξ ≤ ξ := by
      rw [abs_of_nonneg hnonneg, abs_of_nonneg hξ] at habs
      exact habs
    exact Set.mem_uIcc_of_le hnonneg hupper
  · have hnonpos : Prox[φ, hφ] ξ ≤ 0 := by
      simpa [hzero] using hmono hξ
    have hlower : ξ ≤ Prox[φ, hφ] ξ := by
      rw [abs_of_nonpos hnonpos, abs_of_nonpos hξ] at habs
      linarith
    exact Set.mem_uIcc_of_ge hlower hnonpos

end ERealFunction
