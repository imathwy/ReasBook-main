import DifferentialForms_Cartan_1970.III.section10.frozen_0011_Theorem_III_4_extra_9.LoopHomotopy

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the punctured ball
`ball (0 : ℂ) ε \ {0}` is path connected. -/
lemma isPathConnected_puncturedBallComplex {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  let U₁ : Set ℂ := ball (0 : ℂ) ε ∩ {z : ℂ | 0 < z.re}
  let U₂ : Set ℂ := ball (0 : ℂ) ε ∩ {z : ℂ | 0 < z.im}
  let U₃ : Set ℂ := ball (0 : ℂ) ε ∩ {z : ℂ | z.re < 0}
  let U₄ : Set ℂ := ball (0 : ℂ) ε ∩ {z : ℂ | z.im < 0}
  let q : ℝ := ε / 4
  let a : ℂ := (q : ℂ) + (q : ℂ) * Complex.I
  let b : ℂ := (-q : ℂ) + (q : ℂ) * Complex.I
  let c : ℂ := (-q : ℂ) - (q : ℂ) * Complex.I
  have hq_pos : 0 < q := by
    dsimp [q]
    linarith
  have hq_twice_lt : q + q < ε := by
    dsimp [q]
    linarith
  have ha_ball : a ∈ ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc
      ‖a‖ ≤ ‖(q : ℂ)‖ + ‖(q : ℂ) * Complex.I‖ := by
        simpa [a] using norm_add_le (q : ℂ) ((q : ℂ) * Complex.I)
      _ = q + q := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, Complex.norm_real]
        simp [abs_of_pos hq_pos]
      _ < ε := hq_twice_lt
  have hb_ball : b ∈ ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc
      ‖b‖ ≤ ‖(-q : ℂ)‖ + ‖(q : ℂ) * Complex.I‖ := by
        simpa [b] using norm_add_le (-((q : ℂ))) ((q : ℂ) * Complex.I)
      _ = q + q := by
        rw [norm_neg, Complex.norm_real, norm_mul, Complex.norm_I, Complex.norm_real]
        simp [abs_of_pos hq_pos]
      _ < ε := hq_twice_lt
  have hc_ball : c ∈ ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc
      ‖c‖ ≤ ‖(-q : ℂ)‖ + ‖-((q : ℂ) * Complex.I)‖ := by
        simpa [c, sub_eq_add_neg] using norm_add_le (-((q : ℂ))) (-((q : ℂ) * Complex.I))
      _ = q + q := by
        rw [norm_neg, Complex.norm_real, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real]
        simp [abs_of_pos hq_pos]
      _ < ε := hq_twice_lt
  have haU₁ : a ∈ U₁ := by
    change a ∈ ball (0 : ℂ) ε ∩ {z : ℂ | 0 < z.re}
    exact ⟨ha_ball, by simpa [a, q] using hq_pos⟩
  have haU₂ : a ∈ U₂ := by
    change a ∈ ball (0 : ℂ) ε ∩ {z : ℂ | 0 < z.im}
    exact ⟨ha_ball, by simpa [a, q] using hq_pos⟩
  have hbU₂ : b ∈ U₂ := by
    change b ∈ ball (0 : ℂ) ε ∩ {z : ℂ | 0 < z.im}
    exact ⟨hb_ball, by simpa [b, q] using hq_pos⟩
  have hbU₃ : b ∈ U₃ := by
    change b ∈ ball (0 : ℂ) ε ∩ {z : ℂ | z.re < 0}
    exact ⟨hb_ball, by simpa [b, q] using neg_neg_of_pos hq_pos⟩
  have hcU₃ : c ∈ U₃ := by
    change c ∈ ball (0 : ℂ) ε ∩ {z : ℂ | z.re < 0}
    exact ⟨hc_ball, by simpa [c, q] using neg_neg_of_pos hq_pos⟩
  have hcU₄ : c ∈ U₄ := by
    change c ∈ ball (0 : ℂ) ε ∩ {z : ℂ | z.im < 0}
    exact ⟨hc_ball, by simpa [c, q] using neg_neg_of_pos hq_pos⟩
  have hU₁_path : IsPathConnected U₁ := by
    exact ((convex_ball (0 : ℂ) ε).inter (convex_halfSpace_re_gt 0)).isPathConnected ⟨a, haU₁⟩
  have hU₂_path : IsPathConnected U₂ := by
    exact ((convex_ball (0 : ℂ) ε).inter (convex_halfSpace_im_gt 0)).isPathConnected ⟨a, haU₂⟩
  have hU₃_path : IsPathConnected U₃ := by
    exact ((convex_ball (0 : ℂ) ε).inter (convex_halfSpace_re_lt 0)).isPathConnected ⟨b, hbU₃⟩
  have hU₄_path : IsPathConnected U₄ := by
    exact ((convex_ball (0 : ℂ) ε).inter (convex_halfSpace_im_lt 0)).isPathConnected ⟨c, hcU₄⟩
  have hU₁₂_path : IsPathConnected (U₁ ∪ U₂) := by
    exact hU₁_path.union hU₂_path ⟨a, haU₁, haU₂⟩
  have hU₁₂₃_path : IsPathConnected ((U₁ ∪ U₂) ∪ U₃) := by
    exact hU₁₂_path.union hU₃_path ⟨b, Or.inr hbU₂, hbU₃⟩
  have hcover :
      ball (0 : ℂ) ε \ ({0} : Set ℂ) = ((U₁ ∪ U₂) ∪ U₃) ∪ U₄ := by
    ext z
    constructor
    · intro hz
      by_cases hre_pos : 0 < z.re
      · exact Or.inl <| Or.inl <| Or.inl ⟨hz.1, hre_pos⟩
      · by_cases him_pos : 0 < z.im
        · exact Or.inl <| Or.inl <| Or.inr ⟨hz.1, him_pos⟩
        · by_cases hre_neg : z.re < 0
          · exact Or.inl <| Or.inr ⟨hz.1, hre_neg⟩
          · by_cases him_neg : z.im < 0
            · exact Or.inr ⟨hz.1, him_neg⟩
            · exfalso
              have hz_re : z.re = 0 := by
                linarith [le_of_not_gt hre_pos, le_of_not_gt hre_neg]
              have hz_im : z.im = 0 := by
                linarith [le_of_not_gt him_pos, le_of_not_gt him_neg]
              have hz_eq : z = 0 := by
                apply Complex.ext <;> simp [hz_re, hz_im]
              exact hz.2 <| by simpa [Set.mem_singleton_iff] using hz_eq
    · intro hz
      rcases hz with hz | hz
      · rcases hz with hz | hz
        · rcases hz with hz | hz
          · exact ⟨hz.1, by
              simpa [Set.mem_singleton_iff] using fun hz0 ↦ by
                have : (0 : ℝ) < 0 := by simpa [hz0] using hz.2
                linarith⟩
          · exact ⟨hz.1, by
              simpa [Set.mem_singleton_iff] using fun hz0 ↦ by
                have : (0 : ℝ) < 0 := by simpa [hz0] using hz.2
                linarith⟩
        · exact ⟨hz.1, by
            simpa [Set.mem_singleton_iff] using fun hz0 ↦ by
              have : (0 : ℝ) < 0 := by simpa [hz0] using hz.2
              linarith⟩
      · exact ⟨hz.1, by
          simpa [Set.mem_singleton_iff] using fun hz0 ↦ by
            have : (0 : ℝ) < 0 := by simpa [hz0] using hz.2
            linarith⟩
  have hU_path : IsPathConnected (((U₁ ∪ U₂) ∪ U₃) ∪ U₄) := by
    exact hU₁₂₃_path.union hU₄_path ⟨c, Or.inr hcU₃, hcU₄⟩
  simpa [hcover] using hU_path
