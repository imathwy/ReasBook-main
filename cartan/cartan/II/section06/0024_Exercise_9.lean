import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex

/-- Exercise 9: if `f` is holomorphic on a convex open set `D ⊆ ℂ`, then for any `a, b ∈ D`
there are points `c` and `d` on the segment joining `a` and `b` such that `f a - f b` equals
`(a - b)` times the real part of `f'` at `c` plus `I` times the imaginary part of `f'` at `d`. -/
-- Proof sketch: parameterize the segment from `b` to `a` by the real variable
-- `t ↦ b + (a - b) * t`, apply the real mean value theorem to the real and imaginary parts of the
-- normalized function `t ↦ f (b + (a - b) * t) / (a - b)`, and then rewrite the resulting points
-- as elements of `segment ℝ a b`.
theorem sub_eq_mul_re_deriv_add_im_deriv_on_segment
    {D : Set ℂ} {f : ℂ → ℂ} (hD_convex : Convex ℝ D) (hD_open : IsOpen D)
    (hf : DifferentiableOn ℂ f D) {a b : ℂ} (ha : a ∈ D) (hb : b ∈ D) :
    ∃ c ∈ segment ℝ a b, ∃ d ∈ segment ℝ a b,
      f a - f b =
        (a - b) * (((deriv f c).re : ℂ) + Complex.I * ((deriv f d).im : ℂ)) := by
  by_cases hab : a = b
  · subst hab
    refine ⟨a, left_mem_segment ℝ a a, a, left_mem_segment ℝ a a, by simp⟩
  · let u : ℂ → ℝ := fun z ↦ (f z / (a - b)).re
    let v : ℂ → ℝ := fun z ↦ (f z / (a - b)).im
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hu :
        ∀ z ∈ D,
          HasFDerivWithinAt u
            (Complex.reCLM.comp (((derivWithin f D z) / (a - b)) • (1 : ℂ →L[ℝ] ℂ))) D z := by
      intro z hz
      simpa [u] using
        reCLM.hasFDerivAt.comp_hasFDerivWithinAt z
          (((hf z hz).hasDerivWithinAt.div_const (a - b)).complexToReal_fderiv)
    have hv :
        ∀ z ∈ D,
          HasFDerivWithinAt v
            (Complex.imCLM.comp (((derivWithin f D z) / (a - b)) • (1 : ℂ →L[ℝ] ℂ))) D z := by
      intro z hz
      simpa [v] using
        imCLM.hasFDerivAt.comp_hasFDerivWithinAt z
          (((hf z hz).hasDerivWithinAt.div_const (a - b)).complexToReal_fderiv)
    obtain ⟨c, hc, hre⟩ := domain_mvt hu hD_convex hb ha
    obtain ⟨d, hd, him⟩ := domain_mvt hv hD_convex hb ha
    have hcD : c ∈ D := hD_convex.segment_subset hb ha hc
    have hdD : d ∈ D := hD_convex.segment_subset hb ha hd
    have hc' : c ∈ segment ℝ a b := by simpa [segment_symm] using hc
    have hd' : d ∈ segment ℝ a b := by simpa [segment_symm] using hd
    have hre' : u a - u b = (deriv f c).re := by
      calc
        u a - u b =
            (Complex.reCLM.comp (((derivWithin f D c) / (a - b)) • (1 : ℂ →L[ℝ] ℂ))) (a - b) := hre
        _ =
            (Complex.reCLM.comp (((deriv f c) / (a - b)) • (1 : ℂ →L[ℝ] ℂ))) (a - b) := by
              rw [derivWithin_of_mem_nhds (hD_open.mem_nhds hcD)]
        _ = (deriv f c).re := by
              simp [ContinuousLinearMap.comp_apply, hne, div_eq_mul_inv]
    have him' : v a - v b = (deriv f d).im := by
      calc
        v a - v b =
            (Complex.imCLM.comp (((derivWithin f D d) / (a - b)) • (1 : ℂ →L[ℝ] ℂ))) (a - b) := him
        _ =
            (Complex.imCLM.comp (((deriv f d) / (a - b)) • (1 : ℂ →L[ℝ] ℂ))) (a - b) := by
              rw [derivWithin_of_mem_nhds (hD_open.mem_nhds hdD)]
        _ = (deriv f d).im := by
              simp [ContinuousLinearMap.comp_apply, hne, div_eq_mul_inv]
    have hquot :
        f a / (a - b) - f b / (a - b) =
          (((deriv f c).re : ℂ) + Complex.I * ((deriv f d).im : ℂ)) := by
      apply Complex.ext
      · simpa [u] using hre'
      · simpa [v] using him'
    refine ⟨c, hc', d, hd', ?_⟩
    calc
      f a - f b = (a - b) * (f a / (a - b) - f b / (a - b)) := by
        field_simp [hne]
      _ = (a - b) * (((deriv f c).re : ℂ) + Complex.I * ((deriv f d).im : ℂ)) := by
        exact congrArg (fun z : ℂ ↦ (a - b) * z) hquot
