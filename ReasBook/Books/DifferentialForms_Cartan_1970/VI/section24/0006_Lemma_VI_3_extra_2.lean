import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ComplexConjugate

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the complex-conjugation surface was checked directly against mathlib's `ComplexConjugate`
-- notation owner and local repository precedent.

/-- Lemma VI.3-extra-2: if two complex numbers `u` and `v` satisfy `u.re < 0` and `v.re < 0`,
then `‖(v - u) / (v + conj u)‖ < 1`. -/
theorem complex_abs_sub_div_add_conj_lt_one_of_re_neg
    {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0) :
    ‖(v - u) / (v + conj u)‖ < 1 := by
  have hden_re : (v + conj u).re < 0 := by
    simpa [Complex.add_re, Complex.conj_re] using add_lt_add hv hu
  have hden_ne : v + conj u ≠ 0 := by
    intro h
    have hzero : ¬ ((0 : ℂ).re < 0) := by simp
    exact hzero (h ▸ hden_re)
  have hnorm_lt : ‖v - u‖ < ‖v + conj u‖ := by
    have hsq_lt : ‖v - u‖ ^ 2 < ‖v + conj u‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.conj_re,
        Complex.conj_im]
      ring_nf
      nlinarith [hu, hv]
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq_lt
  rw [norm_div]
  exact (div_lt_one (norm_pos_iff.2 hden_ne)).2 hnorm_lt
