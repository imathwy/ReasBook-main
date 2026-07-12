import Mathlib

noncomputable section

/-- Helper for Cartan section12 0038_Exercise_25: the literal rational evaluation
`z ↦ p.eval z / q.eval z` is meromorphic on the whole complex plane. -/
lemma exercise25_rationalEval_meromorphicOn_univ
    (p q : Polynomial ℂ) :
    MeromorphicOn (fun w : ℂ ↦ p.eval w / q.eval w) Set.univ := by
  have hpmer : MeromorphicOn (fun w : ℂ ↦ p.eval w) Set.univ := by
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) p).meromorphicOn
  have hqmer : MeromorphicOn (fun w : ℂ ↦ q.eval w) Set.univ := by
    simpa [Polynomial.coe_aeval_eq_eval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) q).meromorphicOn
  simpa using hpmer.div hqmer

/-- Helper for Cartan section12 0038_Exercise_25: the meromorphic normal form of a
rational function is holomorphic away from the prescribed pole finset. -/
lemma exercise25_rationalNormalForm_differentiableOn_compl_poleFinset
    (p q : Polynomial ℂ) (s : Finset ℂ)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w : ℂ ↦ p.eval w / q.eval w) z < 0 ↔ z ∈ s) :
    DifferentiableOn ℂ
      (toMeromorphicNFOn (fun w : ℂ ↦ p.eval w / q.eval w) Set.univ)
      (↑s : Set ℂ)ᶜ := by
  intro z hz
  let f : ℂ → ℂ := fun w : ℂ ↦ p.eval w / q.eval w
  have hmeromorphic : MeromorphicOn f Set.univ :=
    exercise25_rationalEval_meromorphicOn_univ p q
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    by_contra hneg
    exact hz ((hpoles z).1 (lt_of_not_ge hneg))
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f Set.univ) z := by
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hmeromorphic (by simp)]
    exact horder_nonneg_f
  have hnf : MeromorphicNFAt (toMeromorphicNFOn f Set.univ) z :=
    (meromorphicNFOn_toMeromorphicNFOn f Set.univ) (by simp)
  have hdiffAt : DifferentiableAt ℂ (toMeromorphicNFOn f Set.univ) z := by
    exact (hnf.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).differentiableAt
  exact hdiffAt.differentiableWithinAt
