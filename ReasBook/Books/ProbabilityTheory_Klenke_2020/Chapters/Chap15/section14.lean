import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_14 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory

universe u

noncomputable section

/-- The complex-valued analogue of Chapter 3's `probabilityGeneratingSeries`, evaluated at `z`. -/
noncomputable def probabilityGeneratingSeriesComplex (μ : Measure ℕ) (z : ℂ) : ℂ :=
  tsum (fun n : ℕ ↦ (μ {n}).toReal * z ^ n)

/-- The complex-valued probability generating series is given by its defining `tsum`. -/
-- Proof sketch: unfold `probabilityGeneratingSeriesComplex`.
theorem probabilityGeneratingSeriesComplex_apply (μ : Measure ℕ) (z : ℂ) :
    probabilityGeneratingSeriesComplex μ z = tsum (fun n : ℕ ↦ (μ {n}).toReal * z ^ n) := rfl

/-- On real inputs, the complex probability generating series is the Chapter 3 owner
`probabilityGeneratingSeries`, viewed in `ℂ`. -/
theorem probabilityGeneratingSeriesComplex_ofReal (μ : Measure ℕ) (z : ℝ) :
    probabilityGeneratingSeriesComplex μ z = probabilityGeneratingSeries μ z := by
  simpa [probabilityGeneratingSeriesComplex, probabilityGeneratingSeries] using
    (Complex.ofReal_tsum (fun n : ℕ ↦ (μ {n}).toReal * z ^ n)).symm

/-- The random sum `ω ↦ ∑_{i=1}^{N(ω)} X_i(ω)` for a textbook-style sequence `X 1, X 2, …`. -/
noncomputable def randomFiniteSum {Ω : Type u} {d : ℕ}
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Ω → EuclideanSpace ℝ (Fin d) :=
  fun ω ↦ Finset.sum (Finset.Icc 1 (N ω)) (fun i ↦ X i ω)

/-- The random finite sum agrees with the textbook finite sum over `Icc 1 (N ω)`. -/
-- Proof sketch: unfold `randomFiniteSum`.
theorem randomFiniteSum_def {Ω : Type u} {d : ℕ}
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) :
    randomFiniteSum N X = fun ω ↦ Finset.sum (Finset.Icc 1 (N ω)) (fun i ↦ X i ω) := rfl

/-- Theorem 15.14 (1): a countable nonnegative weighted sum of finite measures on `ℝ^d` has
characteristic function equal to the corresponding weighted sum of the individual characteristic
functions. -/
-- Proof sketch: treat `Measure.sum (fun n ↦ (p n : ENNReal) • μ n)` as the canonical countable
-- weighted measure sum, use linearity of the integral on finite partial sums, and pass to the
-- limit through the weighted total-mass finiteness assumption.
theorem charFun_weighted_measure_sum_eq_tsum {d : ℕ}
    (p : ℕ → NNReal) (μ : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    (hμfin : ∀ n, (μ n) Set.univ ≠ ⊤)
    (hfin : tsum (fun n : ℕ ↦ ((p n : ENNReal) * ((μ n) Set.univ))) ≠ ⊤)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun (Measure.sum (fun n ↦ ((p n : ENNReal) • μ n))) t =
      tsum (fun n : ℕ ↦ (((p n : ℝ) : ℂ) * charFun (μ n) t)) := sorry

/-- Theorem 15.14 (2): if `N` is independent of the whole sequence `X₁, X₂, …`, the sequence is
independent and identically distributed on `ℝ^d`, and `Y = ∑_{i=1}^N X_i`, then the characteristic
function of `Y` is the complex probability generating series of the counting law `P.map N`
evaluated at the common characteristic function of `X₁`. -/
-- Proof sketch: condition on the event `{N = n}`, identify the conditional characteristic
-- function with that of the finite sum `∑_{i=1}^n X_i`, use independence and identical
-- distribution to rewrite it as `charFun (P.map (X 1)) t ^ n`, and sum over `n`.
theorem charFun_randomFiniteSum_eq_complex_pgf {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hN_seq_indep : IndepFun N (fun ω n ↦ X (n + 1) ω) P)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun (P.map (randomFiniteSum N X)) t =
      probabilityGeneratingSeriesComplex (P.map N) (charFun (P.map (X 1)) t) := sorry

/-- Theorem 15.14 (3): if the counting variable in part (2) has Poisson law `Poi_λ`, then the
characteristic function of the random finite sum is `exp (λ (φ_X(t) - 1))`. -/
-- Proof sketch: combine `charFun_randomFiniteSum_eq_complex_pgf` with the closed formula for the
-- Poisson probability generating series and rewrite `P.map N` using the `HasLaw` hypothesis.
theorem charFun_randomFiniteSum_eq_poisson_exponential {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (lam : NNReal)
    (hN : HasLaw N (poissonMeasure lam) P)
    (hN_seq_indep : IndepFun N (fun ω n ↦ X (n + 1) ω) P)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (t : EuclideanSpace ℝ (Fin d)) :
    charFun (P.map (randomFiniteSum N X)) t =
      Complex.exp (((lam : ℝ) : ℂ) * (charFun (P.map (X 1)) t - (1 : ℂ))) := sorry
