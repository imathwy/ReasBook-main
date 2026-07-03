

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_36 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: unfold `standardizedPartialSum` for the shifted sequence `fun k ↦ X (k + 1)` and
-- rewrite the common mean and variance using `hμ` and `hσ2`.
/-- For the textbook sequence `X₁, X₂, …`, the chapter owner `standardizedPartialSum` is exactly
the CLT-normalized centered finite sum `(n σ²)^(-1/2) ∑_{k=1}^n (X_k - μ)`. -/
theorem standardizedPartialSum_succ_apply
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ σ2 : ℝ)
    (hμ : P[X 1] = μ) (hσ2 : Var[X 1; P] = σ2) (n : ℕ) (ω : Ω) :
    standardizedPartialSum P (fun k ↦ X (k + 1)) n ω =
      (Real.sqrt (n * σ2))⁻¹ * ∑ k ∈ Finset.range n, (X (k + 1) ω - μ) := sorry

-- Proof sketch: transfer Lemma 15.36 to the canonical pushforward law of
-- `standardizedPartialSum P (fun k ↦ X (k + 1)) n`. The companion theorem
-- `standardizedPartialSum_succ_apply` recovers the textbook `S_n^*` formula, while the owner
-- `ProbabilityMeasure.map` identifies the same law with the pushforward measure appearing below.
/-- Lemma 15.36: if `X₁, X₂, …` are i.i.d. real random variables with mean `μ` and variance
`σ² > 0`, then the characteristic functions of the normalized partial sums `S_n^*` converge
pointwise to the standard Gaussian characteristic function `t ↦ exp (-t² / 2)`. -/
theorem charFun_cltNormalizedPartialSum_tendsto_standardGaussian
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hVar : 0 < Var[X 1; P])
    (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) n)) t)
      atTop (𝓝 (Complex.exp (-(t ^ 2 / 2 : ℝ)))) := sorry
