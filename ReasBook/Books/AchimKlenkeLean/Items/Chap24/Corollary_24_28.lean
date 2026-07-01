import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : ℕ}

/-- The terminal time `t_n = ∑_{j=1}^n θ_j` attached to the parameter vector `θ`. -/
def dirichletTerminalTime (θ : Fin n → NNReal) : NNReal :=
  ∑ i, θ i

/-- The cumulative times `t_i = ∑_{j=1}^i θ_j`, with `t_0 = 0`, attached to the parameter vector
`θ`. -/
def dirichletCumulativeTimes (θ : Fin n → NNReal) : Fin (n + 1) → NNReal :=
  fun i ↦
    ∑ j : Fin i.1,
      θ (Fin.castLT j (Nat.lt_of_lt_of_le j.2 (Nat.lt_succ_iff.mp i.2)))

/-- The increment `M_{t_i} - M_{t_{i-1}}` along the cumulative times determined by `θ`. -/
def gammaCumulativeIncrement
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) (i : Fin n) : Ω → ℝ :=
  fun ω ↦
    M (dirichletCumulativeTimes θ i.succ) ω -
      M (dirichletCumulativeTimes θ i.castSucc) ω

/-- The normalized increment vector
`((M_{t_i} - M_{t_{i-1}}) / M_{t_n})_{i=1}^n`. -/
def dirichletNormalizedIncrementVector
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) : Ω → Fin n → ℝ :=
  fun ω i ↦ gammaCumulativeIncrement θ M i ω / M (dirichletTerminalTime θ) ω

/-- The pair consisting of the normalized increment vector and the terminal value `M_{t_n}`. -/
def dirichletNormalizedIncrementPair
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) : Ω → (Fin n → ℝ) × ℝ :=
  fun ω ↦ (dirichletNormalizedIncrementVector θ M ω, M (dirichletTerminalTime θ) ω)

/-- The classical Dirichlet law on `Fin n → ℝ`, supported on the standard simplex, with parameter
vector `θ`. -/
def dirichletMeasure (θ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity fun x ↦
    ENNReal.ofReal <|
      Set.indicator (stdSimplex ℝ (Fin n))
        (fun y ↦
          (Real.Gamma (∑ i, θ i) / ∏ i, Real.Gamma (θ i)) *
            (∏ i, Real.rpow (y i) (θ i - 1)))
        x

-- Proof sketch: unfold `dirichletMeasure`; it is defined as Lebesgue measure on `Fin n → ℝ`
-- weighted by the standard Dirichlet density and restricted to the standard simplex via the
-- indicator factor.
/-- Unfolding `dirichletMeasure θ` gives the Dirichlet density on the standard simplex. -/
theorem dirichletMeasure_def (θ : Fin n → ℝ) :
    dirichletMeasure θ =
      volume.withDensity (fun x ↦
        ENNReal.ofReal <|
          Set.indicator (stdSimplex ℝ (Fin n))
            (fun y ↦
              (Real.Gamma (∑ i, θ i) / ∏ i, Real.Gamma (θ i)) *
                (∏ i, Real.rpow (y i) (θ i - 1)))
            x) := sorry

-- Proof sketch: unfold `dirichletNormalizedIncrementPair`; the two coordinates are, by
-- definition, the normalized increment vector and the terminal value `M_{t_n}`.
/-- Unfolding `dirichletNormalizedIncrementPair` recovers the pair `(X, S)` from the source
corollary. -/
theorem dirichletNormalizedIncrementPair_def
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) :
    dirichletNormalizedIncrementPair θ M =
      fun ω ↦
        (dirichletNormalizedIncrementVector θ M ω, M (dirichletTerminalTime θ) ω) := sorry

section Corollary2428

variable {P : ProbabilityMeasure Ω}
variable (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ)

-- Proof sketch: Theorem 24.27 gives independent Gamma increments with unit rate and shapes
-- `θ_i`. The classical Beta-Gamma / Dirichlet-Gamma factorization sends these increments to the
-- pair consisting of their normalized vector and their total sum, and `hM0` identifies that total
-- sum with `M_{t_n}` because the cumulative increments telescope.
/-- Corollary 24.28: if `t_i = ∑_{j=1}^i θ_j`, then the pair consisting of the normalized
increment vector `((M_{t_i} - M_{t_{i-1}}) / M_{t_n})_{i=1}^n` and the terminal value `M_{t_n}`
has the product law `Dir_{θ_1,\dots,θ_n} ⊗ Γ_{1,t_n}`. This product-law statement packages the
independence of `X` and `S` together with their two marginal distributions. -/
theorem gammaSubordinator_normalizedIncrementPair_hasLaw_dirichlet_prod_gamma
    (hM0 : ∀ ω, M 0 ω = 0)
    (h_indep : iIndepFun (fun i ↦ gammaCumulativeIncrement θ M i) (P : Measure Ω))
    (h_law : ∀ i,
      HasLaw (gammaCumulativeIncrement θ M i)
        (ProbabilityTheory.gammaMeasure (θ i : ℝ) 1) (P : Measure Ω)) :
    HasLaw (dirichletNormalizedIncrementPair θ M)
      ((dirichletMeasure fun i ↦ (θ i : ℝ)).prod
        (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1))
      (P : Measure Ω) := sorry

-- Proof sketch: project the first coordinate of the product-law statement for
-- `dirichletNormalizedIncrementPair`.
/-- The normalized increment vector has Dirichlet law with parameter vector `θ`. -/
theorem gammaSubordinator_normalizedIncrementVector_hasLaw_dirichlet
    (hM0 : ∀ ω, M 0 ω = 0)
    (h_indep : iIndepFun (fun i ↦ gammaCumulativeIncrement θ M i) (P : Measure Ω))
    (h_law : ∀ i,
      HasLaw (gammaCumulativeIncrement θ M i)
        (ProbabilityTheory.gammaMeasure (θ i : ℝ) 1) (P : Measure Ω)) :
    HasLaw (dirichletNormalizedIncrementVector θ M)
      (dirichletMeasure fun i ↦ (θ i : ℝ))
      (P : Measure Ω) := sorry

-- Proof sketch: project the second coordinate of the product-law statement for
-- `dirichletNormalizedIncrementPair`.
/-- The terminal value `M_{t_n}` has Gamma law `Γ_{1,t_n}`. -/
theorem gammaSubordinator_terminalValue_hasLaw_gamma
    (hM0 : ∀ ω, M 0 ω = 0)
    (h_indep : iIndepFun (fun i ↦ gammaCumulativeIncrement θ M i) (P : Measure Ω))
    (h_law : ∀ i,
      HasLaw (gammaCumulativeIncrement θ M i)
        (ProbabilityTheory.gammaMeasure (θ i : ℝ) 1) (P : Measure Ω)) :
    HasLaw (fun ω ↦ M (dirichletTerminalTime θ) ω)
      (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1)
      (P : Measure Ω) := sorry

-- Proof sketch: the main product-law statement implies that the two coordinates of
-- `dirichletNormalizedIncrementPair` are independent.
/-- The normalized increment vector and the terminal value `M_{t_n}` are independent. -/
theorem gammaSubordinator_normalizedIncrementVector_indep_terminalValue
    (hM0 : ∀ ω, M 0 ω = 0)
    (h_indep : iIndepFun (fun i ↦ gammaCumulativeIncrement θ M i) (P : Measure Ω))
    (h_law : ∀ i,
      HasLaw (gammaCumulativeIncrement θ M i)
        (ProbabilityTheory.gammaMeasure (θ i : ℝ) 1) (P : Measure Ω)) :
    IndepFun (dirichletNormalizedIncrementVector θ M)
      (fun ω ↦ M (dirichletTerminalTime θ) ω)
      (P : Measure Ω) := sorry

end Corollary2428

end ProbabilityTheory
