import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_11_7 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {μ : Measure Ω}
variable {X : ℕ → Ω → ℝ}

local notation "supermartingaleLimit" => fun ω ↦ -(ℱ.limitProcess (-X) μ ω)

private theorem uniformIntegrable_neg
    (hUI : UniformIntegrable X 1 μ) :
    UniformIntegrable (-X) 1 μ := by
  rcases hUI with ⟨hX_meas, hX_unif, hX_bdd⟩
  rcases hX_bdd with ⟨C, hC⟩
  refine ⟨fun n ↦ (hX_meas n).neg, hX_unif.neg, ⟨C, fun n ↦ ?_⟩⟩
  simpa using hC n

/- Theorem 11.7 (1) for martingales and submartingales uses the owner-level declaration that the
canonical limit process `ℱ.limitProcess X μ` is `⨆ n, ℱ n`-strongly measurable. -/
recall MeasureTheory.Filtration.stronglyMeasurable_limitProcess

/-- Theorem 11.7 (1) for supermartingales: the canonical limit random variable
`ω ↦ -ℱ.limitProcess (-X) μ ω` is `⨆ n, ℱ n`-strongly measurable. -/
theorem supermartingale_stronglyMeasurable_limitProcess
    : StronglyMeasurable[⨆ n, ℱ n] supermartingaleLimit := by
  have h_limit : StronglyMeasurable[⨆ n, ℱ n] (ℱ.limitProcess (-X) μ) :=
    stronglyMeasurable_limitProcess
  change StronglyMeasurable[⨆ n, ℱ n] (fun ω ↦ -(ℱ.limitProcess (-X) μ ω))
  simpa using h_limit.neg

variable [IsFiniteMeasure μ]

/-- Theorem 11.7 (2) for submartingales; the martingale case is the specialization
`hX.submartingale`. -/
theorem submartingale_integrable_limitProcess_of_uniformIntegrable
    (hX : Submartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Integrable (ℱ.limitProcess X μ) μ := by
  obtain ⟨R, hR⟩ := hUI.2.2
  exact (hX.memLp_limitProcess hR).integrable le_rfl

/-- Theorem 11.7 (2) for supermartingales: the canonical limit random variable
`ω ↦ -ℱ.limitProcess (-X) μ ω` is integrable. -/
theorem supermartingale_integrable_limitProcess_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Integrable supermartingaleLimit μ := by
  have h_limit :
      Integrable (ℱ.limitProcess (-X) μ) μ :=
    submartingale_integrable_limitProcess_of_uniformIntegrable hX.neg
      (uniformIntegrable_neg hUI)
  change Integrable (fun ω ↦ -(ℱ.limitProcess (-X) μ ω)) μ
  simpa using h_limit.neg

/- Theorem 11.7 (3) for submartingales, and hence also for martingales, is exactly the
owner-level convergence theorem to `ℱ.limitProcess X μ`. -/
recall MeasureTheory.Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable

/-- Theorem 11.7 (3) for supermartingales: apply the owner theorem to `-X` and negate the limit. -/
theorem supermartingale_ae_tendsto_limitProcess_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (supermartingaleLimit ω)) := by
  have h_neg_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ -X n ω) atTop (𝓝 (ℱ.limitProcess (-X) μ ω)) :=
    hX.neg.ae_tendsto_limitProcess_of_uniformIntegrable (uniformIntegrable_neg hUI)
  filter_upwards [h_neg_tendsto] with ω hω
  simpa using hω.neg

/- Theorem 11.7 (4) for submartingales, and hence also for martingales, is exactly the
owner-level `L¹` convergence theorem to `ℱ.limitProcess X μ`. -/
recall MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess

/-- Theorem 11.7 (4) for supermartingales: `X` converges in `L¹` to
`ω ↦ -ℱ.limitProcess (-X) μ ω`. -/
theorem supermartingale_tendsto_eLpNorm_one_limitProcess_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Tendsto (fun n ↦ eLpNorm (X n - supermartingaleLimit) 1 μ) atTop (𝓝 0) := by
  have h_neg_tendsto :
      Tendsto (fun n ↦ eLpNorm (-X n - ℱ.limitProcess (-X) μ) 1 μ) atTop (𝓝 0) :=
    hX.neg.tendsto_eLpNorm_one_limitProcess (uniformIntegrable_neg hUI)
  have h_eq :
      (fun n ↦ eLpNorm (X n - supermartingaleLimit) 1 μ) =
        fun n ↦ eLpNorm (-X n - ℱ.limitProcess (-X) μ) 1 μ := by
    funext n
    calc
      eLpNorm (X n - supermartingaleLimit) 1 μ =
          eLpNorm (-(-X n - ℱ.limitProcess (-X) μ)) 1 μ := by
            refine eLpNorm_congr_ae (.of_forall fun ω ↦ ?_)
            simp [sub_eq_add_neg, add_comm]
      _ = eLpNorm (-X n - ℱ.limitProcess (-X) μ) 1 μ := by
            rw [eLpNorm_neg]
  rw [h_eq]
  exact h_neg_tendsto

/- In the martingale case, the textbook conditional-expectation identity is exactly the canonical
mathlib statement `MeasureTheory.Martingale.ae_eq_condExp_limitProcess`, with the limit random
variable given by `ℱ.limitProcess X μ`. -/
recall MeasureTheory.Martingale.ae_eq_condExp_limitProcess

-- Proof sketch: combine the `L¹` convergence of `X` to `ℱ.limitProcess X μ` with continuity of
-- conditional expectation in `L¹`, then pass to the limit in the submartingale inequalities
-- `X n ≤ 𝔼[X m | ℱ n]` for `m ≥ n`.
/-- For a uniformly integrable submartingale, each time slice is almost surely bounded above by the
conditional expectation of the canonical limit process. -/
theorem submartingale_ae_le_condExp_limitProcess_of_uniformIntegrable
    (hX : Submartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) (n : ℕ) :
    X n ≤ᵐ[μ] μ[ℱ.limitProcess X μ | ℱ n] := sorry

-- Proof sketch: apply the previous submartingale result to `-X`, identify the limiting random
-- variable of `-X` with `fun ω ↦ -ℱ.limitProcess (-X) μ ω`, and rewrite the conditional
-- expectation using `condExp_neg`.
/-- For a uniformly integrable supermartingale, each time slice is almost surely bounded below by
the conditional expectation of its canonical limit random variable. -/
theorem supermartingale_ae_ge_condExp_limit_of_uniformIntegrable
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) (n : ℕ) :
    μ[fun ω ↦ -ℱ.limitProcess (-X) μ ω | ℱ n] ≤ᵐ[μ] X n := by
  have h_neg_le :
      -X n ≤ᵐ[μ] μ[ℱ.limitProcess (-X) μ | ℱ n] :=
    submartingale_ae_le_condExp_limitProcess_of_uniformIntegrable hX.neg
      (uniformIntegrable_neg hUI) n
  have h_neg_ge :
      -μ[ℱ.limitProcess (-X) μ | ℱ n] ≤ᵐ[μ] X n :=
    h_neg_le.mono fun ω hω ↦ by
      simpa using neg_le_neg hω
  exact (condExp_neg (ℱ.limitProcess (-X) μ) (ℱ n)).le.trans h_neg_ge
