import ProbabilityTheory_Klenke_2020.Chap11.Theorem_11_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- Extends a discrete filtration by adjoining `ℱ∞ = ⨆ n, ℱ n` at time `∞`. -/
def withInfinityFiltration (ℱ : Filtration ℕ mΩ) : Filtration ℕ∞ mΩ where
  seq := ENat.recTopCoe (⨆ k, ℱ k) ℱ
  mono' := by
    -- Proof sketch: if `i ≤ j` in `ℕ∞`, then either `j = ∞`, in which case the value at `j`
    -- is `⨆ n, ℱ n`, or both indices are finite and monotonicity reduces to the monotonicity
    -- of `ℱ` on `ℕ`.
    sorry
  le' := by
    -- Proof sketch: for finite indices the claim is `ℱ n ≤ mΩ`; at `∞` it follows because
    -- every `ℱ n` is below `mΩ`, hence so is their supremum.
    sorry

variable {ℱ : Filtration ℕ mΩ} {μ : Measure Ω}

-- `ENat.recTopCoe` together with `withInfinityFiltration` is the bridge/view layer for
-- Remark 11.8. The source-facing statements below specialize the terminal value to the canonical
-- one already produced by Theorem 11.7.
/-- If a discrete-time process is strongly adapted to `ℱ` and its terminal value is
`⨆ n, ℱ n`-strongly measurable, then adjoining that terminal value yields a process strongly
adapted to the filtration extended by `∞`. -/
private theorem withInfinityProcess_stronglyAdapted
    {E : Type v} [TopologicalSpace E] {X : ℕ → Ω → E} {Xinf : Ω → E}
    (hadp : StronglyAdapted ℱ X) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf) :
    StronglyAdapted (withInfinityFiltration ℱ)
      (show ℕ∞ → Ω → E from ENat.recTopCoe Xinf X) := sorry

-- Proof sketch: use the given finite-time strong adaptedness together with `ℱ∞`-measurability
-- of `X∞`; for `i ≤ j`, the finite-finite cases come from the tower rule, the finite-`∞` cases
-- are exactly the assumed identities, and the `∞`-`∞` case is `condExp_of_stronglyMeasurable`.
private theorem withInfinityProcess_martingale_of_ae_eq_condExp
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : ℕ → Ω → E} {Xinf : Ω → E}
    (hadp : StronglyAdapted ℱ X) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf)
    (hXinfint : Integrable Xinf μ)
    (hcond : ∀ n : ℕ, μ[Xinf | ℱ n] =ᵐ[μ] X n) :
    Martingale
      (show ℕ∞ → Ω → E from ENat.recTopCoe Xinf X)
      (withInfinityFiltration ℱ) μ := sorry

-- Proof sketch: combine the given finite-time strong adaptedness with `ℱ∞`-measurability of
-- `X∞`, use the assumed inequalities for the finite-`∞` comparisons, obtain the finite-finite
-- comparisons from the tower property of conditional expectation, and use
-- `condExp_of_stronglyMeasurable` at `∞`.
private theorem withInfinityProcess_submartingale_of_ae_le_condExp
    {X : ℕ → Ω → ℝ} {Xinf : Ω → ℝ}
    (hadp : StronglyAdapted ℱ X) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf)
    (hXinfint : Integrable Xinf μ)
    (hXint : ∀ n : ℕ, Integrable (X n) μ) (hcond : ∀ n : ℕ, X n ≤ᵐ[μ] μ[Xinf | ℱ n]) :
    Submartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe Xinf X)
      (withInfinityFiltration ℱ) μ := sorry

-- Proof sketch: the argument is the order-reversed version of the submartingale case, using the
-- given finite-time strong adaptedness together with measurability of `X∞` at time `∞`; the
-- finite-`∞` inequalities are supplied by the hypotheses and the remaining cases come from the
-- tower property.
private theorem withInfinityProcess_supermartingale_of_ae_ge_condExp
    {X : ℕ → Ω → ℝ} {Xinf : Ω → ℝ}
    (hadp : StronglyAdapted ℱ X) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf)
    (hXinfint : Integrable Xinf μ)
    (hXint : ∀ n : ℕ, Integrable (X n) μ) (hcond : ∀ n : ℕ, μ[Xinf | ℱ n] ≤ᵐ[μ] X n) :
    Supermartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe Xinf X)
      (withInfinityFiltration ℱ) μ := sorry

section Real

variable {X : ℕ → Ω → ℝ}
variable [IsFiniteMeasure μ]

local notation "supermartingaleLimit" => fun ω ↦ -(ℱ.limitProcess (-X) μ ω)

/-- Remark 11.8 for martingales: adjoining the canonical terminal random variable
`ℱ.limitProcess X μ` from Theorem 11.7 turns `(X n)ₙ` into a martingale on `ℕ∞` for the
filtration extended by `ℱ∞ = ⨆ n, ℱ n`. -/
theorem withInfinityProcess_martingale
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Martingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe (ℱ.limitProcess X μ) X)
      (withInfinityFiltration ℱ) μ := by
  simpa using withInfinityProcess_martingale_of_ae_eq_condExp
    hX.stronglyAdapted
    stronglyMeasurable_limitProcess
    (submartingale_integrable_limitProcess_of_uniformIntegrable hX.submartingale hUI)
    (fun n ↦ (hX.ae_eq_condExp_limitProcess hUI n).symm)

/-- Remark 11.8 for submartingales: adjoining the canonical terminal random variable
`ℱ.limitProcess X μ` from Theorem 11.7 turns `(X n)ₙ` into a submartingale on `ℕ∞` for the
filtration extended by `ℱ∞ = ⨆ n, ℱ n`. -/
theorem withInfinityProcess_submartingale
    (hX : Submartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Submartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe (ℱ.limitProcess X μ) X)
      (withInfinityFiltration ℱ) μ := by
  simpa using withInfinityProcess_submartingale_of_ae_le_condExp
    hX.stronglyAdapted
    stronglyMeasurable_limitProcess
    (submartingale_integrable_limitProcess_of_uniformIntegrable hX hUI)
    hX.integrable
    (submartingale_ae_le_condExp_limitProcess_of_uniformIntegrable hX hUI)

/-- Remark 11.8 for supermartingales: adjoining the canonical terminal random variable
`ω ↦ -ℱ.limitProcess (-X) μ ω` from Theorem 11.7 turns `(X n)ₙ` into a supermartingale on `ℕ∞`
for the filtration extended by `ℱ∞ = ⨆ n, ℱ n`. -/
theorem withInfinityProcess_supermartingale
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Supermartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe supermartingaleLimit X)
      (withInfinityFiltration ℱ) μ := by
  simpa using withInfinityProcess_supermartingale_of_ae_ge_condExp
    hX.stronglyAdapted
    supermartingale_stronglyMeasurable_limitProcess
    (supermartingale_integrable_limitProcess_of_uniformIntegrable hX hUI)
    hX.integrable
    (supermartingale_ae_ge_condExp_limit_of_uniformIntegrable hX hUI)

end Real
