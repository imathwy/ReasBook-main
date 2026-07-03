import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_1 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/- Definition 5.1 (1): For an integrable real random variable, the textbook expectation or mean
`𝔼[X] = ∫ X dP` is the canonical Bochner integral, written in Lean as `μ[X] = ∫ ω, X ω ∂μ`. -/
recall MeasureTheory.integral

/-- A real random variable is centered if it is integrable and its expectation is zero. -/
def IsCentered (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Integrable X μ ∧ μ[X] = 0

/- Definition 5.1 (2): The textbook kth moment `m_k = 𝔼[X^k]` is the canonical moment
`ProbabilityTheory.moment X k μ = μ[X ^ k]`; the kth absolute moment is the expectation of
`|X|^k`. -/
recall ProbabilityTheory.moment

/-- The kth absolute moment of a real random variable. -/
def absoluteMoment (X : Ω → ℝ) (k : ℕ) (μ : Measure Ω) : ℝ :=
  moment (fun ω ↦ |X ω|) k μ

/-- The kth absolute moment is the expectation of `|X|^k`. -/
theorem absoluteMoment_eq_expectation_abs_pow (X : Ω → ℝ) (k : ℕ) (μ : Measure Ω) :
    absoluteMoment X k μ = μ[fun ω ↦ |X ω| ^ k] := by
  simp [absoluteMoment, moment_def]

/- Definition 5.1 (3): The textbook variance is the canonical quantity `Var[X; μ]`. -/
recall ProbabilityTheory.variance

/- On a probability space and for square-integrable `X`, mathlib also provides the textbook formula
`Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2`. -/
recall ProbabilityTheory.variance_eq_sub

/-- The standard deviation of a real random variable is the square root of its variance. -/
def standardDeviation (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  Real.sqrt (Var[X; μ])

/- Definition 5.1 (4): The textbook covariance is the canonical quantity `cov[X, Y; μ] =
∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ`; two square-integrable random variables are uncorrelated when
this covariance is zero. -/
recall ProbabilityTheory.covariance

/-- Two real random variables are uncorrelated if they are square integrable and their covariance
vanishes. -/
def IsUncorrelated (X Y : Ω → ℝ) (μ : Measure Ω) : Prop :=
  MemLp X 2 μ ∧ MemLp Y 2 μ ∧ cov[X, Y; μ] = 0

/-- For square-integrable real random variables, failing to be uncorrelated means that the
covariance is nonzero. -/
theorem not_isUncorrelated_iff {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ¬ IsUncorrelated X Y μ ↔ cov[X, Y; μ] ≠ 0 := by
  simp [IsUncorrelated, hX, hY]

/-! ### Exercise_5_1_1 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable section

-- Proof sketch: upgrade the explicit density law to the canonical `HasPDF` statement, rewrite the
-- canonical pdf as `f` almost everywhere using `eq_of_map_eq_withDensity`, and then invoke the
-- owner LOTUS theorem `pdf.integral_mul_eq_integral`.
/-- Exercise 5.1.1 in textbook density form: if the law of `X` is `volume.withDensity f`, then its
expectation is the Lebesgue integral of `x ↦ x f(x)`. -/
theorem expectation_eq_integral_mul_density {X : Ω → ℝ} {f : ℝ → ℝ≥0}
    (hf : Measurable f)
    (hX_law : HasLaw X ((volume : Measure ℝ).withDensity (fun x ↦ (f x : ℝ≥0∞))) P) :
    P[X] = ∫ x, x * (f x : ℝ) ∂(volume : Measure ℝ) := by
  haveI : HasPDF X P :=
    hasPDF_of_map_eq_withDensity hX_law.aemeasurable
      (fun x : ℝ ↦ (f x : ℝ≥0∞)) hf.aemeasurable.coe_nnreal_ennreal hX_law.map_eq
  have hpdf : pdf X P volume =ᵐ[volume] fun x ↦ (f x : ℝ≥0∞) :=
    (pdf.eq_of_map_eq_withDensity (fun x : ℝ ↦ (f x : ℝ≥0∞))
      hf.aemeasurable.coe_nnreal_ennreal).1 hX_law.map_eq
  have hlotus :
      ∫ x : ℝ, x * (pdf X P volume x).toReal ∂(volume : Measure ℝ) = ∫ ω, X ω ∂P :=
    pdf.integral_mul_eq_integral
  calc
    P[X] = ∫ x, x * (pdf X P volume x).toReal ∂(volume : Measure ℝ) :=
      by simpa using hlotus.symm
    _ = ∫ x, x * (f x : ℝ) ∂(volume : Measure ℝ) := by
      refine integral_congr_ae ?_
      filter_upwards [hpdf] with x hx
      simp [hx]

/-! ### Exercise_5_1_2 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: rewrite the moment integral against `betaMeasure r s` as the Beta integral with
-- parameters `r + n` and `s`.
private lemma integral_pow_eq_beta_ratio_betaMeasure
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    ∫ x, x ^ n ∂betaMeasure r s = beta (r + n) s / beta r s := sorry

-- Proof sketch: unfold `beta` in terms of Gamma functions and use the Gamma recurrence to convert
-- the beta-function ratio into the finite product.
private lemma beta_ratio_eq_prod (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    beta (r + n) s / beta r s = ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := sorry

-- Proof sketch: transport the canonical beta-ratio moment formula for `betaMeasure r s` along
-- `HasLaw.integral_comp`, then rewrite the ratio with `beta_ratio_eq_prod`.
/-- Exercise 5.1.2: If a real random variable has Beta law with parameters `r, s > 0`, then its
`n`th moment is `∏_{k=0}^{n-1} (r + k) / (r + s + k)`. -/
theorem beta_moment_formula (r s : ℝ) (hr : 0 < r) (hs : 0 < s) {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (betaMeasure r s) P) (n : ℕ) :
    P[fun ω ↦ X ω ^ n] = ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := sorry

/-! ### Exercise_5_1_3 (from Items/Chap05) -/
open Filter MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
variable (hX_iid : IsIID (fun n ↦ X (n + 1)) P)

-- Proof sketch: `ProbabilityTheory.strong_law_ae_real` is the canonical strong-law owner for
-- integrable i.i.d. real random variables. Applied to `fun n ↦ X (n + 1)`, it gives almost-sure
-- convergence of the Cesaro averages to `P[X 1]`; subtracting this from the strong law for the
-- constant sequence `fun _ _ ↦ P[X 1]` yields `X (n + 1) / (n + 1) → 0` almost surely, so the
-- `EReal` limsup is `0`. Thus the textbook nonnegativity assumption is redundant for this
-- consequence and is omitted from the Lean interface.
/-- Exercise 5.1.3 (1): the source-facing limsup conclusion is a canonical consequence of the
strong law for integrable i.i.d. real random variables, so the normalized sequence `Xₙ / n`,
represented in Lean by the terms `X 1 / 1, X 2 / 2, …`, has almost-sure limsup `0` without any
extra nonnegativity hypothesis. -/
theorem ae_limsup_normalized_iid_eq_zero_of_integrable
    (hX1_integrable : Integrable (X 1) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop = 0 := sorry

-- Proof sketch: for every `M > 0`, consider the events
-- `{ω | X (n + 1) ω / (n + 1) ≥ M}`. The tail
-- expectation criterion for nonnegative random variables together with identical distribution
-- gives divergence of the probability series, equivalently `¬ Integrable (X 1) P` under the
-- source-facing hypothesis `0 ≤ᵐ[P] X 1`. Since `hX_iid : IsIID (fun n ↦ X (n + 1)) P`, this
-- one-coordinate nonnegativity propagates to every `X (n + 1)` via `hX_iid.identDistrib n 0`.
-- Independence then lets the second Borel-Cantelli lemma force these events to occur infinitely
-- often almost surely. Then let `M → ∞`.
/-- Exercise 5.1.3 (2): For i.i.d. nonnegative real random variables with infinite nonnegative
expectation, it is enough to assume the source-facing condition `0 ≤ᵐ[P] X 1`, since the
chapter's canonical i.i.d. abstraction `IsIID (fun n ↦ X (n + 1)) P` propagates this to every
coordinate. Then the normalized sequence `Xₙ / n`, represented in Lean by the terms
`X 1 / 1, X 2 / 2, …`, has almost-sure limsup `⊤`. -/
theorem ae_limsup_normalized_iid_nonnegative_eq_top_of_not_integrable
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_not_integrable : ¬ Integrable (X 1) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop = ⊤ := sorry

/-! ### Exercise_5_1_4 (from Items/Chap05) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The weighted exponential series from Exercise 5.1.4, written in the textbook indexing
`X 1, X 2, ...`. -/
def weightedExpSeries (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (ω : Ω) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (Real.exp (X (n + 1) ω) * (c : ℝ) ^ (n + 1))

-- Proof sketch: apply the Borel--Cantelli lemma to the tail events
-- `{ω | X (n + 1) ω > -(n + 1) * Real.log (c : ℝ) - Real.log ((n + 1 : ℝ)^2)}`. Finite first
-- moment gives summability of the corresponding probabilities, hence eventually
-- `exp (X (n + 1) ω) * (c : ℝ)^(n + 1) ≤ (n + 1)⁻²`, which makes `weightedExpSeries X c ω`
-- surely by comparison with the convergent p-series.
/-- Exercise 5.1.4 (1): if `X₁, X₂, …` are i.i.d. nonnegative real random variables on a
probability space, `X₁` is almost surely nonnegative, and `X₁` has finite expectation,
equivalently `Integrable (X 1) P` under this nonnegativity hypothesis, then for every
`c ∈ (0, 1)` the weighted exponential series `∑ exp(Xₙ) cⁿ` is finite almost surely. -/
theorem ae_weightedExpSeries_lt_top_of_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_integrable : Integrable (X 1) P) :
    ∀ᵐ ω ∂P, weightedExpSeries X c ω < ∞ := sorry

-- Proof sketch: use the same threshold events as in the finite-moment case. When `X 1` is not
-- integrable, equivalently its nonnegative expectation is infinite, a tail-integral estimate
-- together with identical distribution shows that the probabilities of these events have
-- divergent sum; independence and the second Borel--Cantelli lemma then yield infinitely many
-- occurrences almost surely, forcing the partial sums of the nonnegative series to diverge to
-- `∞`.
/-- Exercise 5.1.4 (2): if `X₁, X₂, …` are i.i.d. nonnegative real random variables on a
probability space, `X₁` is almost surely nonnegative, and `X₁` has infinite expectation,
equivalently `¬ Integrable (X 1) P` under this nonnegativity hypothesis, then for every
`c ∈ (0, 1)` the weighted exponential series `∑ exp(Xₙ) cⁿ` is equal to `∞` almost surely. -/
theorem ae_weightedExpSeries_eq_top_of_not_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_not_integrable : ¬ Integrable (X 1) P) :
    ∀ᵐ ω ∂P, weightedExpSeries X c ω = ∞ := sorry
