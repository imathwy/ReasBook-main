import AchimKlenkeLean.Items.Chap03.Theorem_3_2
import AchimKlenkeLean.Items.Chap15.Corollary_15_32
import AchimKlenkeLean.Items.Chap15.Example_15_5

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

noncomputable section

/- Recall for Example 15.33, item (i): the Gaussian law `N_{μ,σ²}` has moment-generating
function `t ↦ exp (μ t + σ² t² / 2)`. -/
recall ProbabilityTheory.mgf_id_gaussianReal

-- Proof sketch: combine the explicit Gaussian moment-generating function with Corollary 15.32 to
-- put the source statement into the chapter's canonical owner abstraction
-- `Measure.IsMomentDeterminate`.
/-- Example 15.33 (1): Item (i). A Gaussian law on `ℝ` is moment determinate. -/
theorem isMomentDeterminate_gaussianReal (μ : ℝ) (σ2 : NNReal) :
    Measure.IsMomentDeterminate (gaussianReal μ σ2) := sorry

/-- Companion corollary: equality of all moments identifies a Gaussian law. -/
theorem gaussianReal_eq_of_forall_moment_eq
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (μ : ℝ) (σ2 : NNReal)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_mom : ∀ n : ℕ, moment id n ν = moment id n (gaussianReal μ σ2)) :
    ν = gaussianReal μ σ2 := by
  symm
  exact Measure.IsMomentDeterminate.eq_of_forall_moment_eq
    (μ := gaussianReal μ σ2) (ν := ν) (isMomentDeterminate_gaussianReal μ σ2) hν_moments
    (fun n ↦ (h_mom n).symm)

-- Proof sketch: the Gaussian exponential integrability set is all of `ℝ`, so
-- `analyticOn_complexMGF` applies on the whole complex plane to the complex mgf
-- `z ↦ exp (μ z + σ² z² / 2)`. Restricting to the imaginary axis recovers the analytic
-- characteristic function.
/-- Example 15.33 (2): Item (i). The characteristic function of a Gaussian law is analytic on
`ℝ`. -/
theorem gaussianReal_charFun_analytic (μ : ℝ) (σ2 : NNReal) :
    AnalyticOn ℝ (charFun (gaussianReal μ σ2)) Set.univ := sorry

/-- Companion theorem: the complex moment-generating function of a Gaussian law is entire. -/
theorem gaussianReal_complexMGF_entire (μ : ℝ) (σ2 : NNReal) :
    AnalyticOn ℂ (complexMGF id (gaussianReal μ σ2)) Set.univ := sorry

-- Proof sketch: evaluate the exponential-density integral explicitly on `(0, ∞)`, which is
-- the standard geometric-series integral after the substitution `u = (θ - t) x`.
/-- Example 15.33 (3): Item (ii). For the exponential law with rate `θ > 0`, the moment-generating
function is `t ↦ θ / (θ - t)` on `(-∞, θ)`. -/
theorem expMeasure_mgf_eq (θ : ℝ) (hθ : 0 < θ) {t : ℝ} (ht : t < θ) :
    mgf id (expMeasure θ) t = θ / (θ - t) := sorry

-- Proof sketch: the explicit mgf on `(-∞, θ)` supplies the exponential integrability input for
-- Corollary 15.32, so the textbook uniqueness statement is best expressed via
-- `Measure.IsMomentDeterminate`.
/-- Example 15.33 (4): Item (ii). The exponential law with rate `θ > 0` is moment determinate. -/
theorem isMomentDeterminate_expMeasure (θ : ℝ) (hθ : 0 < θ) :
    Measure.IsMomentDeterminate (expMeasure θ) := sorry

/-- Companion corollary: equality of all moments identifies the exponential law of rate `θ`. -/
theorem expMeasure_eq_of_forall_moment_eq
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (θ : ℝ) (hθ : 0 < θ)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_mom : ∀ n : ℕ, moment id n ν = moment id n (expMeasure θ)) :
    ν = expMeasure θ := by
  symm
  exact Measure.IsMomentDeterminate.eq_of_forall_moment_eq
    (μ := expMeasure θ) (ν := ν) (isMomentDeterminate_expMeasure θ hθ) hν_moments
    (fun n ↦ (h_mom n).symm)

-- Proof sketch: compute the complex mgf on the open half-plane `Re z < θ` by the same density
-- integral as in the real case, now with complex parameter `z`. The resulting rational function is
-- holomorphic there and restricts on the imaginary axis to the textbook characteristic function.
/-- Example 15.33 (5): Item (ii). The characteristic function of the exponential law with rate
`θ > 0` is analytic on `ℝ`. -/
theorem expMeasure_charFun_analytic (θ : ℝ) (hθ : 0 < θ) :
    AnalyticOn ℝ (charFun (expMeasure θ)) Set.univ := sorry

/-- Companion theorem: the complex moment-generating function of the exponential law of rate `θ`
is `z ↦ θ / (θ - z)` on the half-plane `Re z < θ`. -/
theorem expMeasure_complexMGF_eq (θ : ℝ) (hθ : 0 < θ) {z : ℂ} (hz : z.re < θ) :
    complexMGF id (expMeasure θ) z = (θ : ℂ) / ((θ : ℂ) - z) := sorry

-- Proof sketch: once `t ≥ θ`, the density representation reduces to the divergent integral of
-- `exp (-(θ - t) x)` over `[0, ∞)`, so the defining exponential moment cannot be integrable.
/-- Example 15.33 (6): Item (ii). For the exponential law with rate `θ > 0`, the exponential
moment at `t` is infinite whenever `t ≥ θ`. -/
theorem expMeasure_not_mem_integrableExpSet_of_ge (θ : ℝ) (hθ : 0 < θ) {t : ℝ}
    (ht : θ ≤ t) :
    t ∉ integrableExpSet id (expMeasure θ) := sorry

/- Example 15.33 (7): Item (iii). If `X = exp Y` with `Y ∼ N(0,1)`, then
`E[X^n] = exp (n² / 2)`. This is exactly the standard log-normal moment formula from
Example 15.5. -/
recall standardLogNormalMeasure_moment

-- Proof sketch: use the oscillatory Stieltjes family from Example 15.5. A nontrivial
-- `logNormalPerturbationMeasure α` is a second probability measure with the same moments as
-- `standardLogNormalMeasure`, so the Chapter 15 owner notion of moment determinacy fails for
-- the standard log-normal law itself.
/-- Example 15.33 (8): Item (iii). The standard log-normal law is not determined by its moments. -/
theorem standardLogNormal_not_moment_determinate :
    ¬ Measure.IsMomentDeterminate standardLogNormalMeasure := sorry

-- Proof sketch: compare the pgf coefficients `p n` with the moment roots and apply the
-- Cauchy--Hadamard root test. This gives the full convergence disk for the pgf power series, not
-- just one point beyond `1`.
/-- Example 15.33 (9): Item (iv). For an `ℕ`-valued law, the pgf power series converges at every
complex point `z` with `|z|` strictly smaller than the reciprocal of the limsup of the extended
moment roots. -/
theorem nat_pmf_pgf_series_summable_of_norm_lt_inv_limsup_moment_root (p : PMF ℕ) {z : ℂ}
    (hz :
      ENNReal.ofReal ‖z‖ <
        (limsup
            (fun n : ℕ ↦
              (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
            atTop)⁻¹) :
    Summable (fun n : ℕ ↦ (p n).toReal * z ^ n) := sorry

-- Proof sketch: the hypothesis on `p` gives a real convergence point `z > 1` for its pgf by the
-- preceding radius criterion. Applying the Chapter 3 owner theorem
-- `probabilityGeneratingFunctionReal_eq_of_iteratedDeriv_eq_of_summable` then recovers the pgf
-- from its derivatives at `1`.
/-- Example 15.33 (10): Item (iv). If two `ℕ`-valued laws have root-limsup strictly smaller than
`1` and the same derivatives of their pgfs at `1`, then their pgfs agree. -/
theorem nat_pmf_probabilityGeneratingFunctionReal_eq_of_iteratedDeriv_eq_of_limsup_moment_root_lt_one
    {p q : PMF ℕ}
    (hpβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    (hqβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂q.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    (h_deriv :
      ∀ n : ℕ,
        iteratedDeriv n (probabilityGeneratingFunctionReal p) 1 =
          iteratedDeriv n (probabilityGeneratingFunctionReal q) 1) :
    probabilityGeneratingFunctionReal p = probabilityGeneratingFunctionReal q := sorry

-- Proof sketch: the root-limsup hypothesis gives a real convergence point `z > 1` for the pgf by
-- the preceding radius criterion. Equality of moments yields equality of the derivatives of the pgf
-- at `1`, so the previous pgf-uniqueness theorem identifies the pushed-forward law.
/-- Example 15.33 (11): Item (iv). If an `ℕ`-valued law has root-limsup strictly smaller than `1`,
then the associated real-valued law `k ↦ k` is moment determinate. -/
theorem isMomentDeterminate_nat_pmf_of_limsup_moment_root_lt_one
    (p : PMF ℕ)
    (hpβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    :
    IsMomentDeterminate p.toMeasure (fun k : ℕ ↦ (k : ℝ)) := sorry

/-- Companion corollary: under the same root-growth hypothesis, equality of all moments identifies
an `ℕ`-valued law. -/
theorem nat_pmf_eq_of_forall_moment_eq_of_limsup_moment_root_lt_one
    {p q : PMF ℕ}
    (hpβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    (hq_moments : ∀ n : ℕ, Integrable (fun k : ℕ ↦ |(k : ℝ)| ^ n) q.toMeasure)
    (h_mom :
      ∀ n : ℕ,
        moment (fun k : ℕ ↦ (k : ℝ)) n p.toMeasure =
          moment (fun k : ℕ ↦ (k : ℝ)) n q.toMeasure) :
    p = q := by
  let h_det : IsMomentDeterminate p.toMeasure (fun k : ℕ ↦ (k : ℝ)) :=
    isMomentDeterminate_nat_pmf_of_limsup_moment_root_lt_one p hpβ
  let h_nat_embedding : MeasurableEmbedding (fun k : ℕ ↦ (k : ℝ)) :=
    MeasurableEmbedding.natCast
  have hmap :
      p.toMeasure.map (fun k : ℕ ↦ (k : ℝ)) =
        q.toMeasure.map (fun k : ℕ ↦ (k : ℝ)) :=
    h_det.map_eq q.toMeasure (fun k : ℕ ↦ (k : ℝ)) h_nat_embedding.measurable hq_moments h_mom
  exact PMF.toMeasure_injective <| h_nat_embedding.map_injective hmap
