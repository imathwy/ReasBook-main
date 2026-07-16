import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

section

/- Exercise 13.2.12 is `source-facing`: it keeps the textbook hypotheses and conclusions in terms
of random variables, but its `core/canonical` owner abstraction is weak convergence of their laws,
accessed here through `MeasureTheory.TendstoInDistribution`. The chapter-level bridge is
`tendstoInDistribution_iff_tendsto_limit_law`, and the lower-semicontinuity input for item `(i)`
is the Portmanteau lintegral theorem
`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`. The moment
expressions are therefore derived from the law-level owner API, not additional primitive data. -/

variable {Ω : ℕ → Type u} {Ω' : Type v}
variable {m : ∀ n, MeasurableSpace (Ω n)} {m' : MeasurableSpace Ω'}
variable {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
variable {μ' : Measure Ω'} [IsProbabilityMeasure μ']
variable {X : (n : ℕ) → Ω n → ℝ} {Z : Ω' → ℝ}

-- Proof sketch: apply the portmanteau lower-semicontinuity inequality to the nonnegative lower
-- semicontinuous test function `x ↦ |x|`, written as an `ENNReal`-valued lower integral of the
-- laws of the random variables.
/-- Exercise 13.2.12 (1): Item (i). Under convergence in distribution, the first absolute moment
of the limit is bounded above by the liminf of the first absolute moments of the approximating
random variables, interpreted as nonnegative extended expectations. -/
theorem lintegral_abs_le_liminf_of_tendstoInDistribution
    (hXZ : TendstoInDistribution X atTop Z μ μ') :
    ∫⁻ ω, ENNReal.ofReal |Z ω| ∂μ' ≤
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal |X n ω| ∂μ n) atTop := sorry

-- Proof sketch: first apply the continuous mapping theorem to `x ↦ |x| ^ p` to obtain
-- convergence in distribution of the `p`-th absolute powers, then use the uniform `r`-moment
-- bound with `r > p` to get uniform integrability and conclude convergence of the corresponding
-- moments by Vitali/portmanteau.
/-- Exercise 13.2.12 (2): Item (ii). If `0 < p < r` and the `r`-th absolute moments are
uniformly bounded, then the `p`-th absolute moments converge along the distributional limit,
again in the extended nonnegative sense. -/
theorem tendsto_lintegral_abs_rpow_of_tendstoInDistribution_of_bounded_moment
    {p r : ℝ} (hp : 0 < p) (hpr : p < r)
    (hXZ : TendstoInDistribution X atTop Z μ μ')
    (hbound : sSup (Set.range fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n) < ⊤) :
    Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂μ')) := sorry

end
