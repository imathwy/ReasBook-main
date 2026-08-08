import Mathlib
import ProbabilityTheory_Klenke_2020.Chap15.Corollary_15_32

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

/- Exercise 15.4.5 is `source-facing`: it states the Fréchet--Shohat subsequence and moment
criteria directly for weakly convergent laws on `ℝ`. Its `core/canonical` owner abstractions are
`ProbabilityMeasure ℝ` for weak convergence and `Measure.IsMomentDeterminate (μ : Measure ℝ)` for
the moment-determinate limit law; the moment equalities are derived from those owners rather than
additional primitive data. -/

section SubseqMoments

variable {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {r : ℝ} (φ : ℕ ↪o ℕ)

-- Proof sketch: combine weak convergence of the subsequence with the uniform `r`th absolute-moment
-- bound to obtain uniform integrability of `x ↦ |x| ^ s` for `0 < s < r`, then apply the
-- portmanteau/Vitali argument to the limit law.
/-- Exercise 15.4.5 (1): Item (i). If a subsequence of laws converges weakly and the whole
sequence has uniformly bounded `r`th absolute moments, then the weak limit has finite `s`th
absolute moment for every `0 < s < r`. -/
theorem integrable_abs_rpow_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    Integrable (fun x : ℝ ↦ |x| ^ s) (μ : Measure ℝ) := sorry

-- Proof sketch: apply the previous uniform-integrability input to the test functions
-- `x ↦ |x| ^ s`; weak convergence of the laws then upgrades to convergence of the corresponding
-- absolute moments along the subsequence.
/-- Exercise 15.4.5 (2): Item (i). Under the same hypotheses, the `s`th absolute moments converge
along the weakly convergent subsequence for every `0 < s < r`. -/
theorem tendsto_integral_abs_rpow_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    Tendsto (fun l ↦ ∫ x, |x| ^ s ∂(ν (φ l) : Measure ℝ)) atTop
      (𝓝 (∫ x, |x| ^ s ∂(μ : Measure ℝ))) := sorry

-- Proof sketch: first use the bounded `r`th absolute moments to deduce uniform integrability of
-- `x ↦ x ^ k` for each natural `k` with `0 < k < r`, then apply item (i) to identify the limit of
-- the ordinary moments along the weakly convergent subsequence.
/-- Exercise 15.4.5 (3): Item (i). Under the same hypotheses, every ordinary moment of order
`k ∈ ℕ ∩ (0, r)` converges along the weakly convergent subsequence. -/
theorem tendsto_moment_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {k : ℕ} (hk0 : 0 < k) (hkr : (k : ℝ) < r) :
    Tendsto (fun l ↦ moment id k (ν (φ l) : Measure ℝ)) atTop
      (𝓝 (moment id k (μ : Measure ℝ))) := sorry

end SubseqMoments

-- Proof sketch: convergence of the first absolute moments implies tightness of the laws; apply
-- sequential compactness of tight probability measures on `ℝ` to extract a weakly convergent
-- subsequence, then use item (i) to identify all moments of the limit law with the prescribed
-- limits `m k` and to recover that this limit law has finite absolute moments of every order.
/-- Exercise 15.4.5 (4): Item (ii). If every moment sequence eventually exists and converges to a
finite limit, then there is a probability law on `ℝ` with exactly those moments and a weakly
convergent subsequence of the original laws converging to it; in particular, the limiting law has
finite absolute moments of every order. -/
theorem exists_subseq_tendsto_probabilityMeasure_of_eventually_defined_moments
    {ν : ℕ → ProbabilityMeasure ℝ} (m : ℕ → ℝ)
    (hfinite :
      ∀ k : ℕ, ∀ᶠ n in atTop, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (ν n : Measure ℝ))
    (hm : ∀ k : ℕ, Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop (𝓝 (m k))) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ k : ℕ, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (μ : Measure ℝ)) ∧
        (∀ k : ℕ, moment id k (μ : Measure ℝ) = m k) ∧
        ∃ φ : ℕ ↪o ℕ, Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ) := sorry

/- The canonical chapter notion of a moment-determinate law is the owner predicate
`Measure.IsMomentDeterminate`; the corresponding owner-level theorem
`Measure.isMomentDeterminate_iff` exposes both the distinguished law's finite moments and its
uniqueness among comparison laws with the same finite moments. -/
recall Measure.isMomentDeterminate_iff

-- Proof sketch: by item (ii), every subsequence admits a further weakly convergent subsequence
-- whose limit law has moments `moment id k μ` and finite absolute moments of every order; the
-- eventual finite-moment hypothesis is needed here because `moment` is the totalized Bochner
-- integral in this project, so this genuine finite-moment content of the subsequential limit must
-- be recovered for the subsequential limits. Moment determinacy of `μ` already packages the
-- finite-moment content of the distinguished limit law together with uniqueness, so every such
-- subsequential limit equals `μ`, and the standard subsequence criterion yields convergence of
-- the whole sequence.
/-- Exercise 15.4.5 (5): Item (iii). This is the Fréchet--Shohat theorem in the source-faithful
form for the chapter's totalized moment convention: if the approximating laws eventually have all
absolute moments finite and the moments of `ν n` converge to those of a moment-determinate law
`μ`, then the laws `ν n` themselves converge weakly to `μ`. -/
theorem tendsto_probabilityMeasure_of_moments_tendsto_of_moment_determinate
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hfinite :
      ∀ k : ℕ, ∀ᶠ n in atTop, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (ν n : Measure ℝ))
    (hm : ∀ k : ℕ,
      Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop
        (𝓝 (moment id k (μ : Measure ℝ))))
    (hdet : Measure.IsMomentDeterminate (μ : Measure ℝ)) :
    Tendsto ν atTop (𝓝 μ) := sorry
