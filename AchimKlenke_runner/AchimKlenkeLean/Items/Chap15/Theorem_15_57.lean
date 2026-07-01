import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/- Theorem 15.57 is `source-facing`: the main mathematical content is the weak convergence of the
laws of the textbook normalized sums. In this domain the `core/canonical` owners are
`ProbabilityMeasure.map` for laws of measurable random vectors and `multivariateGaussian` for the
limit law. Since the chapter's `partialSum` owner is specialized to real-valued sequences, this
file keeps the vector-valued finite sum only as an internal bridge, not as a parallel public API.
-/

-- Proof sketch: each summand `X (k + 1)` is almost everywhere measurable, finite sums preserve
-- almost everywhere measurability, and multiplication by the constant `(√n)⁻¹` preserves it.
private theorem aemeasurable_multivariateCltNormalizedSum {P : Measure Ω}
    (X : ℕ → Ω → E)
    (hX : ∀ n, AEMeasurable (X (n + 1)) P) (n : ℕ) :
    AEMeasurable (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω) P := sorry

-- Proof sketch: for each `v`, apply the one-dimensional CLT to the scalar projections
-- `ω ↦ ⟪v, X n ω⟫`, whose limiting variance is identified from the covariance matrix `C`.
-- Then use the multidimensional convergence criterion from the preceding section
-- (the Cramér--Wold device / Theorem 15.56) to upgrade convergence of all linear forms to weak
-- convergence of the vector laws.
/-- Theorem 15.57: if `X₁, X₂, …` are i.i.d. `ℝ^d`-valued random vectors with mean `0` and
covariance matrix `C`, then the laws of the normalized sums `S_n^*` converge weakly to the
multivariate Gaussian law `N_{0,C}`. -/
theorem multivariate_central_limit_theorem (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (C : Matrix (Fin d) (Fin d) ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hX_memLp : MemLp (X 1) 2 P)
    (hX_mean : ∫ ω, X 1 ω ∂P = 0)
    (hX_cov : ∀ i j : Fin d, cov[fun ω ↦ X 1 ω i, fun ω ↦ X 1 ω j; P] = C i j) :
    Tendsto
      (fun n : ℕ ↦
        ProbabilityMeasure.map ⟨P, inferInstance⟩
          (show AEMeasurable
              (fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, X (k + 1) ω) P from
            aemeasurable_multivariateCltNormalizedSum X
              (fun n ↦ (hX_ident n).aemeasurable_fst) n))
      atTop
      (𝓝 ⟨multivariateGaussian 0 C, inferInstance⟩) := sorry

end
