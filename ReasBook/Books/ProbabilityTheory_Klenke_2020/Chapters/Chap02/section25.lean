import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_2_25 (from Items/Chap02) -/
open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]

-- Proof sketch: the textbook density factors coordinatewise by the Gaussian pdfs
-- `gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩`. Corollary 2.22 then gives independence from
-- the factorization of the finite-dimensional densities, and the singleton case identifies the
-- one-dimensional marginals with the Gaussian laws `gaussianReal (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩`.
/-- Example 2.25: Assume that each coordinate `X i` is measurable, that the variances satisfy
`σ i ^ 2 > 0`, and that every finite-dimensional joint law has the textbook Gaussian density
`x ↦ ∏ j, (2 * π * σ j ^ 2)^(-1 / 2) * exp (-(x j - m j)^2 / (2 * σ j ^ 2))`, expressed here via
`gaussianPDFReal`. Then the family is independent and each marginal has the Gaussian law
`N(m i, σ i ^ 2)`. -/
theorem iIndepFun_and_marginal_hasLaw_of_jointDensity_eq_prod_gaussianPDFReal
    {P : Measure Ω} {X : ι → Ω → ℝ} {m σ : ι → ℝ}
    (hX : ∀ i, Measurable (X i))
    (hσ : ∀ i, 0 < σ i ^ 2)
    (h_density :
      ∀ J : Finset ι,
        P.map (fun ω ↦ J.restrict (X · ω)) =
          volume.withDensity
            (fun x : J → ℝ ↦
              ENNReal.ofReal
                (∏ j : J, gaussianPDFReal (m j) ⟨σ j ^ 2, le_of_lt (hσ j)⟩ (x j)))) :
    iIndepFun X P ∧
      ∀ i, HasLaw (X i) (gaussianReal (m i) ⟨σ i ^ 2, le_of_lt (hσ i)⟩) P := by
  sorry
