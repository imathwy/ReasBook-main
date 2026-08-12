import Mathlib
import ProbabilityTheory_Klenke_2020.Chap02.Definition_2_20
import ProbabilityTheory_Klenke_2020.Chap02.Theorem_2_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]

local instance : DecidableEq ι := Classical.decEq ι

-- Proof sketch: if `X` is independent, Theorem 2.21 gives the factorization of the finite joint
-- distribution functions; uniqueness of continuous densities identifies the integrands, yielding
-- the density product formula. Conversely, integrating the product density over rectangles gives
-- the factorization of the finite joint distribution functions, and Theorem 2.21 then yields
-- independence.
/-- Corollary 2.22: If every finite joint law of a real-valued family admits a continuous density
with respect to Lebesgue measure, then the family is independent if and only if every finite joint
density factors as the product of the corresponding one-dimensional densities. -/
theorem iIndepFun_iff_jointDensityFactorizes (μ : Measure Ω) (X : ι → Ω → ℝ)
    (f : ∀ J : Finset ι, (J → ℝ) → NNReal) (hX : ∀ i, Measurable (X i))
    (hcont : ∀ J : Finset ι, Continuous (f J))
    (h_density :
      ∀ J : Finset ι,
        μ.map (fun ω ↦ J.restrict (X · ω)) =
          volume.withDensity (fun x ↦ (f J x : ENNReal))) :
    iIndepFun X μ ↔
      ∀ (J : Finset ι) (x : J → ℝ),
        f J x = ∏ j : J, f ({j.1} : Finset ι) (fun _ ↦ x j) := sorry

end
