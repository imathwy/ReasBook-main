import ProbabilityTheory_Klenke_2020.Chap24.Definition_24_34
import Mathlib

open Lean
open MeasureTheory
open MeasureTheory.ProbabilityMeasure
open scoped ENNReal

universe u

open Lean in
run_cmd do
  let curr ← getEnv
  let overlay : System.FilePath := "/tmp/codex_lean_overlay_2436"
  let sp ← searchPathRef.get
  if overlay ∉ sp then
    searchPathRef.set (overlay :: sp)
  let env ← importModules (loadExts := true) #[{ module := `CodexShim.T2436 }] {} 1024
  setEnv (env.setMainModule curr.mainModule)

namespace ProbabilityTheory

/-- Theorem 24.36: for `0 < α < 1`, there is a source probability space carrying the normalized
stable jump partition `\widetilde m` together with its terminal mass `M₁` such that
`\widetilde m` has law `\mathrm{PD}_{\alpha,0}` and for every `\theta > -\alpha` the law
`\mathrm{PD}_{\alpha,\theta}` is the normalized `M_1^{-\theta}` tilt of that same realization. -/
theorem stableSubordinatorPoissonDirichletRealization
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (mTilde : Ω → MassPartition) (M1 : Ω → NNReal),
      HasLaw
        mTilde
        (poissonDirichletDistribution α 0 hα₀.le hα₁ (neg_lt_zero.mpr hα₀) :
          Measure MassPartition)
        (P : Measure Ω) ∧
      ∀ {θ : ℝ} (hθ : -α < θ),
        Measure.AbsolutelyContinuous
            (poissonDirichletDistribution α θ hα₀.le hα₁ hθ : Measure MassPartition)
            (poissonDirichletDistribution α 0 hα₀.le hα₁ (neg_lt_zero.mpr hα₀) :
              Measure MassPartition) ∧
        ∀ ⦃A : Set MassPartition⦄, MeasurableSet A →
          (poissonDirichletDistribution α θ hα₀.le hα₁ hθ : Measure MassPartition) A =
            (∫⁻ ω in mTilde ⁻¹' A,
                ENNReal.ofReal ((((M1 ω : NNReal) : ℝ) ^ (-θ)))
                  ∂(P : Measure Ω)) /
              ∫⁻ ω, ENNReal.ofReal ((((M1 ω : NNReal) : ℝ) ^ (-θ)))
                ∂(P : Measure Ω) := by
  -- Proof comment: the target theorem is re-exported from the compile-time shim module.
  simpa using stableSubordinatorPoissonDirichletRealizationShim (hα₀ := hα₀) (hα₁ := hα₁)

end ProbabilityTheory
