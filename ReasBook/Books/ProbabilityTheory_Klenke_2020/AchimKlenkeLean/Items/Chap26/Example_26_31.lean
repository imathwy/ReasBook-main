import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_51

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

local notation "PathSpace" => ContinuousMap NNReal ℝ

local instance pathSpaceMeasurableSpace : MeasurableSpace PathSpace := borel _
local instance pathSpaceBorelSpace : BorelSpace PathSpace := ⟨rfl⟩

-- Proof sketch: this is Theorem 21.51 specialized to the unit initial state corresponding to the
-- rescaling `N⁻¹ Z₀ᴺ = 1`; the rescaled path law already encodes the textbook linear
-- interpolation of `N⁻¹ Z^N_{⌊Nt⌋}`.
/-- Example 26.31: for the critical geometric Galton--Watson family with initial masses `N`, once
Lindvall's finite-dimensional convergence and tightness hypotheses are verified for the linearly
interpolated rescaled paths, those path laws converge weakly to a Feller branching diffusion
started from `1`. -/
theorem rescaledGaltonWatsonPathLaw_tendsto_fellerBranchingDiffusion_startedAtOne
    {ΩN : ℕ+ → Type u} [∀ N : ℕ+, MeasurableSpace (ΩN N)]
    {Ω : Type v} [MeasurableSpace Ω]
    (PZ : (N : ℕ+) → ProbabilityMeasure (ΩN N))
    (Z : (N : ℕ+) → ℕ → ΩN N → ℕ)
    (hZ_meas : ∀ N : ℕ+, ∀ k : ℕ, Measurable (Z N k))
    (PY : ProbabilityMeasure Ω)
    (Y : Ω → PathSpace)
    (hY_meas : Measurable Y)
    (hY : HasFellerBranchingDiffusionPathLaw PY Y 1)
    (hfdd :
      ∀ m : ℕ, ∀ times : Fin (m + 1) → NNReal,
        Tendsto
          (fun N : ℕ+ ↦
            continuousPathFiniteDimensionalDistribution
              (rescaledGaltonWatsonPathLaw (PZ N) (Z N) (hZ_meas N) (N : ℕ)) times)
          atTop
          (nhds
            (continuousPathFiniteDimensionalDistribution
              (continuousPathLaw PY Y hY_meas) times)))
    (htight :
      IsTightMeasureSet
        (Set.range fun N : ℕ+ ↦
          (rescaledGaltonWatsonPathLaw (PZ N) (Z N) (hZ_meas N) (N : ℕ) : Measure PathSpace))) :
    Tendsto
      (fun N : ℕ+ ↦ rescaledGaltonWatsonPathLaw (PZ N) (Z N) (hZ_meas N) (N : ℕ))
      atTop
      (nhds (continuousPathLaw PY Y hY_meas)) := sorry

end ProbabilityTheory
