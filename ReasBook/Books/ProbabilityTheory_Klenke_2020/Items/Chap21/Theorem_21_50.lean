import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_35
import ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_47
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ωn : ℕ → Type u} [∀ n : ℕ, MeasurableSpace (Ωn n)]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- The scalar rescaling of the discrete Galton--Watson population process `Z`, with time speed-up
by `n` and space scaling by `1 / n`. This is the textbook process `\tilde Z^n`. -/
def rescaledGaltonWatsonProcess {Ω : Type*} (Z : ℕ → Ω → ℕ) (n : ℕ) :
    NNReal → Ω → NNReal :=
  if _h : n = 0 then
    fun _ ω ↦ Z 0 ω
  else
    fun t ω ↦ (Z (Nat.floor ((n : ℝ) * (t : ℝ))) ω : NNReal) / (n : NNReal)

/-
The theorem is `source-facing`: its content is the concrete chapter claim that the rescaled
branching-process laws `ℒ_x[\tilde Zⁿ]` converge in finite-dimensional distributions to the
branching-diffusion laws `ℒ_x[Y]`. Its `core/canonical` owner is the chapter notation
`⟶[fdd]`, while `HasNaturalMarkovProperty` on the rescaled-process side and
`IsMarkovProcessRealization κ P Y` on the limit side are the ambient Markov-process owners.
-/
-- Proof sketch: use the natural Markov property of each rescaled branching process `\tilde Z^n`
-- and the Markov-process realization of `Y` to compute the finite-dimensional Laplace transforms
-- of the coordinate vectors recursively from the one-time transforms. Combine the assumed
-- convergence of the one-time rescaled Laplace transforms with the branching-diffusion Laplace
-- formula and then apply the Cramér--Wold device to conclude convergence of every finite
-- coordinate vector.
section

variable {κ : NNReal → Kernel NNReal NNReal}
variable (Z : (n : ℕ) → ℕ → Ωn n → ℕ)

local notation "Z̃" => fun n ↦ rescaledGaltonWatsonProcess (Z n) n

/-- Theorem 21.50: for a fixed initial state `x`, if the rescaled branching processes `\tilde Zⁿ`
have the natural Markov property under the laws `ℒ_x[\tilde Zⁿ]` and their one-time Laplace
transforms converge to the branching-diffusion Laplace transform, then
`(ℒ_x[\tilde Zⁿ], \tilde Zⁿ) ⟶[fdd] (ℒ_x[Y], Y)`. -/
theorem rescaled_branching_process_laws_tendsto_branchingDiffusion
    (x : NNReal)
    (PZ : (n : ℕ) → ProbabilityMeasure (Ωn n))
    (hZ_markov : ∀ n : ℕ,
      HasNaturalMarkovProperty
        (PZ n : Measure (Ωn n))
        (Z̃ n))
    (P : NNReal → ProbabilityMeasure Ω)
    (Y : NNReal → Ω → NNReal)
    [IsMarkovProcessRealization κ P Y]
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (h_laplace : ∀ t l : NNReal,
        Tendsto
          (fun n ↦
            ∫ ω,
              Real.exp (-((l : ℝ) * (Z̃ n t ω : ℝ)))
                ∂(PZ n : Measure (Ωn n)))
          atTop
          (nhds (branchingDiffusionLaplaceTransform t x l))) :
    (PZ, Z̃) ⟶[fdd] (P x, Y) := sorry

end

end ProbabilityTheory
