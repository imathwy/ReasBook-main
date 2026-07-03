import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46
import ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_27

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ν : NNReal → ProbabilityMeasure ℝ}

/-- The translated convolution kernels attached to `ν`, with time-`t` row
`x ↦ δ_x ∗ ν_t`. -/
noncomputable abbrev translatedConvolutionKernel
    (ν : NNReal → ProbabilityMeasure ℝ) : NNReal → Kernel ℝ ℝ :=
  fun t ↦ dirac_convolution_kernel (ν t : Measure ℝ)

@[simp] theorem translatedConvolutionKernel_apply (t : NNReal) :
    translatedConvolutionKernel ν t = dirac_convolution_kernel (ν t : Measure ℝ) :=
  rfl

namespace IsContinuousConvolutionSemigroup

variable [IsContinuousConvolutionSemigroup ν]

-- Proof sketch: the translated kernels `x ↦ δ_x ∗ ν_t` form a Markov semigroup by the
-- convolution-semigroup law, preserve `C₀(ℝ)` because translation acts continuously on `ℝ`, and
-- converge pointwise to the identity at `t = 0` by the weak continuity of `ν` at the origin.
/-- A continuous convolution semigroup on `ℝ` canonically induces a Feller semigroup on the
translated convolution kernels `t ↦ x ↦ δ_x ∗ ν_t`. -/
instance translatedConvolutionKernel_isFellerSemigroup :
    IsFellerSemigroup (translatedConvolutionKernel ν) where
  isMarkovKernel t := by
    refine ⟨?_⟩
    intro x
    rw [translatedConvolutionKernel_apply, dirac_convolution_kernel_apply]
    infer_instance
  zero_eq := by
    sorry
  comp_eq s t := by
    sorry
  mapZeroAtInfty_continuous t f := by
    sorry
  mapZeroAtInfty_zeroAtInfty t f := by
    sorry
  continuousAt_zero f x := by
    sorry

end IsContinuousConvolutionSemigroup

namespace IsFellerProcessRealization

variable {P : ℝ → ProbabilityMeasure Ω}
variable {X : NNReal → Ω → ℝ}
variable {pathKernel : Kernel ℝ (NNReal → ℝ)}
variable [IsContinuousConvolutionSemigroup ν]

-- Proof sketch: use `transition_eq` to identify the transition kernel with
-- `x ↦ δ_x ∗ ν (t - s)` via `translatedConvolutionKernel ν`, then apply the Markov property at
-- time `s`
-- and push the translated law forward by `y ↦ y - X s`.
/-- If a Feller realization has transition kernels `x ↦ δ_x ∗ ν_t`, then under every initial law
`P x` the increment over `[s, t]` has law `ν (t - s)`. -/
theorem increment_hasLaw_of_diracConvolutionKernel
    (hX : IsFellerProcessRealization (translatedConvolutionKernel ν) P X pathKernel)
    (x : ℝ) :
    ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw (fun ω ↦ X t ω - X s ω) (ν (t - s) : Measure ℝ) (P x : Measure Ω) := sorry

-- Proof sketch: both translated increments have law `ν s` by
-- `increment_hasLaw_of_diracConvolutionKernel`, so they are identically distributed.
/-- The same translated-kernel realization has stationary increment laws under every initial law.
-/
theorem hasStationaryIncrementLaws_of_diracConvolutionKernel
    (hX : IsFellerProcessRealization (translatedConvolutionKernel ν) P X pathKernel)
    (x : ℝ) :
    HasStationaryIncrementLaws X (P x : Measure Ω) := sorry

-- Proof sketch: use the Markov property and the translation form of the transition kernels to
-- prove independence of disjoint increments; combine this with the stationary-increment-law lemma.
/-- A Feller realization of the translated convolution kernels has independent stationary
increments under every initial law. -/
theorem hasStationaryIndependentIncrements_of_diracConvolutionKernel
    (hX : IsFellerProcessRealization (translatedConvolutionKernel ν) P X pathKernel)
    (x : ℝ) :
    HasStationaryIndependentIncrements X (P x : Measure Ω) := sorry

end IsFellerProcessRealization

-- Proof sketch: use the canonical translated kernel family `translatedConvolutionKernel ν`, apply
-- `exists_fellerProcessRealization`, and then use the
-- translated-kernel realization lemmas to record the prescribed increment laws and stationary
-- independent increments under each initial law.
/-- Corollary 21.25: a continuous convolution semigroup on `ℝ` yields the translated Feller
semigroup on `translatedConvolutionKernel ν`, and this semigroup admits a càdlàg strong Markov
realization.
Under each initial law `P x`, the increment over `[s, t]` has law `ν (t - s)`, hence the
realization has stationary independent increments as well. -/
theorem exists_cadlagMarkovRealization_of_continuousConvolutionSemigroup
    (ν : NNReal → ProbabilityMeasure ℝ) [IsContinuousConvolutionSemigroup ν] :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ X : NNReal → Ω → ℝ,
      ∃ P : ℝ → ProbabilityMeasure Ω, ∃ pathKernel : Kernel ℝ (NNReal → ℝ),
        IsFellerProcessRealization (translatedConvolutionKernel ν) P X pathKernel ∧
          (∀ x : ℝ, ∀ ⦃s t : NNReal⦄, s ≤ t →
            HasLaw (fun ω ↦ X t ω - X s ω) (ν (t - s) : Measure ℝ) (P x : Measure Ω)) ∧
          ∀ x : ℝ, HasStationaryIndependentIncrements X (P x : Measure Ω) := sorry

end ProbabilityTheory
