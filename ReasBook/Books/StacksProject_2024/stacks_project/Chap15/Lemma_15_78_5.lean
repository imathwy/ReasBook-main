import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_109_10
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_15
import StacksProject_2024.stacks_project.Chap15.Lemma_15_18_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_19
import StacksProject_2024.stacks_project.Chap15.Lemma_15_78_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/-- Lemma 15.78.5: let `A → B` be a flat ring map, let `d ≥ 0`, and let `K^•` be a
pseudo-coherent object of `D(B)`. If every fiber ring `B ⊗[A] κ(\mathfrak p)` has global
dimension at most `d` and `K^•`, viewed over `A`, has tor-amplitude in `[a, b]`, then `K^•` is
perfect over `B` and has tor-amplitude in `[a - d, b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_fiber_hasGlobalDimensionLE
    (K : DModB) (a b : ℤ) (d : ℕ)
    (hfiber :
      ∀ p : PrimeSpectrum A, HasGlobalDimensionLE (p.asIdeal.Fiber B) d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        a b) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := by
  -- Proof comment: the target statement is isolated here while the proof is repaired separately.
  sorry

end

end CategoryTheory
