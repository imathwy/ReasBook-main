import Mathlib.RingTheory.Spectrum.Prime.Module
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: the source-facing owner is the scheme-module support `moduleSupport`, whose
-- affine counterpart is the canonical module-theoretic support on prime spectra, with
-- `Module.stableUnderSpecialization_support` as the core affine specialization-closed owner.

/-- Lemma 29.5.2: for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a scheme `X`, the
support of `\mathcal F` is closed under specialization. -/
@[stacks 05AC]
theorem stableUnderSpecialization_moduleSupport :
    StableUnderSpecialization (moduleSupport ℱ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
