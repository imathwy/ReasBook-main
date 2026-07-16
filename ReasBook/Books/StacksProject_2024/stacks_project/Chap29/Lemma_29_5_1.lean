import Mathlib.RingTheory.Spectrum.Prime.Module
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: the source-facing scheme-module support owner is `moduleSupport`, while the
-- affine section-side owner is the canonical module-theoretic support `Module.support`; the point
-- correspondence is the standard affine-open map `IsAffineOpen.fromSpec`.

/-- Lemma 29.5.1: for a quasi-coherent `\mathcal O_X`-module `ℱ` on a scheme `X`, an affine open
`U ⊆ X`, and a prime `p` of the section ring `Γ(X, U)`, the prime `p` lies in the support of the
module of sections `Γ(ℱ, U)` if and only if the corresponding point of `U` lies in the support of
`ℱ`. -/
@[stacks 056I]
theorem mem_support_sections_iff_fromSpec_mem_support
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))) :
    p ∈ Module.support (Γ(X, U)) (Γ(ℱ, U)) ↔ hU.fromSpec p ∈ moduleSupport ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
