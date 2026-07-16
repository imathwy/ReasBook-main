import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the affine-local prime/stalk localization API around
-- `IsLocalization.AtPrime` and associated primes, while local precedent
-- `mem_support_sections_iff_fromSpec_mem_support` fixes the affine-open point correspondence via
-- `hU.fromSpec p`. Following the Chapter 31 associated-point precedent, the main public entry uses
-- the canonical set owners `weaklyAssociatedPrimes` and `ℱ.weakAss`, with the pointwise predicate
-- form retained as a companion theorem.

/-- Lemma 31.5.2: for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a scheme `X`, an
affine open `U ⊆ X`, and a prime `\mathfrak p` of the section ring `Γ(X, U)`, the prime
`\mathfrak p` is weakly associated to the module of sections `Γ(U, \mathcal F)` if and only if the
corresponding point of `U` is weakly associated to `\mathcal F`. -/
@[stacks 056M]
theorem mem_weaklyAssociatedPrimes_sections_iff_fromSpec_mem_weakAss
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))) :
    p.asIdeal ∈ weaklyAssociatedPrimes (Γ(X, U)) (Γ(ℱ, U)) ↔
      hU.fromSpec p ∈ ℱ.weakAss := sorry

/-- Pointwise form of Lemma 31.5.2, expressed using the affine section predicate and the stalkwise
weak-association predicate. -/
theorem isWeaklyAssociatedToModule_sections_iff_fromSpec_weaklyAssociatedAt
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))) :
    Ideal.IsWeaklyAssociatedToModule (Γ(X, U)) (Γ(ℱ, U)) p.asIdeal ↔
      ℱ.weaklyAssociatedAt (hU.fromSpec p) := by
  simpa [mem_weaklyAssociatedPrimes_iff, mem_weakAss_iff] using
    (mem_weaklyAssociatedPrimes_sections_iff_fromSpec_mem_weakAss ℱ hU p)

end AlgebraicGeometry.Scheme.Modules
