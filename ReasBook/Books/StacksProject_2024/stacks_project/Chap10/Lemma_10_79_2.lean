import Mathlib
import StacksProject_2024.Chap10.Lemma_10_79_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

open PrimeSpectrum

/-!
Domain-style sampling:
* primary domain: support-theoretic openness loci for localized module maps over `Spec R`.
* sampled owner declarations:
  `Module.FinitePresentation.fg_ker`,
  `Module.isClosed_support`,
  `localized_surjective_iff_not_mem_support_cokernel`.
* best owner abstraction: the supports of the canonical kernel and cokernel modules.
* layer: `bridge/view`; the localized isomorphism locus is expressed through those owner supports.

Layering for this item:
* source-facing: the primes where `φ` becomes an isomorphism after localizing.
* core/canonical owners: `Module.support R (LinearMap.ker φ)` and
  `Module.support R (N ⧸ LinearMap.range φ)`.
* bridge/view: localized bijectivity is equivalent to lying outside both owner supports.

Primitive data vs derived API:
* primitive owner data are the kernel and cokernel modules;
* the isomorphism locus is a derived set, so this file states it directly rather than introducing a
  parallel wrapper definition.
-/

/-- A localized map is bijective exactly away from the supports of its kernel and cokernel. -/
theorem localized_bijective_iff_not_mem_support_ker_and_cokernel
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ) ↔
      p ∉ Module.support R (LinearMap.ker φ) ∧
        p ∉ Module.support R (N ⧸ LinearMap.range φ) := sorry

-- Proof sketch: by
-- `localized_bijective_iff_not_mem_support_ker_and_cokernel`, the bijective locus is the
-- intersection of the complements of `Module.support R (LinearMap.ker φ)` and
-- `Module.support R (N ⧸ LinearMap.range φ)`. The kernel support is closed because
-- `Module.FinitePresentation.fg_ker φ` makes `LinearMap.ker φ` finite from the assumptions that
-- `M` is finite and `N` is finitely presented; the cokernel support is closed because quotients of
-- finite modules are finite. Hence the bijective locus is open.
/-- Lemma 10.79.2: if `M` is a finite `R`-module and `N` is a finitely presented `R`-module, then
the set of primes `p` such that the localized map `φₚ : Mₚ → Nₚ` is an isomorphism is open in
`Spec R`. -/
theorem isOpen_moduleMapIsomorphismLocus [Module.Finite R M] [Module.FinitePresentation R N]
    (φ : M →ₗ[R] N) :
    IsOpen
      { p : PrimeSpectrum R | Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ) } :=
  sorry

end
