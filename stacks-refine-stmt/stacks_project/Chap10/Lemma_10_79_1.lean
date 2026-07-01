import Mathlib
import stacks_project.Chap10.Definition_10_17_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open PrimeSpectrum
open scoped PrimeSpectrum
open scoped TensorProduct

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-
Layering for this item:
* source-facing: the primes where `φ` is surjective after localization or on the residue-field
  fiber.
* core/canonical owner: `Module.support R (N ⧸ LinearMap.range φ)`.
* bridge/view: those source-facing loci are the complement of the support of the cokernel.

Primitive data vs derived API:
* primitive owner data is the cokernel `N ⧸ LinearMap.range φ`;
* the localized and residue-field surjectivity loci are derived views, so they are expressed
  directly as sets rather than introduced as separate owner definitions.
-/

/-- A localized map is surjective exactly away from the support of its cokernel. -/
theorem localized_surjective_iff_not_mem_support_cokernel
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) ↔
      p ∉ Module.support R (N ⧸ LinearMap.range φ) := sorry

/-- The localized surjectivity locus is the complement of the support of the cokernel. -/
theorem moduleMapSurjectiveLocus_eq_compl_support_cokernel
    (φ : M →ₗ[R] N) :
    { p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) } =
      (Module.support R (N ⧸ LinearMap.range φ))ᶜ := by
  ext p
  simpa [Set.mem_compl_iff] using localized_surjective_iff_not_mem_support_cokernel φ p

/-- For a finite target module, surjectivity on the residue-field fiber is equivalent to vanishing
of the cokernel at that prime. -/
theorem fiber_surjective_iff_not_mem_support_cokernel [Module.Finite R N]
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) ↔
      p ∉ Module.support R (N ⧸ LinearMap.range φ) := sorry

/-- The residue-field fiber surjectivity locus is the complement of the support of the cokernel. -/
theorem moduleMapFiberSurjectiveLocus_eq_compl_support_cokernel [Module.Finite R N]
    (φ : M →ₗ[R] N) :
    { p : PrimeSpectrum R | Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) } =
      (Module.support R (N ⧸ LinearMap.range φ))ᶜ := by
  ext p
  simpa [Set.mem_compl_iff] using fiber_surjective_iff_not_mem_support_cokernel φ p

/-- Lemma 10.79.1 (1): for a map `φ : M →ₗ[R] N` with `N` finite, the locus where the localized
map `φₚ : Mₚ → Nₚ` is surjective is exactly the locus where the fiber map
`M ⊗[R] κ(p) → N ⊗[R] κ(p)` is surjective. -/
-- Proof sketch: fix `p`. Over the local ring `Rₚ`, surjectivity of `φₚ` is equivalent by
-- Nakayama's lemma to surjectivity modulo the maximal ideal, and the latter is exactly
-- surjectivity after tensoring with `κ(p)`.
theorem moduleMapSurjectiveLocus_eq_moduleMapFiberSurjectiveLocus [Module.Finite R N]
    (φ : M →ₗ[R] N) :
    { p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) } =
      { p : PrimeSpectrum R | Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) } :=
  (moduleMapSurjectiveLocus_eq_compl_support_cokernel φ).trans
    (moduleMapFiberSurjectiveLocus_eq_compl_support_cokernel φ).symm

/-- Lemma 10.79.1 (2): for a map `φ : M →ₗ[R] N` with `N` finite, the surjectivity locus of `φ`
is an open subset of `Spec R`. -/
-- Proof sketch: the cokernel `N ⧸ LinearMap.range φ` is finite because `N` is finite, so its
-- support is closed. A prime lies outside that support exactly when the localized cokernel
-- vanishes, equivalently when `φₚ` is surjective, so the surjectivity locus is the complement of a
-- closed set.
theorem isOpen_moduleMapSurjectiveLocus [Module.Finite R N] (φ : M →ₗ[R] N) :
    IsOpen { p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) } := by
  rw [moduleMapSurjectiveLocus_eq_compl_support_cokernel φ]
  exact Module.isClosed_support.isOpen_compl

/-- Lemma 10.79.1 (3): if the basic open `D(f)` is contained in the surjectivity locus of `φ`,
then the localized map `M_f → N_f` is surjective. -/
-- Proof sketch: every maximal ideal of `Localization.Away f` comes from a prime of `R` lying in
-- `D(f)`, so the hypothesis implies surjectivity after localizing `φ_f` at every maximal ideal of
-- `R_f`. Apply the local-to-global surjectivity criterion `surjective_of_localized_maximal`.
theorem surjective_localizedAway_of_D_subset_moduleMapSurjectiveLocus
    (φ : M →ₗ[R] N) (f : R)
    (hU :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) }) :
    Function.Surjective (LocalizedModule.map (.powers f) φ) := sorry

end
