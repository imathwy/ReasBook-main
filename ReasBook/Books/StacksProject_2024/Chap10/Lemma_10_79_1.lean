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

/-- Helper for Lemma 10.79.1: localizing `φ` at a submonoid is surjective exactly when the
localized cokernel is trivial. -/
lemma localized_map_surjective_iff_subsingleton_cokernel
    (φ : M →ₗ[R] N) (S : Submonoid R) :
    Function.Surjective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (N ⧸ LinearMap.range φ)) :=
  -- TODO: translate `LocalizedModule.subsingleton_iff` for the cokernel into surjectivity by
  -- clearing denominators in both directions with `IsLocalizedModule.mk'_surjective`.
  sorry

/-- Helper for Lemma 10.79.1: the tensor of the cokernel with the residue field is trivial exactly
when the residue-field fiber map is surjective. -/
lemma tensor_cokernel_subsingleton_iff_rTensor_surjective [Module.Finite R N]
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Subsingleton ((N ⧸ LinearMap.range φ) ⊗[R] p.asIdeal.ResidueField) ↔
      Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) :=
  -- TODO: tensor the exact cokernel sequence on the right by `κ(p)`, identify the resulting
  -- quotient map as zero exactly when `(N ⧸ range φ) ⊗[R] κ(p)` is subsingleton, and conclude
  -- surjectivity from `LinearMap.exact_zero_iff_surjective`.
  sorry

/-- A localized map is surjective exactly away from the support of its cokernel. -/
theorem localized_surjective_iff_not_mem_support_cokernel
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) ↔
      p ∉ Module.support R (N ⧸ LinearMap.range φ) := by
  -- Translate support avoidance into vanishing of the localized cokernel and specialize the
  -- general submonoid criterion.
  rw [Module.notMem_support_iff]
  simpa using localized_map_surjective_iff_subsingleton_cokernel φ p.asIdeal.primeCompl

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
      p ∉ Module.support R (N ⧸ LinearMap.range φ) :=
  -- TODO: combine the residue-field tensor helper with
  -- `Module.mem_support_iff_nontrivial_residueField_tensorProduct`, using `TensorProduct.comm` to
  -- pass from `κ(p) ⊗[R] cokernel` to `cokernel ⊗[R] κ(p)`.
  sorry

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
    Function.Surjective (LocalizedModule.map (.powers f) φ) := by
  -- The hypothesis says the basic open `D(f)` is disjoint from the support of the cokernel.
  have hsub :
      Subsingleton (LocalizedModule (.powers f) (N ⧸ LinearMap.range φ)) := by
    rw [LocalizedModule.subsingleton_iff_disjoint]
    refine Set.disjoint_left.2 ?_
    intro p hpD hpSupport
    exact (localized_surjective_iff_not_mem_support_cokernel φ p).mp (hU hpD) hpSupport
  -- Vanishing of the away-localized cokernel is equivalent to surjectivity after localizing away.
  exact (localized_map_surjective_iff_subsingleton_cokernel φ (.powers f)).mpr hsub

end
