import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap10.Lemma_10_79_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open PrimeSpectrum
open scoped PrimeSpectrum
open scoped TensorProduct

section

variable {R : Type u} [CommRing R]
variable {P₁ : Type v} [AddCommGroup P₁] [Module R P₁]
variable {P₂ : Type w} [AddCommGroup P₂] [Module R P₂]

/- Domain-style sampling:
* primary domain: support-theoretic residue-field fiber loci for maps of finite projective modules
  over `Spec R`.
* sampled owner declarations:
  `Module.mem_support_iff`,
  `Module.isClosed_support`,
  `fiber_surjective_iff_not_mem_support_cokernel`,
  `localized_bijective_iff_not_mem_support_ker_and_cokernel`,
  `isOpen_moduleMapSurjectiveLocus`,
  `surjective_localizedAway_of_D_subset_moduleMapSurjectiveLocus`.
* best owner abstraction:
  `Module.support R (LinearMap.ker φ)` and `Module.support R (P₂ ⧸ LinearMap.range φ)`.
* layer:
  the numbered item is `source-facing` for maps of finite projective modules, while the kernel and
  cokernel support descriptions are `bridge/view` companions derived from those owner supports.
* primitive data:
  the map `φ : P₁ →ₗ[R] P₂`.
* derived API:
  fiber injectivity/surjectivity, their openness/localization statements, and fiber-bijectivity as
  the intersection of the injective and surjective loci.
-/

section

variable [Module.Finite R P₁] [Module.FinitePresentation R P₂]

/-- For a map from a finite module to a finitely presented module, injectivity on the residue-field
fiber is equivalent to vanishing of the kernel at that prime. -/
theorem fiber_injective_iff_not_mem_support_ker
    (φ : P₁ →ₗ[R] P₂) (p : PrimeSpectrum R) :
    Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) ↔
      p ∉ Module.support R (LinearMap.ker φ) := sorry

/-- The injective residue-fiber locus is the complement of the support of the kernel. -/
theorem moduleMapFiberInjectiveLocus_eq_compl_support_ker
    (φ : P₁ →ₗ[R] P₂) :
    { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) } =
      (Module.support R (LinearMap.ker φ))ᶜ := by
  ext p
  simpa [Set.mem_compl_iff] using fiber_injective_iff_not_mem_support_ker φ p

/-- For a map from a finite module to a finitely presented module, the injective residue-fiber
locus is open in `Spec R`. -/
-- Proof sketch: by `moduleMapFiberInjectiveLocus_eq_compl_support_ker`, this is the complement of
-- the support of `LinearMap.ker φ`, which is closed under the finite-generation input coming from
-- the finitely presented target.
theorem isOpen_moduleMapResidueInjectiveLocus_of_finite_of_finitePresentation
    (φ : P₁ →ₗ[R] P₂) :
    IsOpen { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) } :=
  sorry

/-- For a map from a finite module to a finitely presented module, inclusion of `D(f)` in the
injective residue-fiber locus forces the away-localized map over `R_f` to be injective. -/
-- Proof sketch: for every prime in `D(f)`, injectivity on the residue-field fiber implies
-- injectivity after localizing at that prime; then apply the local-to-global injectivity criterion
-- over `R_f`.
theorem injective_localizedAway_of_D_subset_moduleMapResidueInjectiveLocus_of_finite_of_finitePresentation
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hU :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) }) :
    Function.Injective (LocalizedModule.map (.powers f) φ) := sorry

end

section

variable [Module.Finite R P₁] [Module.Projective R P₁]
variable [Module.Finite R P₂] [Module.Projective R P₂]

/-- Lemma 10.79.4 (1): for a map between finite projective `R`-modules, the locus where the
residue-field fiber is injective is open in `Spec R`. -/
theorem isOpen_moduleMapResidueInjectiveLocus (φ : P₁ →ₗ[R] P₂) :
    IsOpen { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) } := by
  let _ : Module.Projective R P₁ := inferInstance
  letI : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  exact isOpen_moduleMapResidueInjectiveLocus_of_finite_of_finitePresentation φ

/-- Lemma 10.79.4 (2): if `D(f)` lies in the injective residue-fiber locus of a map between
finite projective `R`-modules, then the away-localized map over `R_f` is injective. -/
theorem injective_localizedAway_of_D_subset_moduleMapResidueInjectiveLocus
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hU :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) }) :
    Function.Injective (LocalizedModule.map (.powers f) φ) := by
  let _ : Module.Projective R P₁ := inferInstance
  letI : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  exact
    injective_localizedAway_of_D_subset_moduleMapResidueInjectiveLocus_of_finite_of_finitePresentation
      φ f hU

/-- Lemma 10.79.4 (3): if `D(f)` lies in the injective residue-fiber locus of a map between finite
projective `R`-modules, then the localized cokernel is finite projective over `R_f`. -/
-- Proof sketch: on a standard open where an appropriate maximal minor is invertible, identify the
-- cokernel with a finite free summand of the localized codomain, and then glue this local finite
-- projective description on `D(f)`.
theorem cokernel_localizedAway_finiteProjective_of_D_subset_moduleMapResidueInjectiveLocus
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hU :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) }) :
    Module.Finite (Localization.Away f) (LocalizedModule.Away f (P₂ ⧸ LinearMap.range φ)) ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f (P₂ ⧸ LinearMap.range φ)) :=
  sorry

/-- Lemma 10.79.4 (4): for a map between finite projective `R`-modules, the locus where the
residue-field fiber is surjective is open in `Spec R`. -/
-- Proof sketch: by `moduleMapFiberSurjectiveLocus_eq_compl_support_cokernel`, this locus is the
-- complement of the cokernel support, which is closed because finite projective modules are
-- finite.
theorem isOpen_moduleMapResidueSurjectiveLocus (φ : P₁ →ₗ[R] P₂) :
    IsOpen { p : PrimeSpectrum R | Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) } := by
  let _ : Module.Finite R P₁ := inferInstance
  let _ : Module.Projective R P₁ := inferInstance
  let _ : Module.Projective R P₂ := inferInstance
  rw [moduleMapFiberSurjectiveLocus_eq_compl_support_cokernel φ]
  exact Module.isClosed_support.isOpen_compl

/-- Lemma 10.79.4 (5): if `D(f)` lies in the surjective residue-fiber locus of a map between
finite projective `R`-modules, then the away-localized map over `R_f` is surjective. -/
-- Proof sketch: this is exactly the owner theorem
-- `surjective_localizedAway_of_D_subset_moduleMapSurjectiveLocus` from `10.79.1`.
theorem surjective_localizedAway_of_D_subset_moduleMapResidueSurjectiveLocus
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hW :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) }) :
    Function.Surjective (LocalizedModule.map (.powers f) φ) := by
  let _ : Module.Finite R P₁ := inferInstance
  let _ : Module.Projective R P₁ := inferInstance
  let _ : Module.Projective R P₂ := inferInstance
  have hW' :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) } := by
    simpa [moduleMapSurjectiveLocus_eq_moduleMapFiberSurjectiveLocus φ] using hW
  exact surjective_localizedAway_of_D_subset_moduleMapSurjectiveLocus
    φ f hW'

/-- Lemma 10.79.4 (6): if `D(f)` lies in the surjective residue-fiber locus of a map from a finite
projective `R`-module onto a finite projective `R`-module, then the localized kernel is finite
projective over `R_f`. -/
-- Proof sketch: after localizing away from `f`, the surjective map onto a projective module splits,
-- so the kernel is a direct summand of a finite projective module and hence is itself finite
-- projective.
theorem kernel_localizedAway_finiteProjective_of_D_subset_moduleMapResidueSurjectiveLocus
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hW :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) }) :
    Module.Finite (Localization.Away f) (LocalizedModule.Away f (LinearMap.ker φ)) ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f (LinearMap.ker φ)) := sorry

/-- Lemma 10.79.4 (7): for a map between finite projective `R`-modules, the locus where the
residue-field fiber is bijective is open in `Spec R`. -/
-- Proof sketch: the bijective fiber locus is the intersection of the injective and surjective
-- fiber loci.
theorem isOpen_moduleMapResidueBijectiveLocus (φ : P₁ →ₗ[R] P₂) :
    IsOpen { p : PrimeSpectrum R | Function.Bijective (LinearMap.rTensor p.asIdeal.ResidueField φ) } := by
  simpa [Function.Bijective, Set.setOf_and] using
    (isOpen_moduleMapResidueInjectiveLocus φ).inter
      (isOpen_moduleMapResidueSurjectiveLocus φ)

/-- Lemma 10.79.4 (8): if `D(f)` lies in the bijective residue-fiber locus of a map between finite
projective `R`-modules, then the away-localized map over `R_f` is bijective. -/
-- Proof sketch: a bijective fiber map is both injective and surjective on every prime of `D(f)`;
-- apply the localized injective and surjective statements and combine the conclusions.
theorem bijective_localizedAway_of_D_subset_moduleMapResidueBijectiveLocus
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hV :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Bijective (LinearMap.rTensor p.asIdeal.ResidueField φ) }) :
    Function.Bijective (LocalizedModule.map (.powers f) φ) := by
  refine ⟨?_, ?_⟩
  · exact injective_localizedAway_of_D_subset_moduleMapResidueInjectiveLocus
      φ f fun p hp ↦ (hV hp).1
  · exact surjective_localizedAway_of_D_subset_moduleMapResidueSurjectiveLocus
      φ f fun p hp ↦ (hV hp).2

end

end
