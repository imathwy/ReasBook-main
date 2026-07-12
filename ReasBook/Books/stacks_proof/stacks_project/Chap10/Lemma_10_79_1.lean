import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1

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

/-- Helper for Chap10 Lemma 10 79 1: localizing `φ` at a submonoid is surjective exactly when
the localized cokernel is trivial. -/
lemma localized_map_surjective_iff_subsingleton_cokernel
    (φ : M →ₗ[R] N) (S : Submonoid R) :
    Function.Surjective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (N ⧸ LinearMap.range φ)) := by
  let ψ : LocalizedModule S M →ₗ[Localization S] LocalizedModule S N := LocalizedModule.map S φ
  have hRange :
      LinearMap.range ψ = (LinearMap.range φ).localized S := by
    -- Identify the range of the localized map with the localization of the original range.
    symm
    simpa [ψ, Submodule.localized] using
      (LinearMap.localized'_range_eq_range_localizedMap
        (S := Localization S)
        (p := S)
        (f := LocalizedModule.mkLinearMap S M)
        (f' := LocalizedModule.mkLinearMap S N)
        φ)
  let eQuot :
      (LocalizedModule S N ⧸ (LinearMap.range φ).localized S) ≃ₗ[Localization S]
        LocalizedModule S (N ⧸ LinearMap.range φ) :=
    localizedQuotientEquiv
      (p := S)
      (M' := LinearMap.range φ)
  let e :
      (LocalizedModule S N ⧸ LinearMap.range ψ) ≃ₗ[Localization S]
        LocalizedModule S (N ⧸ LinearMap.range φ) :=
    (Submodule.quotEquivOfEq _ _ hRange).trans eQuot
  constructor
  · intro hφ
    have hsub :
        Subsingleton (LocalizedModule S N ⧸ LinearMap.range ψ) := by
      -- A surjective localized map has quotient by its range equal to the zero module.
      exact (Submodule.Quotient.subsingleton_iff).2 (LinearMap.range_eq_top.2 hφ)
    exact (e.toEquiv.subsingleton_congr).1 hsub
  · intro hsub
    have hsub' :
        Subsingleton (LocalizedModule S N ⧸ LinearMap.range ψ) :=
      (e.toEquiv.subsingleton_congr).2 hsub
    -- Triviality of the localized cokernel says that the localized range is the whole codomain.
    exact LinearMap.range_eq_top.1 ((Submodule.Quotient.subsingleton_iff).1 hsub')

/-- Helper for Chap10 Lemma 10 79 1: after tensoring on the right, a map is surjective exactly
when the tensor of its cokernel is trivial. -/
private lemma rTensor_surjective_iff_subsingleton_tensor_cokernel
    {Q : Type*} [AddCommGroup Q] [Module R Q] (φ : M →ₗ[R] N) :
    Function.Surjective (LinearMap.rTensor Q φ) ↔
      Subsingleton ((N ⧸ LinearMap.range φ) ⊗[R] Q) := by
  let π : N →ₗ[R] N ⧸ LinearMap.range φ := (LinearMap.range φ).mkQ
  let F : (M ⊗[R] Q) →ₗ[R] (N ⊗[R] Q) := LinearMap.rTensor Q φ
  let G : (N ⊗[R] Q) →ₗ[R] ((N ⧸ LinearMap.range φ) ⊗[R] Q) :=
    LinearMap.rTensor Q π
  have hExact : Function.Exact F G := by
    -- Tensor the exact cokernel sequence `M → N → N ⧸ range φ`.
    simpa [F, G, π] using
      rTensor_exact Q (LinearMap.exact_map_mkQ_range φ)
        (Submodule.mkQ_surjective (LinearMap.range φ))
  have hGsurj : Function.Surjective G := by
    -- The tensor of the quotient map is still surjective.
    simpa [G, π] using
      LinearMap.rTensor_surjective Q (Submodule.mkQ_surjective (LinearMap.range φ))
  constructor
  · intro hF
    have hF' : Function.Surjective F := by
      simpa [F] using hF
    refine ⟨?_⟩
    intro z z'
    obtain ⟨y, rfl⟩ := hGsurj z
    obtain ⟨y', rfl⟩ := hGsurj z'
    obtain ⟨x, rfl⟩ := hF' y
    obtain ⟨x', rfl⟩ := hF' y'
    have hcomp : G.comp F = 0 := Function.Exact.linearMap_comp_eq_zero hExact
    have hx : G (F x) = 0 := DFunLike.congr_fun hcomp x
    have hx' : G (F x') = 0 := DFunLike.congr_fun hcomp x'
    simpa [hx, hx']
  · intro hSub y
    -- If the cokernel tensor is trivial, every element lies in the exact image.
    have hy : G y = 0 := Subsingleton.elim (G y) 0
    exact (hExact y).mp hy

/-- Helper for Chap10 Lemma 10 79 1: the tensor of the cokernel with the residue field is trivial
exactly when the residue-field fiber map is surjective. -/
lemma tensor_cokernel_subsingleton_iff_rTensor_surjective [Module.Finite R N]
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Subsingleton ((N ⧸ LinearMap.range φ) ⊗[R] p.asIdeal.ResidueField) ↔
      Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) := by
  -- Specialize the general tensor-cokernel criterion to the residue field and reverse it.
  exact (rTensor_surjective_iff_subsingleton_tensor_cokernel φ).symm

/-- Helper for Chap10 Lemma 10 79 1: avoiding the support of a finite module is equivalent to
the right residue-field tensor being trivial. -/
private lemma notMem_support_iff_subsingleton_tensor_residueField
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] (p : PrimeSpectrum R) :
    p ∉ Module.support R Q ↔ Subsingleton (Q ⊗[R] p.asIdeal.ResidueField) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  constructor
  · intro hnot
    have hLeft : Subsingleton (p.asIdeal.ResidueField ⊗[R] Q) :=
      not_nontrivial_iff_subsingleton.mp hnot
    -- Commute the two tensor factors to match the cokernel convention used in the fiber map.
    exact ((TensorProduct.comm R p.asIdeal.ResidueField Q).toEquiv.subsingleton_congr).1 hLeft
  · intro hRight
    have hLeft : Subsingleton (p.asIdeal.ResidueField ⊗[R] Q) :=
      ((TensorProduct.comm R p.asIdeal.ResidueField Q).toEquiv.subsingleton_congr).2 hRight
    -- A subsingleton residue-field tensor is precisely non-membership in the support.
    exact not_nontrivial_iff_subsingleton.mpr hLeft

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
      p ∉ Module.support R (N ⧸ LinearMap.range φ) := by
  -- Chain fiber surjectivity through the tensor cokernel and then through support avoidance.
  exact (tensor_cokernel_subsingleton_iff_rTensor_surjective φ p).symm.trans
    (notMem_support_iff_subsingleton_tensor_residueField p).symm

/-- The residue-field fiber surjectivity locus is the complement of the support of the cokernel. -/
theorem moduleMapFiberSurjectiveLocus_eq_compl_support_cokernel [Module.Finite R N]
    (φ : M →ₗ[R] N) :
    { p : PrimeSpectrum R | Function.Surjective (LinearMap.rTensor p.asIdeal.ResidueField φ) } =
      (Module.support R (N ⧸ LinearMap.range φ))ᶜ := by
  ext p
  simpa [Set.mem_compl_iff] using fiber_surjective_iff_not_mem_support_cokernel φ p

/-- Chap10 Lemma 10 79 1 (Lemma 10.79.1 (1)): for a map `φ : M →ₗ[R] N` with `N` finite,
the locus where the localized map `φₚ : Mₚ → Nₚ` is surjective is exactly the locus where the fiber map
`M ⊗[R] κ(p) → N ⊗[R] κ(p)` is surjective. -/
-- Proof sketch: fix `p`. Over the local ring `Rₚ`, surjectivity of `φₚ` is equivalent by
-- Nakayama's lemma to surjectivity modulo the maximal ideal, and the latter is exactly
-- surjectivity after tensoring with `κ(p)`.
@[stacks 05GE]
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
@[stacks 05GE]
theorem isOpen_moduleMapSurjectiveLocus [Module.Finite R N] (φ : M →ₗ[R] N) :
    IsOpen { p : PrimeSpectrum R | Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl φ) } := by
  rw [moduleMapSurjectiveLocus_eq_compl_support_cokernel φ]
  exact Module.isClosed_support.isOpen_compl

/-- Lemma 10.79.1 (3): if the basic open `D(f)` is contained in the surjectivity locus of `φ`,
then the localized map `M_f → N_f` is surjective. -/
-- Proof sketch: every maximal ideal of `Localization.Away f` comes from a prime of `R` lying in
-- `D(f)`, so the hypothesis implies surjectivity after localizing `φ_f` at every maximal ideal of
-- `R_f`. Apply the local-to-global surjectivity criterion `surjective_of_localized_maximal`.
@[stacks 05GE]
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
