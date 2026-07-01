import Mathlib
import stacks_project.Chap10.Lemma_10_79_1

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

/-- Helper for Lemma 10.79.2: after localizing at `p`, injectivity of `φ` is equivalent to the
localized kernel vanishing. -/
lemma localized_injective_iff_not_mem_support_ker
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Injective (LocalizedModule.map p.asIdeal.primeCompl φ) ↔
      p ∉ Module.support R (LinearMap.ker φ) := by
  let κ : LinearMap.ker φ →ₗ[R] LinearMap.ker (LocalizedModule.map p.asIdeal.primeCompl φ) :=
    LinearMap.toKerIsLocalized
      (p := p.asIdeal.primeCompl)
      (f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (f' := LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
      φ
  let _ : IsLocalizedModule p.asIdeal.primeCompl κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization.AtPrime p.asIdeal)
      (p := p.asIdeal.primeCompl)
      (f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (f' := LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
      φ
  -- Compare the localized kernel module with the actual kernel of the localized map.
  rw [Module.notMem_support_iff]
  constructor
  · intro hφ
    have hker :
        LinearMap.ker (LocalizedModule.map p.asIdeal.primeCompl φ) = ⊥ :=
      LinearMap.ker_eq_bot.2 hφ
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map p.asIdeal.primeCompl φ)) :=
      Submodule.subsingleton_iff_eq_bot.2 hker
    exact ((IsLocalizedModule.iso p.asIdeal.primeCompl κ).toEquiv.subsingleton_congr).2 hsub
  · intro hker
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map p.asIdeal.primeCompl φ)) :=
      ((IsLocalizedModule.iso p.asIdeal.primeCompl κ).toEquiv.subsingleton_congr).1 hker
    exact LinearMap.ker_eq_bot.1 (Submodule.subsingleton_iff_eq_bot.1 hsub)

/-- A localized map is bijective exactly away from the supports of its kernel and cokernel. -/
theorem localized_bijective_iff_not_mem_support_ker_and_cokernel
    (φ : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ) ↔
      p ∉ Module.support R (LinearMap.ker φ) ∧
        p ∉ Module.support R (N ⧸ LinearMap.range φ) := by
  -- Split bijectivity into injectivity and surjectivity, then apply the owner lemmas for the
  -- kernel and cokernel supports separately.
  constructor
  · intro hbij
    exact ⟨
      (localized_injective_iff_not_mem_support_ker φ p).1 hbij.1,
      (localized_surjective_iff_not_mem_support_cokernel φ p).1 hbij.2
    ⟩
  · rintro ⟨hinj, hsurj⟩
    exact ⟨
      (localized_injective_iff_not_mem_support_ker φ p).2 hinj,
      (localized_surjective_iff_not_mem_support_cokernel φ p).2 hsurj
    ⟩

/-- Helper for Lemma 10.79.2: the localized isomorphism locus is the intersection of the
complements of the kernel and cokernel supports. -/
lemma moduleMapIsomorphismLocus_eq_compl_support_ker_inter_compl_support_cokernel
    (φ : M →ₗ[R] N) :
    { p : PrimeSpectrum R | Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ) } =
      (Module.support R (LinearMap.ker φ))ᶜ ∩
        (Module.support R (N ⧸ LinearMap.range φ))ᶜ := by
  ext p
  -- Rewrite pointwise membership using the bijectivity/support criterion.
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  exact localized_bijective_iff_not_mem_support_ker_and_cokernel φ p

/-- Helper for Lemma 10.79.2: after localizing at a submonoid `S`, injectivity of `φ` is
equivalent to the localized kernel vanishing. -/
lemma localized_map_injective_iff_subsingleton_ker
    (φ : M →ₗ[R] N) (S : Submonoid R) :
    Function.Injective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (LinearMap.ker φ)) := by
  let κ : LinearMap.ker φ →ₗ[R] LinearMap.ker (LocalizedModule.map S φ) :=
    LinearMap.toKerIsLocalized
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  let _ : IsLocalizedModule S κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization S)
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  -- Compare the localized kernel module with the actual kernel after localizing the map.
  constructor
  · intro hφ
    have hker :
        LinearMap.ker (LocalizedModule.map S φ) = ⊥ :=
      LinearMap.ker_eq_bot.2 hφ
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      Submodule.subsingleton_iff_eq_bot.2 hker
    exact ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).2 hsub
  · intro hker
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).1 hker
    exact LinearMap.ker_eq_bot.1 (Submodule.subsingleton_iff_eq_bot.1 hsub)

/-- Helper for Lemma 10.79.2: a bijection after localizing away from `f` stays a bijection at
every prime in `D(f)`. -/
lemma basicOpen_subset_moduleMapIsomorphismLocus_of_bijective_away
    (φ : M →ₗ[R] N) {f : R}
    (hbij : Function.Bijective (LocalizedModule.map (.powers f) φ)) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
      { p : PrimeSpectrum R | Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl φ) } := by
  intro p hp
  -- Vanishing of the away-localized kernel and cokernel forces the whole basic open to avoid
  -- both supports.
  have hker_sub :
      Subsingleton (LocalizedModule (.powers f) (LinearMap.ker φ)) :=
    (localized_map_injective_iff_subsingleton_ker φ (.powers f)).1 hbij.1
  have hcoker_sub :
      Subsingleton (LocalizedModule (.powers f) (N ⧸ LinearMap.range φ)) :=
    (localized_map_surjective_iff_subsingleton_cokernel φ (.powers f)).1 hbij.2
  have hdisj_ker :
      Disjoint ↑(PrimeSpectrum.basicOpen f) (Module.support R (LinearMap.ker φ)) := by
    rw [← LocalizedModule.subsingleton_iff_disjoint]
    exact hker_sub
  have hdisj_coker :
      Disjoint ↑(PrimeSpectrum.basicOpen f) (Module.support R (N ⧸ LinearMap.range φ)) := by
    rw [← LocalizedModule.subsingleton_iff_disjoint]
    exact hcoker_sub
  have hp_not_ker : p ∉ Module.support R (LinearMap.ker φ) := by
    intro hpker
    exact Set.disjoint_left.mp hdisj_ker hp hpker
  have hp_not_coker : p ∉ Module.support R (N ⧸ LinearMap.range φ) := by
    intro hpcoker
    exact Set.disjoint_left.mp hdisj_coker hp hpcoker
  -- The pointwise criterion from the support description finishes the localization step.
  exact (localized_bijective_iff_not_mem_support_ker_and_cokernel φ p).2
    ⟨hp_not_ker, hp_not_coker⟩

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
  by
  -- Route correction: the proof is local around each prime, so we use the finite-presentation
  -- basic-open shrinking theorem instead of a false global closedness claim for `support (ker φ)`.
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff]
  intro p hp
  have hp' :
      Function.Bijective
        (IsLocalizedModule.map p.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
          φ) := by
    -- Rewrite the pointwise localized map into the `IsLocalizedModule.map` form expected by the
    -- finite-presentation theorem.
    rw [IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)]
    exact hp
  obtain ⟨g, hg, hbij⟩ :=
    Module.FinitePresentation.exists_notMem_bijective
      (f := φ)
      (p := p.asIdeal)
      (fM := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
      (fN := LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
      hp'
  -- The resulting distinguished open is contained in the isomorphism locus by the away-local
  -- support criterion proved above.
  refine ⟨PrimeSpectrum.basicOpen g, ⟨g, rfl⟩, ?_, ?_⟩
  · exact (PrimeSpectrum.mem_basicOpen g p).2 hg
  · exact basicOpen_subset_moduleMapIsomorphismLocus_of_bijective_away φ hbij

end
