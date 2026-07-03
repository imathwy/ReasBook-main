import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_79_1 (from Chap10) -/
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

/-! ### Lemma_10_79_2 (from Chap10) -/
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

/-! ### Lemma_10_79_3 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (p : Ideal R) [p.IsPrime]
variable [Module.FinitePresentation R M]

/- Domain-style sampling:
* primary domain: localization descent for free finitely presented modules.
* sampled owner declarations:
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`,
  `Module.isOpen_freeLocus`.
* best owner abstraction: the canonical localized module map
  `LocalizedModule.mkLinearMap p.primeCompl M`; freeness after localization at a submonoid is the
  primitive owner statement, while primewise and open-locus formulations are derived views.
* layer: `bridge/view`; this item specializes the submonoid owner theorem to the complement of the
  prime ideal `p` and rewrites membership in `p.primeCompl` as the source-facing condition `f ∉ p`.
* primitive data: `M` and its canonical localization map at `p.primeCompl`.
* derived API: the witness `f ∉ p` and the away-localized freeness statement.
-/

-- Proof sketch: apply `Module.FinitePresentation.exists_free_localizedModule_powers` to the
-- canonical localization map `M → M_p` for the submonoid `p.primeCompl`. Since `M_p` is free, this
-- yields some `f ∈ p.primeCompl` such that `M` localized at the powers of `f` is free. Rewriting
-- `f ∈ p.primeCompl` as `f ∉ p` and the powers-localization as localization away from `f` gives
-- the stated result.
/-- Lemma 10.79.3: if a finitely presented `R`-module becomes free after localizing at the prime
ideal `p`, then there exists `f ∈ R` with `f ∉ p` such that localization away from `f` is a free
`R_f`-module. -/
theorem exists_not_mem_prime_localizedAway_free_of_localizedAtPrime_free
    [Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p M)] :
    ∃ f : R, f ∉ p ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨f, hf, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  exact ⟨f, hf, hfree⟩

end
