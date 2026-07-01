import stacks_project.Chap10.Definition_10_17_1
import stacks_project.Chap10.Lemma_10_17_6
import stacks_project.Chap10.Lemma_10_55_8
import stacks_project.Chap10.Lemma_10_79_1
import stacks_project.Chap10.Lemma_10_79_2
import stacks_project.Chap10.Lemma_10_79_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open PrimeSpectrum
open scoped PrimeSpectrum
open scoped TensorProduct

section

variable {R : Type u} [CommRing R]
variable {P₁ : Type v} [AddCommGroup P₁] [Module R P₁]
variable {P₂ : Type w} [AddCommGroup P₂] [Module R P₂]

/-- Helper for Lemma 10.79.4: a split surjection exhibits the source as the direct sum of the
range of the section and the kernel. -/
lemma range_isCompl_ker_of_split
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ψ : M →ₗ[A] N) (σ : N →ₗ[A] M) (hσ : ψ.comp σ = LinearMap.id) :
    IsCompl (LinearMap.range σ) (LinearMap.ker ψ) := by
  let e : M →ₗ[A] M := σ.comp ψ
  have he : IsIdempotentElem e := by
    -- The projector `σ ∘ ψ` is idempotent because `ψ ∘ σ = id`.
    change e * e = e
    ext x
    change σ (ψ (σ (ψ x))) = σ (ψ x)
    have hψσ : ψ (σ (ψ x)) = ψ x := by
      simpa using congrArg (fun f : N →ₗ[A] N => f (ψ x)) hσ
    rw [hψσ]
  have hrange : LinearMap.range e = LinearMap.range σ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨ψ y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨σ y, ?_⟩
      change σ (ψ (σ y)) = σ y
      have hψσ : ψ (σ y) = y := by
        simpa using congrArg (fun f : N →ₗ[A] N => f y) hσ
      rw [hψσ]
  have hker : LinearMap.ker e = LinearMap.ker ψ := by
    ext x
    constructor
    · intro hx
      change σ (ψ x) = 0 at hx
      have hψx : ψ (σ (ψ x)) = 0 := by
        simpa using congrArg ψ hx
      have hψσ : ψ (σ (ψ x)) = ψ x := by
        simpa using congrArg (fun f : N →ₗ[A] N => f (ψ x)) hσ
      rw [hψσ] at hψx
      exact hψx
    · intro hx
      change σ (ψ x) = 0
      simpa using congrArg σ hx
  -- Transport the standard range/kernel complement for an idempotent endomorphism.
  simpa [hrange, hker] using LinearMap.IsIdempotentElem.isCompl (f := e) he

/-- Helper for Lemma 10.79.4: the kernel of a split surjection onto a projective module is
projective. -/
lemma kernel_projective_of_split_surjective
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ψ : M →ₗ[A] N) (σ : N →ₗ[A] M) (hσ : ψ.comp σ = LinearMap.id)
    [Module.Projective A M] :
    Module.Projective A (LinearMap.ker ψ) := by
  let hCompl : IsCompl (LinearMap.ker ψ) (LinearMap.range σ) :=
    (range_isCompl_ker_of_split ψ σ hσ).symm
  -- The projection onto the kernel gives the required splitting.
  exact Module.Projective.of_split
    (LinearMap.ker ψ).subtype
    ((LinearMap.ker ψ).linearProjOfIsCompl (LinearMap.range σ) hCompl)
    (Submodule.linearProjOfIsCompl_comp_subtype hCompl)

/-- Helper for Lemma 10.79.4: the cokernel of a split injection into a projective module is
projective. -/
lemma cokernel_projective_of_split_injective
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ψ : M →ₗ[A] N) (σ : N →ₗ[A] M) (hσ : σ.comp ψ = LinearMap.id)
    [Module.Projective A N] :
    Module.Projective A (N ⧸ LinearMap.range ψ) := by
  let hCompl : IsCompl (LinearMap.range ψ) (LinearMap.ker σ) :=
    range_isCompl_ker_of_split σ ψ hσ
  have hprojKer : Module.Projective A (LinearMap.ker σ) :=
    kernel_projective_of_split_surjective σ ψ hσ
  let e :
      (N ⧸ LinearMap.range ψ) ≃ₗ[A] LinearMap.ker σ :=
    Submodule.quotientEquivOfIsCompl (LinearMap.range ψ) (LinearMap.ker σ) hCompl
  -- Transport projectivity across the quotient/kernel equivalence coming from the splitting.
  let _ : Module.Projective A (LinearMap.ker σ) := hprojKer
  exact Module.Projective.of_equiv e.symm

/-- Helper for Lemma 10.79.4: injectivity transfers across a commuting square of linear
equivalences. -/
lemma injective_of_ladder_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {φ : A →ₗ[R] B} {ψ : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : ψ.comp e₁.toLinearMap = e₂.toLinearMap.comp φ)
    (hφ : Function.Injective φ) :
    Function.Injective ψ := by
  -- Pull the equality back through the two equivalences and use injectivity of the known side.
  intro x y hxy
  apply e₁.symm.injective
  apply hφ
  apply e₂.injective
  calc
    e₂ (φ (e₁.symm x)) = ψ x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = ψ y := hxy
    _ = e₂ (φ (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

/-- Helper for Lemma 10.79.4: changing the tensor factor by a linear equivalence preserves
injectivity of the tensorized map. -/
lemma injective_rTensor_of_linearEquiv
    {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M']
    {Q P : Type*} [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    (φ : M →ₗ[R] M') (e : Q ≃ₗ[R] P)
    (hP : Function.Injective (φ.rTensor P)) :
    Function.Injective (φ.rTensor Q) := by
  let eM : TensorProduct R M Q ≃ₗ[R] TensorProduct R M P := e.lTensor M
  let eM' : TensorProduct R M' Q ≃ₗ[R] TensorProduct R M' P := e.lTensor M'
  have hSquare :
      (φ.rTensor Q).comp eM.symm.toLinearMap =
        eM'.symm.toLinearMap.comp (φ.rTensor P) := by
    -- The two tensor maps commute with the linear equivalence induced by `e`.
    apply TensorProduct.ext'
    intro x y
    simp [eM, eM', LinearEquiv.lTensor]
  exact injective_of_ladder_linearEquiv hSquare hP

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

section

variable [Module.Finite R P₁] [Module.Projective R P₁]
variable [Module.Finite R P₂] [Module.Projective R P₂]

/-- Helper for Lemma 10.79.4: after localizing at a prime, both finite projective modules become
free over the local ring. -/
lemma localizedAtPrime_free_pair
    (p : PrimeSpectrum R) :
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₁) ∧
      Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₂) := by
  -- Over the local ring `R_p`, finite projective modules are free by Lemma `10.55.8`.
  letI : Module.Projective (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₁) :=
    Module.projective_of_isLocalizedModule
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁)
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₁) :=
    finite_projective_module_free_of_isLocalRing (R := Localization.AtPrime p.asIdeal)
  letI : Module.Projective (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₂) :=
    Module.projective_of_isLocalizedModule
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₂)
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₂) :=
    finite_projective_module_free_of_isLocalRing (R := Localization.AtPrime p.asIdeal)
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 10.79.4: near any prime, both finite projective modules admit one common
basic-open chart contained in their free loci. -/
lemma exists_not_mem_prime_basicOpen_subset_freeLocus_pair
    (p : PrimeSpectrum R) :
    ∃ g : R, g ∉ p.asIdeal ∧
      (D(g) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₁ ∧
      (D(g) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₂ := by
  letI : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  letI : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₁) :=
    (localizedAtPrime_free_pair (P₁ := P₁) (P₂ := P₂) p).1
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal P₂) :=
    (localizedAtPrime_free_pair (P₁ := P₁) (P₂ := P₂) p).2
  obtain ⟨g₁, hg₁, hfree₁⟩ :=
    exists_not_mem_prime_localizedAway_free_of_localizedAtPrime_free
      (p := p.asIdeal) (M := P₁)
  obtain ⟨g₂, hg₂, hfree₂⟩ :=
    exists_not_mem_prime_localizedAway_free_of_localizedAtPrime_free
      (p := p.asIdeal) (M := P₂)
  have hg : g₁ * g₂ ∉ p.asIdeal := by
    -- The product basic open still contains `p` because neither factor vanishes there.
    intro hg
    exact hg₁ ((p.isPrime.mem_or_mem hg).resolve_right hg₂)
  have hsubset₁ :
      (PrimeSpectrum.basicOpen (g₁ * g₂) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₁ := by
    have hsubset_g₁ :
        (PrimeSpectrum.basicOpen g₁ : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₁ := by
      -- Repackage the first one-chart freeness witness as a free-locus inclusion.
      rw [Module.basicOpen_subset_freeLocus_iff]
      letI : Module.Free (Localization.Away g₁) (LocalizedModule.Away g₁ P₁) := hfree₁
      infer_instance
    intro q hq
    apply hsubset_g₁
    refine (PrimeSpectrum.mem_basicOpen g₁ q).2 ?_
    intro hg₁q
    exact ((PrimeSpectrum.mem_basicOpen (g₁ * g₂) q).1 hq)
      (by simpa [mul_comm] using q.asIdeal.mul_mem_left g₂ hg₁q)
  have hsubset₂ :
      (PrimeSpectrum.basicOpen (g₁ * g₂) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₂ := by
    have hsubset_g₂ :
        (PrimeSpectrum.basicOpen g₂ : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₂ := by
      -- Repackage the second one-chart freeness witness as a free-locus inclusion.
      rw [Module.basicOpen_subset_freeLocus_iff]
      letI : Module.Free (Localization.Away g₂) (LocalizedModule.Away g₂ P₂) := hfree₂
      infer_instance
    intro q hq
    apply hsubset_g₂
    refine (PrimeSpectrum.mem_basicOpen g₂ q).2 ?_
    intro hg₂q
    exact ((PrimeSpectrum.mem_basicOpen (g₁ * g₂) q).1 hq)
      (q.asIdeal.mul_mem_left g₁ hg₂q)
  exact ⟨g₁ * g₂, hg, hsubset₁, hsubset₂⟩

/-- Helper for Lemma 10.79.4: a common basic-open chart inside both free loci yields projective
away-localized modules on that chart. -/
lemma away_projective_pair_of_basicOpen_subset_freeLocus_pair
    (g : R)
    (hP₁ : (D(g) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₁)
    (hP₂ : (D(g) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₂) :
    Module.Projective (Localization.Away g) (LocalizedModule.Away g P₁) ∧
      Module.Projective (Localization.Away g) (LocalizedModule.Away g P₂) := by
  letI : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  letI : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  constructor
  · -- Convert the first free-locus inclusion into the concrete away-local projectivity instance.
    rw [Module.basicOpen_subset_freeLocus_iff] at hP₁
    exact hP₁
  · -- Convert the second free-locus inclusion into the same away-local projectivity instance.
    rw [Module.basicOpen_subset_freeLocus_iff] at hP₂
    exact hP₂

/-- Helper for Lemma 10.79.4: after passing to a prime of the common away chart, the twice
localized modules are free over the resulting local ring. -/
lemma localizedAwayAtPrime_free_pair_of_basicOpen_subset_freeLocus_pair
    (g : R) (q : PrimeSpectrum (Localization.Away g))
    (hP₁ : (D(g) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₁)
    (hP₂ : (D(g) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R P₂) :
    Module.Free (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal (LocalizedModule.Away g P₁)) ∧
      Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (LocalizedModule.Away g P₂)) := by
  obtain ⟨hproj₁, hproj₂⟩ :=
    away_projective_pair_of_basicOpen_subset_freeLocus_pair
      (P₁ := P₁) (P₂ := P₂) g hP₁ hP₂
  constructor
  · letI : Module.Projective (Localization.Away g) (LocalizedModule.Away g P₁) := hproj₁
    letI : Module.Projective (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (LocalizedModule.Away g P₁)) :=
      Module.projective_of_isLocalizedModule
        q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (LocalizedModule.Away g P₁))
    -- Localizing the common projective chart at `q` puts us over a local ring, so the finite
    -- projective module becomes free.
    letI : Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (LocalizedModule.Away g P₁)) :=
      finite_projective_module_free_of_isLocalRing (R := Localization.AtPrime q.asIdeal)
    infer_instance
  · letI : Module.Projective (Localization.Away g) (LocalizedModule.Away g P₂) := hproj₂
    letI : Module.Projective (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (LocalizedModule.Away g P₂)) :=
      Module.projective_of_isLocalizedModule
        q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (LocalizedModule.Away g P₂))
    -- The same local-ring argument upgrades the second twice-localized module to a free chart.
    letI : Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (LocalizedModule.Away g P₂)) :=
      finite_projective_module_free_of_isLocalRing (R := Localization.AtPrime q.asIdeal)
    infer_instance

end

variable [Module.Finite R P₁] [Module.FinitePresentation R P₂]

/-- Helper for Lemma 10.79.4: localized injectivity is equivalent to avoiding the support of the
kernel. -/
theorem localized_injective_iff_not_mem_support_ker_of_finite_of_finitePresentation
    (φ : P₁ →ₗ[R] P₂) (p : PrimeSpectrum R) :
    Function.Injective (LocalizedModule.map p.asIdeal.primeCompl φ) ↔
      p ∉ Module.support R (LinearMap.ker φ) := by
  -- Reuse the earlier localized support criterion instead of the false residue-fiber version.
  exact localized_injective_iff_not_mem_support_ker φ p

/-- Helper for Lemma 10.79.4: the localized injective locus is the complement of the kernel
support. -/
theorem moduleMapLocalizedInjectiveLocus_eq_compl_support_ker
    (φ : P₁ →ₗ[R] P₂) :
    { p : PrimeSpectrum R | Function.Injective (LocalizedModule.map p.asIdeal.primeCompl φ) } =
      (Module.support R (LinearMap.ker φ))ᶜ := by
  ext p
  simpa [Set.mem_compl_iff] using
    localized_injective_iff_not_mem_support_ker_of_finite_of_finitePresentation φ p

/-- Helper for Lemma 10.79.4: if every localized map on `D(f)` is injective, then the away
localization away from `f` is injective. -/
lemma injective_localizedAway_of_basicOpen_localizedInjective
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hlocal :
      ∀ q ∈ (D(f) : Set (PrimeSpectrum R)),
        Function.Injective (LocalizedModule.map q.asIdeal.primeCompl φ)) :
    Function.Injective (LocalizedModule.map (.powers f) φ) := by
  have hsub :
      Subsingleton (LocalizedModule (.powers f) (LinearMap.ker φ)) := by
    -- The support of the kernel misses the whole basic open once every localization there is
    -- injective.
    rw [LocalizedModule.subsingleton_iff_disjoint]
    refine Set.disjoint_left.2 ?_
    intro q hq_basic hq_support
    exact ((localized_injective_iff_not_mem_support_ker_of_finite_of_finitePresentation φ q).1
      (hlocal q hq_basic)) hq_support
  -- Convert the vanishing of the away-localized kernel back into injectivity of the away map.
  exact (localized_map_injective_iff_subsingleton_ker φ (.powers f)).2 hsub

/-- Helper for Lemma 10.79.4: a basic-open neighborhood of the chart point in `Spec(R_g)` refines
to one single distinguished open `D(g * a)` in `Spec R`. -/
lemma exists_basicOpen_refining_away_element
    (g : R) (p : PrimeSpectrum R) (hg : g ∉ p.asIdeal)
    (δ : Localization.Away g)
    (hδ :
      δ ∉ ((primeSpectrum_localizationAway_homeomorph_D g).symm ⟨p, (mem_D g p).2 hg⟩).asIdeal) :
    ∃ a : R, a ∉ p.asIdeal ∧
      (PrimeSpectrum.basicOpen (g * a) : Set (PrimeSpectrum R)) ⊆
        PrimeSpectrum.comap (algebraMap R (Localization.Away g)) ''
          (D(δ) : Set (PrimeSpectrum (Localization.Away g))) := by
  let q : PrimeSpectrum (Localization.Away g) :=
    (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨p, (mem_D g p).2 hg⟩
  have hq_mem :
      q ∈ (D(δ) : Set (PrimeSpectrum (Localization.Away g))) :=
    -- The chosen element `δ` is invertible at the chart point `q`.
    (PrimeSpectrum.mem_basicOpen δ q).2 hδ
  have hp_mem :
      p ∈ PrimeSpectrum.comap (algebraMap R (Localization.Away g)) ''
        (D(δ) : Set (PrimeSpectrum (Localization.Away g))) := by
    refine ⟨q, hq_mem, ?_⟩
    -- The chart point `q` was chosen to lie over the original prime `p`.
    change PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q = p
    have hq_eq :
        primeSpectrum_localizationAway_homeomorph_D g q = ⟨p, (mem_D g p).2 hg⟩ := by
      simpa [q] using
        (primeSpectrum_localizationAway_homeomorph_D g).apply_symm_apply
          ⟨p, (mem_D g p).2 hg⟩
    simpa [primeSpectrum_localizationAway_homeomorph_D_apply] using congrArg Subtype.val hq_eq
  have himageOpen :
      IsOpen (PrimeSpectrum.comap (algebraMap R (Localization.Away g)) ''
        (D(δ) : Set (PrimeSpectrum (Localization.Away g)))) := by
    -- The localization map on spectra is an open embedding, so images of basic opens stay open.
    exact
      (PrimeSpectrum.localization_away_isOpenEmbedding
        (S := Localization.Away g) g).isOpenMap _ isOpen_basicOpen
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff] at himageOpen
  obtain ⟨U, hUbasic, hpU, hUsubset⟩ := himageOpen p hp_mem
  rcases hUbasic with ⟨a, rfl⟩
  have ha : a ∉ p.asIdeal := (PrimeSpectrum.mem_basicOpen a p).1 hpU
  refine ⟨a, ha, ?_⟩
  intro r hr
  apply hUsubset
  -- Membership in `D(g * a)` forces membership in `D(a)`, hence in the refined chart image.
  refine (PrimeSpectrum.mem_basicOpen a r).2 ?_
  intro ha_mem
  exact ((PrimeSpectrum.mem_basicOpen (g * a) r).1 hr) (r.asIdeal.mul_mem_left g ha_mem)

/-- Helper for Lemma 10.79.4: a splitting over `Rₚ` descends to a splitting over one
distinguished open `D(g)` containing `p`. -/
lemma exists_not_mem_prime_split_injective_of_localized_split
    [Module.Finite R P₁] [Module.FinitePresentation R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : PrimeSpectrum R)
    (σp : LocalizedModule.AtPrime p.asIdeal P₂ →ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal P₁)
    (hσp : σp.comp (LocalizedModule.map p.asIdeal.primeCompl φ) = LinearMap.id) :
    ∃ g : R, g ∉ p.asIdeal ∧
      ∃ σg : LocalizedModule.Away g P₂ →ₗ[Localization.Away g] LocalizedModule.Away g P₁,
        σg.comp (LocalizedModule.map (.powers g) φ) = LinearMap.id := by
  let σpR : LocalizedModule.AtPrime p.asIdeal P₂ →ₗ[R] LocalizedModule.AtPrime p.asIdeal P₁ :=
    σp.restrictScalars R
  obtain ⟨τ, s₀, hτ⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule
      p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁)
      (σpR.comp (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₂))
  have hσpR :
      σpR.comp ((LocalizedModule.map p.asIdeal.primeCompl φ).restrictScalars R) = LinearMap.id := by
    -- Restrict the local splitting identity from `Rₚ`-linearity to `R`-linearity.
    simpa using congrArg (fun f => f.restrictScalars R) hσp
  have hmap :
      ((LocalizedModule.map p.asIdeal.primeCompl φ).restrictScalars R).comp
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁) =
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₂).comp φ := by
    -- Rewrite the canonical localization map into the `IsLocalizedModule.map` form expected by
    -- the finite-presentation descent lemmas.
    simpa [LocalizedModule.restrictScalars_map_eq,
      IsLocalizedModule.iso_localizedModule_eq_refl] using
      (IsLocalizedModule.map_comp p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₂)
        φ)
  have hcomp :
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁).comp (τ.comp φ) =
        s₀ • (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁) := by
    -- The lifted map `τ` agrees with the local left inverse after multiplying by `s₀`, so its
    -- composite with `φ` already equals `s₀ • id` after localizing at `p`.
    calc
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁).comp (τ.comp φ)
          = ((LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁).comp τ).comp φ := by
              simp [LinearMap.comp_assoc]
      _ = (s₀ • (σpR.comp (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₂))).comp φ := by
            rw [hτ]
      _ = s₀ • ((σpR.comp (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₂)).comp φ) := by
            rw [LinearMap.smul_comp]
      _ = s₀ • (σpR.comp (((LocalizedModule.map p.asIdeal.primeCompl φ).restrictScalars R).comp
            (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁))) := by
            rw [hmap]
            simp [LinearMap.comp_assoc]
      _ = s₀ • ((σpR.comp ((LocalizedModule.map p.asIdeal.primeCompl φ).restrictScalars R)).comp
            (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁)) := by
            simp [LinearMap.comp_assoc]
      _ = s₀ • (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁) := by
            rw [hσpR]
            simp
  have hcomp' :
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁).comp (τ.comp φ) =
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁).comp (s₀ • LinearMap.id) := by
    -- Repackage the localized identity so `exists_smul_of_comp_eq_of_isLocalizedModule` can clear
    -- the remaining denominator on the finite source module `P₁`.
    simpa [LinearMap.comp_smul] using hcomp
  obtain ⟨s₁, hs₁⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
      p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P₁)
      (τ.comp φ)
      (s₀ • LinearMap.id)
      hcomp'
  let g : R := s₀.1 * s₁.1
  have hg : g ∉ p.asIdeal := by
    -- The common denominator still avoids `p` because both factors lie in `p.primeCompl`.
    intro hg
    exact s₀.2 ((p.isPrime.mem_or_mem hg).resolve_right s₁.2)
  let τg : LocalizedModule.Away g P₂ →ₗ[Localization.Away g] LocalizedModule.Away g P₁ :=
    LocalizedModule.map (.powers g) τ
  let Rg := Localization.Away g
  have hu₀ : IsUnit (algebraMap R Rg s₀.1) := by
    -- After inverting `g = s₀ * s₁`, the first denominator becomes a unit.
    refine isUnit_of_dvd_unit
      (map_dvd (algebraMap R Rg) ⟨s₁.1, by simp [g]⟩)
      (IsLocalization.map_units Rg ⟨g, Submonoid.mem_powers g⟩)
  have hu₁ : IsUnit (algebraMap R Rg s₁.1) := by
    -- The same holds for the scalar clearing the discrepancy on `τ ∘ φ`.
    refine isUnit_of_dvd_unit
      (map_dvd (algebraMap R Rg) ⟨s₀.1, by simp [g, mul_comm]⟩)
      (IsLocalization.map_units Rg ⟨g, Submonoid.mem_powers g⟩)
  let σg : LocalizedModule.Away g P₂ →ₗ[Localization.Away g] LocalizedModule.Away g P₁ :=
    (hu₀.unit⁻¹).1 • τg
  have hσg : σg.comp (LocalizedModule.map (.powers g) φ) = LinearMap.id := by
    -- After localizing away from `g`, both scalars are units, so the descended map becomes an
    -- honest left inverse.
    apply ((Module.End.isUnit_iff _).mp (hu₁.map (algebraMap Rg (Module.End Rg _)))).1
    apply ((Module.End.isUnit_iff _).mp (hu₀.map (algebraMap Rg (Module.End Rg _)))).1
    simp only [σg, τg, Module.algebraMap_end_apply, algebraMap_smul,
      LinearMap.map_smul_of_tower]
    rw [LinearMap.smul_comp, ← smul_assoc s₀.1, Algebra.smul_def s₀.1, IsUnit.mul_val_inv, one_smul]
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext (.powers g) (LocalizedModule.mkLinearMap (.powers g) P₁)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (.powers g) P₁))
    ext x
    have hx : s₁.1 • τ (φ x) = s₁.1 • s₀.1 • x := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : P₁ →ₗ[R] P₁ => f x) hs₁
    simp [LocalizedModule.smul'_mk, hx, g]
  exact ⟨g, hg, σg, hσg⟩

/-- Helper for Lemma 10.79.4: tensoring a localized map with an algebra over the localization
intertwines with tensoring the original map after the standard localization/base-change
equivalences. -/
lemma localized_lTensor_compare_square
    (S : Submonoid R)
    (φ : P₁ →ₗ[R] P₂)
    {B : Type*} [CommRing B] [Algebra R B] [Algebra (Localization S) B]
    [IsScalarTower R (Localization S) B] :
    let e₁ : B ⊗[Localization S] LocalizedModule S P₁ ≃ₗ[B] B ⊗[R] P₁ :=
      (LinearEquiv.baseChange
        (R := Localization S) (A := B)
        (M := LocalizedModule S P₁) (N := Localization S ⊗[R] P₁)
        (LocalizedModule.equivTensorProduct S P₁)).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₁)
    let e₂ : B ⊗[Localization S] LocalizedModule S P₂ ≃ₗ[B] B ⊗[R] P₂ :=
      (LinearEquiv.baseChange
        (R := Localization S) (A := B)
        (M := LocalizedModule S P₂) (N := Localization S ⊗[R] P₂)
        (LocalizedModule.equivTensorProduct S P₂)).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₂)
    e₂.toLinearMap.comp ((LocalizedModule.map S φ).baseChange B) =
      (φ.baseChange B).comp e₁.toLinearMap := by
  let e₁ : B ⊗[Localization S] LocalizedModule S P₁ ≃ₗ[B] B ⊗[R] P₁ :=
    (LinearEquiv.baseChange
      (R := Localization S) (A := B)
      (M := LocalizedModule S P₁) (N := Localization S ⊗[R] P₁)
      (LocalizedModule.equivTensorProduct S P₁)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₁)
  let e₂ : B ⊗[Localization S] LocalizedModule S P₂ ≃ₗ[B] B ⊗[R] P₂ :=
    (LinearEquiv.baseChange
      (R := Localization S) (A := B)
      (M := LocalizedModule S P₂) (N := Localization S ⊗[R] P₂)
      (LocalizedModule.equivTensorProduct S P₂)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₂)
  -- Compare the two composites on pure tensors and then expand the localized factor into `x / s`.
  dsimp [e₁, e₂]
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp only [LinearMap.map_zero]
  · intro b m
    obtain ⟨⟨x, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S P₁) m
    calc
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₂)
          (b ⊗ₜ[Localization S]
            (LocalizedModule.equivTensorProduct S P₂)
              (((LocalizedModule.map S) φ)
                (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S P₁) x s)))
          =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₂)
          (b ⊗ₜ[Localization S] (Localization.mk 1 s ⊗ₜ[R] φ x)) := by
            rw [← IsLocalizedModule.mk_eq_mk' (S := S) (M := P₁) (s := s) (m := x)]
            rw [LocalizedModule.map_mk, LocalizedModule.equivTensorProduct_apply_mk]
      _ = ((Localization.mk 1 s : Localization S) • b) ⊗ₜ[R] φ x := by
            simp
      _ =
        (LinearMap.lTensor B φ)
          (((Localization.mk 1 s : Localization S) • b) ⊗ₜ[R] x) := by
            simp
      _ =
        (LinearMap.lTensor B φ)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₁)
            (b ⊗ₜ[Localization S]
              (LocalizedModule.equivTensorProduct S P₁)
                (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S P₁) x s))) := by
            rw [← IsLocalizedModule.mk_eq_mk' (S := S) (M := P₁) (s := s) (m := x)]
            rw [LocalizedModule.equivTensorProduct_apply_mk]
            simp
  · intro x y hx hy
    simpa [LinearMap.map_add, hx, hy]

/-- Helper for Lemma 10.79.4: tensoring a localized map with an algebra over the localization
detects exactly the same injectivity as tensoring the original map with that algebra. -/
lemma localized_lTensor_injective_iff
    (S : Submonoid R)
    (φ : P₁ →ₗ[R] P₂)
    {B : Type*} [CommRing B] [Algebra R B] [Algebra (Localization S) B]
    [IsScalarTower R (Localization S) B] :
    Function.Injective ((LocalizedModule.map S φ).baseChange B) ↔
      Function.Injective (φ.lTensor B) := by
  let e₁ : B ⊗[Localization S] LocalizedModule S P₁ ≃ₗ[B] B ⊗[R] P₁ :=
    (LinearEquiv.baseChange
      (R := Localization S) (A := B)
      (M := LocalizedModule S P₁) (N := Localization S ⊗[R] P₁)
      (LocalizedModule.equivTensorProduct S P₁)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₁)
  let e₂ : B ⊗[Localization S] LocalizedModule S P₂ ≃ₗ[B] B ⊗[R] P₂ :=
    (LinearEquiv.baseChange
      (R := Localization S) (A := B)
      (M := LocalizedModule S P₂) (N := Localization S ⊗[R] P₂)
      (LocalizedModule.equivTensorProduct S P₂)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization S) B B P₂)
  have hSquare :
      (φ.baseChange B).comp e₁.toLinearMap =
        e₂.toLinearMap.comp ((LocalizedModule.map S φ).baseChange B) :=
    (localized_lTensor_compare_square (P₁ := P₁) (P₂ := P₂) S φ).symm
  constructor
  · intro hLocalized
    -- Transport injectivity across the source and target comparison equivalences.
    simpa [LinearMap.baseChange_eq_ltensor] using
      injective_of_ladder_linearEquiv hSquare hLocalized
  · intro hTensor
    -- Run the same ladder argument in the reverse direction using the inverse equivalences.
    have hSquareSymm :
        ((LocalizedModule.map S φ).baseChange B).comp e₁.symm.toLinearMap =
          e₂.symm.toLinearMap.comp (φ.baseChange B) := by
      apply LinearMap.ext
      intro z
      apply e₂.injective
      simpa [LinearMap.comp_assoc] using
        (LinearMap.congr_fun hSquare (e₁.symm z)).symm
    exact injective_of_ladder_linearEquiv hSquareSymm
      (by simpa [LinearMap.baseChange_eq_ltensor] using hTensor)

/-- Helper for Lemma 10.79.4: over the local ring `Rₚ`, residue-field injectivity of the fiber
gives a splitting of the localized map. -/
lemma localizedAtPrime_split_injective_of_residue_injective
    [Module.Projective R P₁] [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : PrimeSpectrum R)
    (hp : Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ)) :
    ∃ σp : LocalizedModule.AtPrime p.asIdeal P₂ →ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal P₁,
      σp.comp (LocalizedModule.map p.asIdeal.primeCompl φ) = LinearMap.id := by
  obtain ⟨hfree₁, hfree₂⟩ := localizedAtPrime_free_pair (P₁ := P₁) (P₂ := P₂) p
  letI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal P₂) := hfree₂
  have hTensorInj :
      Function.Injective
        ((LocalizedModule.map p.asIdeal.primeCompl φ).baseChange p.asIdeal.ResidueField) := by
    -- The residue field of `Rₚ` is already an algebra over `Rₚ`, so the generic localization
    -- tensor comparison rewrites the given source-fiber injectivity into the local tensor goal.
    rw [localized_lTensor_injective_iff (P₁ := P₁) (P₂ := P₂)
      p.asIdeal.primeCompl φ]
    simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using hp
  have hTensorInj' :
      Function.Injective
        ((LocalizedModule.map p.asIdeal.primeCompl φ).lTensor p.asIdeal.ResidueField) := by
    simpa [LinearMap.baseChange_eq_ltensor] using hTensorInj
  -- Over the local ring `Rₚ`, injectivity on the residue field tensor is exactly the split
  -- injectivity criterion for maps into a finite free module.
  rw [← IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (LocalizedModule.map p.asIdeal.primeCompl φ)] at hTensorInj'
  simpa [LinearMap.comp_assoc] using hTensorInj'

/-- Helper for Lemma 10.79.4: near a prime where the residue-field fiber is injective, one can
shrink to a basic open on which the residue-field fibers stay injective, the localized map at the
base prime is injective, and the localized cokernel is projective. -/
lemma residue_injective_of_split_away_at_chart_point
    [Module.Projective R P₁] [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (g : R)
    (σg : LocalizedModule.Away g P₂ →ₗ[Localization.Away g] LocalizedModule.Away g P₁)
    (hσg : σg.comp (LocalizedModule.map (.powers g) φ) = LinearMap.id)
    (q : PrimeSpectrum R) (hq : q ∈ (D(g) : Set (PrimeSpectrum R))) :
    Function.Injective (LinearMap.rTensor q.asIdeal.ResidueField φ) := by
  let qg : PrimeSpectrum (Localization.Away g) :=
    (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨q, hq⟩
  have hqComap :
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) qg = q := by
    -- The chart prime was chosen as the inverse image of `q` under the localization homeomorphism.
    change (primeSpectrum_localizationAway_homeomorph_D g qg).1 = q
    simpa [qg, primeSpectrum_localizationAway_homeomorph_D_apply] using
      congrArg Subtype.val
        ((primeSpectrum_localizationAway_homeomorph_D g).apply_symm_apply ⟨q, hq⟩)
  have hqIdeal :
      q.asIdeal = Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal := by
    -- Record the corresponding ideal contraction for the residue-field comparison map.
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqComap.symm
  have hSplitTensor :
      (σg.baseChange qg.asIdeal.ResidueField).comp
          ((LocalizedModule.map (.powers g) φ).baseChange qg.asIdeal.ResidueField) =
        LinearMap.id := by
    -- Tensoring the split identity over `R_g` preserves the left inverse.
    rw [← LinearMap.baseChange_comp, hσg, LinearMap.baseChange_id]
  have hAwayTensorInj :
      Function.Injective
        ((LocalizedModule.map (.powers g) φ).baseChange qg.asIdeal.ResidueField) := by
    exact Function.HasLeftInverse.injective
      ⟨σg.baseChange qg.asIdeal.ResidueField, fun x ↦ by
        exact LinearMap.congr_fun hSplitTensor x⟩
  have hTensorInj :
      Function.Injective (φ.lTensor qg.asIdeal.ResidueField) := by
    -- The localization-tensor comparison removes the intermediate away localization.
    exact (localized_lTensor_injective_iff (P₁ := P₁) (P₂ := P₂)
      (.powers g) φ).mp hAwayTensorInj
  have hqgRTensor :
      Function.Injective (LinearMap.rTensor qg.asIdeal.ResidueField φ) := by
    exact
      (LinearMap.lTensor_inj_iff_rTensor_inj
        (M := qg.asIdeal.ResidueField) (f := φ)).1 hTensorInj
  let eκ :
      q.asIdeal.ResidueField ≃ₐ[R] qg.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ q.asIdeal qg.asIdeal
        (Algebra.ofId R (Localization.Away g)) hqIdeal)
      ((RingHom.surjectiveOnStalks_of_isLocalization (.powers g)
        (Localization.Away g)).residueFieldMap_bijective q.asIdeal qg.asIdeal hqIdeal)
  -- Transfer injectivity back along the canonical residue-field equivalence over the chart.
  exact injective_rTensor_of_linearEquiv φ eκ.toLinearEquiv hqgRTensor

/-- Helper for Lemma 10.79.4: near a prime where the residue-field fiber is injective, one can
shrink to a basic open on which the residue-field fibers stay injective, the localized map at the
base prime is injective, and the localized cokernel is projective. -/
theorem exists_basicOpen_split_injective_near_residueInjective_point
    [Module.Projective R P₁] [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (p : PrimeSpectrum R)
    (hp : Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ)) :
    ∃ g : R, g ∉ p.asIdeal ∧
      (D(g) : Set (PrimeSpectrum R)) ⊆
        { q : PrimeSpectrum R | Function.Injective (LinearMap.rTensor q.asIdeal.ResidueField φ) } ∧
      Function.Injective (LocalizedModule.map p.asIdeal.primeCompl φ) ∧
      Function.Injective (LocalizedModule.map (.powers g) φ) ∧
      Module.Projective (Localization.Away g)
        (LocalizedModule.Away g (P₂ ⧸ LinearMap.range φ)) := by
  -- Route correction: pivot from the stalled away-chart/minor search to the simpler source-faithful
  -- local route `R → Rₚ`: first split over `Rₚ`, then descend that section to one `D(g)`.
  letI : Module.Finite R P₂ := inferInstance
  letI : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  letI : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  obtain ⟨σp, hσp⟩ := localizedAtPrime_split_injective_of_residue_injective φ p hp
  obtain ⟨g, hg, σg, hσg⟩ :=
    exists_not_mem_prime_split_injective_of_localized_split φ p σp hσp
  have hpLocalizedInj : Function.Injective (LocalizedModule.map p.asIdeal.primeCompl φ) := by
    -- A left inverse over `Rₚ` gives injectivity of the localized map at `p`.
    exact Function.HasLeftInverse.injective ⟨σp, fun x ↦ by simpa using congrArg (fun f => f x) hσp⟩
  have hgAwayInj : Function.Injective (LocalizedModule.map (.powers g) φ) := by
    -- The descended section gives injectivity over the smaller distinguished open `D(g)`.
    exact Function.HasLeftInverse.injective ⟨σg, fun x ↦ by simpa using congrArg (fun f => f x) hσg⟩
  letI : Module.Projective (Localization.Away g) (LocalizedModule.Away g P₂) :=
    Module.projective_of_isLocalizedModule (.powers g) (LocalizedModule.mkLinearMap (.powers g) P₂)
  let eCoker :
      (LocalizedModule.Away g P₂ ⧸ LinearMap.range (LocalizedModule.map (.powers g) φ)) ≃ₗ[Localization.Away g]
        LocalizedModule.Away g (P₂ ⧸ LinearMap.range φ) := by
    have hRange :
        Submodule.localized (.powers g) (LinearMap.range φ) =
          LinearMap.range (LocalizedModule.map (.powers g) φ) := by
      -- The range of the away-localized map is exactly the localization of the original range.
      simpa [LocalizedModule.restrictScalars_map_eq,
        IsLocalizedModule.iso_localizedModule_eq_refl] using
        (LinearMap.localized'_range_eq_range_localizedMap
          (S := Localization (.powers g))
          (p := (.powers g))
          (f := LocalizedModule.mkLinearMap (.powers g) P₁)
          (f' := LocalizedModule.mkLinearMap (.powers g) P₂)
          φ)
    -- Identify the localized cokernel with the quotient by the range of the localized map.
    exact
      (Submodule.quotEquivOfEq
        (Submodule.localized (.powers g) (LinearMap.range φ))
        (LinearMap.range (LocalizedModule.map (.powers g) φ))
        hRange).symm.trans
        (localizedQuotientEquiv (.powers g) (LinearMap.range φ))
  have hprojLocalizedCoker :
      Module.Projective (Localization.Away g)
        (LocalizedModule.Away g P₂ ⧸ LinearMap.range (LocalizedModule.map (.powers g) φ)) :=
    cokernel_projective_of_split_injective
      (LocalizedModule.map (.powers g) φ) σg hσg
  letI :
      Module.Projective (Localization.Away g)
        (LocalizedModule.Away g P₂ ⧸ LinearMap.range (LocalizedModule.map (.powers g) φ)) :=
    hprojLocalizedCoker
  have hprojCoker :
      Module.Projective (Localization.Away g)
        (LocalizedModule.Away g (P₂ ⧸ LinearMap.range φ)) :=
    Module.Projective.of_equiv eCoker
  refine ⟨g, hg, ?_, hpLocalizedInj, hgAwayInj, hprojCoker⟩
  intro q hq
  -- Every point of the descended chart inherits residue-field injectivity from the split over
  -- `R_g`.
  exact residue_injective_of_split_away_at_chart_point φ g σg hσg q hq

/-- Helper for Lemma 10.79.4: in the projective setting, the injective residue-fiber locus is open
in `Spec R`. -/
-- Proof sketch: the source-faithful neighborhood theorem above supplies a basic-open chart around
-- every point of the injective locus.
theorem isOpen_moduleMapResidueInjectiveLocus_of_finite_of_finitePresentation
    [Module.Projective R P₁] [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) :
    IsOpen { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) } := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff]
  intro p hp
  -- The source-faithful neighborhood lemma packages the basic-open minor argument around `p`.
  obtain ⟨g, hg, hsubset, _, _, _⟩ :=
    exists_basicOpen_split_injective_near_residueInjective_point φ p hp
  refine ⟨PrimeSpectrum.basicOpen g, ⟨g, rfl⟩, ?_, hsubset⟩
  exact (PrimeSpectrum.mem_basicOpen g p).2 hg

/-- Helper for Lemma 10.79.4: in the projective setting, inclusion of `D(f)` in the injective
residue-fiber locus forces the away-localized map over `R_f` to be injective. -/
-- Proof sketch: for every prime in `D(f)`, apply the neighborhood theorem and then globalize the
-- resulting primewise localized injectivity over `R_f`.
theorem injective_localizedAway_of_D_subset_moduleMapResidueInjectiveLocus_of_finite_of_finitePresentation
    [Module.Projective R P₁] [Module.Projective R P₂]
    (φ : P₁ →ₗ[R] P₂) (f : R)
    (hU :
      (D(f) : Set (PrimeSpectrum R)) ⊆
        { p : PrimeSpectrum R | Function.Injective (LinearMap.rTensor p.asIdeal.ResidueField φ) }) :
    Function.Injective (LocalizedModule.map (.powers f) φ) := by
  -- The basic-open pointwise injectivity criterion reduces the away-local statement to the local
  -- injectivity supplied by the neighborhood lemma at each point of `D(f)`.
  refine injective_localizedAway_of_basicOpen_localizedInjective φ f ?_
  intro q hq
  obtain ⟨g, hg, _, hqInj, _, _⟩ :=
    exists_basicOpen_split_injective_near_residueInjective_point φ q (hU hq)
  exact hqInj

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

/-- Helper for Lemma 10.79.4: localizing `A[1/t]` at a prime ideal is canonically the same as
localizing `A` at the contracted prime. -/
noncomputable abbrev away_atPrime_algEquiv_to_contracted
    {A : Type*} [CommRing A] {t : A} (I : Ideal (Localization.Away t)) [I.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) I) ≃ₐ[A]
      Localization.AtPrime I :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := Submonoid.powers t) I

/-- Helper for Lemma 10.79.4: the iterated stalk of `M_t` at `I` is the localization of `M` at
the contracted prime. -/
lemma localizedAway_stalk_isLocalizedModule_of_contracted_prime
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {t : A} (I : Ideal (Localization.Away t)) [I.IsPrime] :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) I
    let κ :
      M →ₗ[A] LocalizedModule.AtPrime I (LocalizedModule.Away t M) :=
      ((LocalizedModule.mkLinearMap I.primeCompl (LocalizedModule.Away t M)).restrictScalars A).comp
        (LocalizedModule.mkLinearMap (.powers t) M)
    IsLocalizedModule J.primeCompl κ := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) I
  let B := Localization.AtPrime I
  let κ :
      M →ₗ[A] LocalizedModule.AtPrime I (LocalizedModule.Away t M) :=
    ((LocalizedModule.mkLinearMap I.primeCompl (LocalizedModule.Away t M)).restrictScalars A).comp
      (LocalizedModule.mkLinearMap (.powers t) M)
  let eOuter :
      LocalizedModule.AtPrime I (LocalizedModule.Away t M) ≃ₗ[B]
        B ⊗[Localization.Away t] LocalizedModule.Away t M :=
    LocalizedModule.equivTensorProduct I.primeCompl (LocalizedModule.Away t M)
  let eInner :
      B ⊗[Localization.Away t] LocalizedModule.Away t M ≃ₗ[B] B ⊗[A] M :=
    (LinearEquiv.baseChange
      (R := Localization.Away t) (A := B)
      (M := LocalizedModule.Away t M) (N := Localization.Away t ⊗[A] M)
      (LocalizedModule.equivTensorProduct (.powers t) M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) B B M)
  let e :
      LocalizedModule.AtPrime I (LocalizedModule.Away t M) ≃ₗ[A] B ⊗[A] M :=
    (eOuter.trans eInner).restrictScalars A
  have hcomp :
      e.toLinearMap.comp κ = TensorProduct.mk A B M 1 := by
    -- The iterated localization map becomes the standard tensor generator after the two
    -- localization/base-change identifications.
    ext x
    change (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away t) B B M)
        ((LinearEquiv.baseChange
          (R := Localization.Away t) (A := B)
          (M := LocalizedModule.Away t M) (N := Localization.Away t ⊗[A] M)
          (LocalizedModule.equivTensorProduct (Submonoid.powers t) M))
          ((LocalizedModule.equivTensorProduct I.primeCompl (LocalizedModule.Away t M))
            (LocalizedModule.mk (LocalizedModule.mk x 1) 1))) =
      1 ⊗ₜ[A] x
    rw [LocalizedModule.equivTensorProduct_apply_mk, LinearEquiv.baseChange_tmul,
      LocalizedModule.equivTensorProduct_apply_mk,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    congr 1
    rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap, Algebra.smul_def,
      map_one, map_one, one_mul]
  letI : IsLocalization.AtPrime B J := by
    dsimp [B, J]
    infer_instance
  have hκ :
      e.symm.toLinearMap.comp (TensorProduct.mk A B M 1) = κ := by
    -- Pull the tensor-model localization map back through the comparison equivalence.
    ext x
    apply e.injective
    simpa [LinearMap.comp_assoc] using
      (congrArg (fun f : M →ₗ[A] B ⊗[A] M => f x) hcomp).symm
  -- Transport the standard tensor-product localization model along the comparison equivalence.
  convert
    (inferInstance : IsLocalizedModule J.primeCompl
      (e.symm.toLinearMap.comp (TensorProduct.mk A B M 1))) using 1
  exact hκ.symm

/-- Helper for Lemma 10.79.4: a projective away-localized chart over `D(g)` yields a projective
stalk at every prime of that chart. -/
lemma projective_contracted_stalk_of_projective_away_chart
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (g : A) (q : PrimeSpectrum A) (hq : q ∈ (D(g) : Set (PrimeSpectrum A)))
    (hproj : Module.Projective (Localization.Away g) (LocalizedModule.Away g M)) :
    Module.Projective (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal M) := by
  let qg : PrimeSpectrum (Localization.Away g) :=
    (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨q, hq⟩
  have hqgIdeal :
      qg.asIdeal = q.asIdeal.map (algebraMap A (Localization.Away g)) := by
    -- The prime of `A_g` attached to `q` is its extension along `A → A_g`.
    simpa [qg] using
      primeSpectrum_localizationAway_homeomorph_D_symm_asIdeal g ⟨q, hq⟩
  have hq' : Submonoid.powers g ≤ q.asIdeal.primeCompl := by
    -- The chart condition `q ∈ D(g)` says exactly that every power of `g` avoids `q`.
    simpa [Submonoid.powers_le, Ideal.primeCompl] using (mem_D g q).1 hq
  let Aq := Localization.AtPrime q.asIdeal
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  letI : Algebra (Localization.Away g) Aq :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers g) q.asIdeal.primeCompl hq'
  have : IsScalarTower A (Localization.Away g) Aq :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  letI : Module (Localization.Away g) Mq := Module.compHom Mq (algebraMap (Localization.Away g) Aq)
  have : IsScalarTower A (Localization.Away g) Mq :=
    ⟨fun r r' m ↦ show algebraMap (Localization.Away g) Aq (r • r') • m = _ by
      simp [Aq, Mq, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away g) Aq Mq :=
    ⟨fun r r' m ↦ show _ = algebraMap (Localization.Away g) Aq r • r' • m by
      rw [← mul_smul, ← Algebra.smul_def]⟩
  let l :
      LocalizedModule.Away g M →ₗ[Localization.Away g] Mq :=
    (IsLocalizedModule.liftOfLE _ _ hq'
      (LocalizedModule.mkLinearMap (.powers g) M)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)).extendScalarsOfIsLocalization
        (.powers g) (Localization.Away g)
  have : IsLocalization.AtPrime Aq qg.asIdeal := by
    -- Localizing `A_g` at the point over `q` recovers the contracted stalk `A_q`.
    have := IsLocalization.isLocalization_of_submonoid_le
      (Localization.Away g) Aq (.powers g) q.asIdeal.primeCompl hq'
    apply IsLocalization.isLocalization_of_is_exists_mul_mem _
      (Submonoid.map (algebraMap A (Localization.Away g)) q.asIdeal.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩
      intro hxMap
      rcases (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (.powers g) (S := Localization.Away g) q.asIdeal x).mp
          (by simpa [hqgIdeal] using hxMap) with ⟨m, hm, hmx⟩
      exact hx ((q.isPrime.mem_or_mem hmx).resolve_left (hq' hm))
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers g) x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [hqgIdeal]
      exact (IsLocalization.mk'_mem_map_algebraMap_iff
        (M := (.powers g)) (S := Localization.Away g) q.asIdeal x s).2
          ⟨1, by simpa, by simpa using H⟩
  have : IsLocalizedModule qg.asIdeal.primeCompl l := by
    -- First view `M_q` as the localization of `M_g` at the image of `qᶜ`, then enlarge that
    -- image submonoid to the full complement of `qg`.
    have : IsLocalizedModule q.asIdeal.primeCompl (l.restrictScalars A) :=
      inferInstanceAs (IsLocalizedModule q.asIdeal.primeCompl
        ((IsLocalizedModule.liftOfLE _ _ hq'
          (LocalizedModule.mkLinearMap (.powers g) M)
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))))
    have : IsLocalizedModule
        (Algebra.algebraMapSubmonoid (Localization.Away g) q.asIdeal.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars q.asIdeal.primeCompl l
    apply IsLocalizedModule.of_exists_mul_mem
      (Algebra.algebraMapSubmonoid (Localization.Away g) q.asIdeal.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩
      intro hxMap
      rcases (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (.powers g) (S := Localization.Away g) q.asIdeal x).mp
          (by simpa [hqgIdeal] using hxMap) with ⟨m, hm, hmx⟩
      exact hx ((q.isPrime.mem_or_mem hmx).resolve_left (hq' hm))
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers g) x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [hqgIdeal]
      exact (IsLocalization.mk'_mem_map_algebraMap_iff
        (M := (.powers g)) (S := Localization.Away g) q.asIdeal x s).2
          ⟨1, by simpa, by simpa using H⟩
  letI : Module.Projective (Localization.Away g) (LocalizedModule.Away g M) := hproj
  -- Projectivity ascends along the localization map `M_g → M_q`.
  exact Module.projective_of_isLocalizedModule qg.asIdeal.primeCompl l

/-- Helper for Lemma 10.79.4: the canonical ring maps between the contracted stalk ring and the
iterated away-then-prime stalk ring form an inverse pair. -/
lemma away_atPrime_algEquiv_to_contracted_ringHomInvPair
    {A : Type*} [CommRing A] {t : A} (I : Ideal (Localization.Away t)) [I.IsPrime] :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) I
    let σ : Localization.AtPrime J →+* Localization.AtPrime I :=
      (away_atPrime_algEquiv_to_contracted (A := A) (t := t) I).toRingHom
    let σ' : Localization.AtPrime I →+* Localization.AtPrime J :=
      (away_atPrime_algEquiv_to_contracted (A := A) (t := t) I).symm.toRingHom
    RingHomInvPair σ σ' ∧ RingHomInvPair σ' σ := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) I
  let σ : Localization.AtPrime J →+* Localization.AtPrime I :=
    (away_atPrime_algEquiv_to_contracted (A := A) (t := t) I).toRingHom
  let σ' : Localization.AtPrime I →+* Localization.AtPrime J :=
    (away_atPrime_algEquiv_to_contracted (A := A) (t := t) I).symm.toRingHom
  letI : RingHomInvPair σ σ' :=
    RingHomInvPair.of_ringEquiv (away_atPrime_algEquiv_to_contracted (A := A) (t := t) I).toRingEquiv
  constructor
  · exact inferInstance
  · exact RingHomInvPair.symm σ σ'

/-- Helper for Lemma 10.79.4: projectivity of the contracted stalk of `M` at the prime under
`I ⊆ A_t` should transport to projectivity of the maximal stalk of `M_t` at `I`. -/
lemma projective_localizedAway_stalk_of_projective_contracted_stalk
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {t : A} (I : Ideal (Localization.Away t)) [I.IsPrime]
    (hproj :
      Module.Projective
        (Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) I))
        (LocalizedModule.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) I) M)) :
    Module.Projective (Localization.AtPrime I)
      (LocalizedModule.AtPrime I (LocalizedModule.Away t M)) := by
  -- Route correction: first identify the iterated stalk as the same localization of `M` at the
  -- contracted prime, then transport projectivity across the resulting semilinear equivalence.
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) I
  let κ :
      M →ₗ[A] LocalizedModule.AtPrime I (LocalizedModule.Away t M) :=
    ((LocalizedModule.mkLinearMap I.primeCompl (LocalizedModule.Away t M)).restrictScalars A).comp
      (LocalizedModule.mkLinearMap (.powers t) M)
  letI : IsLocalizedModule J.primeCompl κ :=
    localizedAway_stalk_isLocalizedModule_of_contracted_prime (A := A) (M := M) (t := t) I
  let σ : Localization.AtPrime J →+* Localization.AtPrime I :=
    (away_atPrime_algEquiv_to_contracted (A := A) (t := t) I).toRingHom
  let σ' : Localization.AtPrime I →+* Localization.AtPrime J :=
    (away_atPrime_algEquiv_to_contracted (A := A) (t := t) I).symm.toRingHom
  letI : IsLocalization.AtPrime (Localization.AtPrime I) J := by
    infer_instance
  have hInvPair :
      RingHomInvPair σ σ' ∧ RingHomInvPair σ' σ :=
    away_atPrime_algEquiv_to_contracted_ringHomInvPair (A := A) (t := t) I
  letI : RingHomInvPair σ σ' := hInvPair.1
  letI : RingHomInvPair σ' σ := hInvPair.2
  let e :
      LocalizedModule.AtPrime J M ≃ₛₗ[σ] LocalizedModule.AtPrime I (LocalizedModule.Away t M) := by
    letI : Module (Localization.AtPrime J)
        (LocalizedModule.AtPrime I (LocalizedModule.Away t M)) :=
      IsLocalizedModule.module J.primeCompl κ
    letI : IsScalarTower A (Localization.AtPrime J)
        (LocalizedModule.AtPrime I (LocalizedModule.Away t M)) :=
      IsLocalizedModule.isScalarTower_module J.primeCompl κ
    let eA :
        LocalizedModule.AtPrime J M ≃ₗ[A] LocalizedModule.AtPrime I (LocalizedModule.Away t M) :=
      IsLocalizedModule.linearEquiv J.primeCompl
        (LocalizedModule.mkLinearMap J.primeCompl M) κ
    refine
      { __ := eA
        map_smul' := ?_ }
    intro r m
    -- Clear the denominator of `r` in the contracted stalk and use `A`-linearity of the
    -- localization comparison.
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq J.primeCompl r
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units κ s)).1
    change (↑s : A) • eA (IsLocalization.mk' (Localization.AtPrime J) r s • m) =
      (↑s : A) • (σ (IsLocalization.mk' (Localization.AtPrime J) r s) • eA m)
    have hsigma :
        (↑s : A) • σ (IsLocalization.mk' (Localization.AtPrime J) r s) =
          algebraMap A (Localization.AtPrime I) r := by
      have hσmk :
          σ (IsLocalization.mk' (Localization.AtPrime J) r s) =
            IsLocalization.mk' (Localization.AtPrime I) r s := by
        dsimp [σ, away_atPrime_algEquiv_to_contracted]
        change (IsLocalization.algEquiv J.primeCompl (Localization.AtPrime J)
          (Localization.AtPrime I))
            (IsLocalization.mk' (Localization.AtPrime J) r s) =
          IsLocalization.mk' (Localization.AtPrime I) r s
        simpa using
          (IsLocalization.algEquiv_mk' (M := J.primeCompl)
            (S := Localization.AtPrime J) (Q := Localization.AtPrime I) r s)
      rw [hσmk, IsLocalization.smul_mk'_self]
    calc
      (↑s : A) • eA (IsLocalization.mk' (Localization.AtPrime J) r s • m) =
          eA ((↑s : A) • (IsLocalization.mk' (Localization.AtPrime J) r s • m)) := by
            rw [eA.map_smul]
      _ = eA (r • m) := by
            rw [← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]
      _ = r • eA m := by
            rw [eA.map_smul]
      _ = (algebraMap A (Localization.AtPrime I) r) • eA m := by
            simpa using (algebraMap_smul (Localization.AtPrime I) r (eA m)).symm
      _ = ((↑s : A) • σ (IsLocalization.mk' (Localization.AtPrime J) r s)) • eA m := by
            rw [hsigma]
      _ = (↑s : A) • (σ (IsLocalization.mk' (Localization.AtPrime J) r s) • eA m) := by
            rw [smul_assoc]
  letI :
      Module.Projective (Localization.AtPrime J) (LocalizedModule.AtPrime J M) := hproj
  -- The source and target stalks are the same localization of `M`, only viewed through the
  -- canonical ring equivalence collapsing the iterated localization.
  exact Module.Projective.of_equiv (M := LocalizedModule.AtPrime J M)
    (R := Localization.AtPrime J) (σ := σ) e

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
  by
  have hfiniteQuot : Module.Finite R (P₂ ⧸ LinearMap.range φ) :=
    Module.Finite.of_surjective (Submodule.mkQ (LinearMap.range φ))
      (Submodule.mkQ_surjective _)
  letI : Module.Finite R (P₂ ⧸ LinearMap.range φ) := hfiniteQuot
  have hfiniteLocalized :
      Module.Finite (Localization.Away f) (LocalizedModule.Away f (P₂ ⧸ LinearMap.range φ)) :=
    inferInstance
  letI : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  letI : Module.FinitePresentation R (P₂ ⧸ LinearMap.range φ) :=
    Module.finitePresentation_of_surjective
      (Submodule.mkQ (LinearMap.range φ))
      (Submodule.mkQ_surjective _)
      (by simpa using Submodule.fg_range φ)
  letI : Module.FinitePresentation (Localization.Away f)
      (LocalizedModule.Away f (P₂ ⧸ LinearMap.range φ)) := inferInstance
  -- Route correction: the finite part is done; the remaining issue is purely the canonical
  -- at-prime transport from the projective chart `C_g` supplied by the neighborhood theorem to the
  -- maximal stalk of `C_f`.
  refine ⟨hfiniteLocalized, ?_⟩
  let C : Type w := P₂ ⧸ LinearMap.range φ
  refine Module.projective_of_localization_maximal
    (R := Localization.Away f)
    (M := LocalizedModule.Away f C) fun I hI ↦ ?_
  let qf : PrimeSpectrum (Localization.Away f) := ⟨I, Ideal.IsMaximal.isPrime hI⟩
  let qD : D(f) := primeSpectrum_localizationAway_homeomorph_D f qf
  let q : PrimeSpectrum R := qD.1
  have hqfIdeal :
      qf.asIdeal = q.asIdeal.map (algebraMap R (Localization.Away f)) := by
    -- The maximal ideal `I` of `R_f` is the extension of the contracted prime `q`.
    simpa [qf, q, qD] using primeSpectrum_localizationAway_homeomorph_D_symm_asIdeal f qD
  have hI_map : I = q.asIdeal.map (algebraMap R (Localization.Away f)) := by
    simpa [qf] using hqfIdeal
  have hqf : q ∈ (D(f) : Set (PrimeSpectrum R)) := qD.2
  obtain ⟨g, hg, _, _, _, hprojChart⟩ :=
    exists_basicOpen_split_injective_near_residueInjective_point φ q (hU hqf)
  have hqg : q ∈ (D(g) : Set (PrimeSpectrum R)) := (mem_D g q).2 hg
  have hprojContracted :
      Module.Projective (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal C) :=
    -- The neighborhood theorem provides a projective away-chart, and the helper upgrades it to
    -- the projective contracted stalk `C_q`.
    projective_contracted_stalk_of_projective_away_chart
      (M := C) g q hqg hprojChart
  have hq' : Submonoid.powers f ≤ q.asIdeal.primeCompl := by
    -- The contracted point `q` lies in `D(f)`, so every power of `f` is inverted at `q`.
    simpa [Submonoid.powers_le, Ideal.primeCompl] using (mem_D f q).1 hqf
  let Rq := Localization.AtPrime q.asIdeal
  let Cq := LocalizedModule.AtPrime q.asIdeal C
  letI : Algebra (Localization.Away f) Rq :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) q.asIdeal.primeCompl hq'
  have : IsScalarTower R (Localization.Away f) Rq :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  letI : Module (Localization.Away f) Cq := Module.compHom Cq (algebraMap (Localization.Away f) Rq)
  have : IsScalarTower R (Localization.Away f) Cq :=
    ⟨fun r r' m ↦ show algebraMap (Localization.Away f) Rq (r • r') • m = _ by
      simp [Rq, Cq, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away f) Rq Cq :=
    ⟨fun r r' m ↦ show _ = algebraMap (Localization.Away f) Rq r • r' • m by
      rw [← mul_smul, ← Algebra.smul_def]⟩
  let l :
      LocalizedModule.Away f C →ₗ[Localization.Away f] Cq :=
    (IsLocalizedModule.liftOfLE _ _ hq'
      (LocalizedModule.mkLinearMap (.powers f) C)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl C)).extendScalarsOfIsLocalization
        (.powers f) (Localization.Away f)
  have : IsLocalization.AtPrime Rq qf.asIdeal := by
    -- The maximal point `qf` of `Spec(R_f)` lies over `q`, so localizing `R_f` at `qf`
    -- recovers the original local ring `R_q`.
    have := IsLocalization.isLocalization_of_submonoid_le
      (Localization.Away f) Rq (.powers f) q.asIdeal.primeCompl hq'
    apply IsLocalization.isLocalization_of_is_exists_mul_mem _
      (Submonoid.map (algebraMap R (Localization.Away f)) q.asIdeal.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩
      intro hxMap
      rcases (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (.powers f) (S := Localization.Away f) q.asIdeal x).mp
          (by simpa [hqfIdeal] using hxMap) with ⟨m, hm, hmx⟩
      exact hx ((q.isPrime.mem_or_mem hmx).resolve_left (hq' hm))
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [hqfIdeal]
      exact (IsLocalization.mk'_mem_map_algebraMap_iff
        (M := (.powers f)) (S := Localization.Away f) q.asIdeal x s).2
          ⟨1, by simpa, by simpa using H⟩
  have : IsLocalizedModule I.primeCompl l := by
    -- First regard `C_q` as the localization of `C_f` at the image of `qᶜ`, then enlarge that
    -- image to the full complement of the maximal ideal `I = qf.asIdeal`.
    have : IsLocalizedModule q.asIdeal.primeCompl (l.restrictScalars R) :=
      inferInstanceAs (IsLocalizedModule q.asIdeal.primeCompl
        ((IsLocalizedModule.liftOfLE _ _ hq'
          (LocalizedModule.mkLinearMap (.powers f) C)
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl C))))
    have : IsLocalizedModule
        (Algebra.algebraMapSubmonoid (Localization.Away f) q.asIdeal.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars q.asIdeal.primeCompl l
    apply IsLocalizedModule.of_exists_mul_mem
      (Algebra.algebraMapSubmonoid (Localization.Away f) q.asIdeal.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩
      intro hxMap
      rcases (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (.powers f) (S := Localization.Away f) q.asIdeal x).mp
          (by simpa [hI_map] using hxMap) with ⟨m, hm, hmx⟩
      exact hx ((q.isPrime.mem_or_mem hmx).resolve_left (hq' hm))
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [hI_map]
      exact (IsLocalization.mk'_mem_map_algebraMap_iff
        (M := (.powers f)) (S := Localization.Away f) q.asIdeal x s).2
          ⟨1, by simpa, by simpa using H⟩
  letI : I.IsPrime := Ideal.IsMaximal.isPrime hI
  -- Reduce the final maximal-stalk projectivity to the missing generic transport lemma.
  exact projective_localizedAway_stalk_of_projective_contracted_stalk
    (M := C) (t := f) I hprojContracted

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
      Module.Projective (Localization.Away f) (LocalizedModule.Away f (LinearMap.ker φ)) := by
  let ψ : LocalizedModule.Away f P₁ →ₗ[Localization.Away f] LocalizedModule.Away f P₂ :=
    LocalizedModule.map (.powers f) φ
  have hsurj : Function.Surjective ψ :=
    surjective_localizedAway_of_D_subset_moduleMapResidueSurjectiveLocus φ f hW
  letI : Module.Projective (Localization.Away f) (LocalizedModule.Away f P₂) :=
    Module.projective_of_isLocalizedModule (.powers f) (LocalizedModule.mkLinearMap (.powers f) P₂)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property ψ (LinearMap.id) hsurj
  let κ :
      LinearMap.ker φ →ₗ[R] LinearMap.ker ψ :=
    LinearMap.toKerIsLocalized
      (p := .powers f)
      (f := LocalizedModule.mkLinearMap (.powers f) P₁)
      (f' := LocalizedModule.mkLinearMap (.powers f) P₂)
      φ
  letI : IsLocalizedModule (.powers f) κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization (.powers f))
      (p := .powers f)
      (f := LocalizedModule.mkLinearMap (.powers f) P₁)
      (f' := LocalizedModule.mkLinearMap (.powers f) P₂)
      φ
  let e :
      LocalizedModule.Away f (LinearMap.ker φ) ≃ₗ[Localization.Away f]
        LinearMap.ker ψ :=
    (IsLocalizedModule.iso (.powers f) κ).extendScalarsOfIsLocalization
      (.powers f) (Localization.Away f)
  have hfiniteKer : Module.Finite (Localization.Away f) (LinearMap.ker ψ) := by
    let hCompl : IsCompl (LinearMap.ker ψ) (LinearMap.range σ) :=
      (range_isCompl_ker_of_split ψ σ hσ).symm
    let π :
        LocalizedModule.Away f P₁ →ₗ[Localization.Away f]
          LinearMap.ker ψ :=
      (LinearMap.ker ψ).linearProjOfIsCompl (LinearMap.range σ) hCompl
    have hπ : Function.Surjective π := Submodule.linearProjOfIsCompl_surjective hCompl
    exact Module.Finite.of_surjective π hπ
  have hprojKer : Module.Projective (Localization.Away f) (LinearMap.ker ψ) :=
    by
      letI : Module.Projective (Localization.Away f) (LocalizedModule.Away f P₁) :=
        Module.projective_of_isLocalizedModule (.powers f) (LocalizedModule.mkLinearMap (.powers f) P₁)
      exact kernel_projective_of_split_surjective ψ σ hσ
  constructor
  · exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  · exact Module.Projective.of_equiv e.symm

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
