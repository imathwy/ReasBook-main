import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Lemma_10_126_4
import StacksProject_2024.Chap10.Lemma_10_150_4
import StacksProject_2024.Chap10.Lemma_10_9_5
import StacksProject_2024.Chap15.Lemma_15_18_3
import StacksProject_2024.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum
open scoped TensorProduct

universe u v w x y z

noncomputable section

section DirectLimitDescent

variable {R : Type u} {S : Type v} {M : Type w} {Λ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
variable [Preorder Λ] [IsDirectedOrder Λ] [Nonempty Λ]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling:
- primary domain: directed colimits of commutative `R`-algebras and flat-over-base loci on closed
  subsets;
- sampled owner declarations:
  `PrimeSpectrum.zeroLocus`,
  `stacks_project.Chap10.Definition_10_17_1`'s notation owner `V(-)`,
  `Ring.DirectLimit.algebraMap`,
  `Ring.DirectLimit.algebraMap_eq_of`,
  `Ring.DirectLimit.instAlgebra`,
  `Module.flatOverBaseLocus`;
- best owner abstraction: the direct-limit `R`-algebra owner `Ring.DirectLimit.algebraMap`;
- layer triage:
  - `source-facing`: Lemma 15.19.4;
  - `core/canonical`: `Module.flatOverBaseLocus` and `Ring.DirectLimit.algebraMap`;
  - `bridge/view`: passing to the underlying ring-hom system of an `AlgHom`-valued directed
    system when forming `Ring.DirectLimit`.

Primitive data are the stage rings, their `R`-algebra structures, the directed system, and the
stage ideal family. The direct-limit `R`-algebra structure is derived API and should therefore be
reused from the chapter-10 owner rather than rebuilt from a separate compatibility witness on raw
ring homomorphisms.
-/

section

variable (J : Ideal S)
variable (A : Λ → Type y) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (φ : ∀ i j, i ≤ j → A i →ₐ[R] A j)
variable [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)]
variable (I : ∀ i, Ideal (A i))

local notation "ρ" => fun i j h ↦ (φ i j h : A i →+* A j)
local notation "A∞" => Ring.DirectLimit A ρ
local notation "ι∞" => Ring.DirectLimit.of A ρ
local notation "I∞" => ⨆ i, Ideal.map (ι∞ i) (I i)
local notation "S∞" => S ⊗[R] A∞
local notation "M∞" => S∞ ⊗[S] M
local notation "K∞" =>
  (Ideal.map (algebraMap A∞ S∞) I∞ + Ideal.map (algebraMap S S∞) J : Ideal S∞)
local notation "S[" i "]" => S ⊗[R] A i
local notation "M[" i "]" => S[i] ⊗[S] M
local notation "K[" i "]" =>
  (Ideal.map (algebraMap (A i) S[i]) (I i) + Ideal.map (algebraMap S S[i]) J : Ideal S[i])

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: an essentially finitely presented map factors through a finitely
presented algebra followed by a localization. -/
lemma exists_finitePresentation_factorization
    (hS : RingHom.EssFinitePresentation (algebraMap R S)) :
    ∃ (P : Type (max u v)) (_ : CommRing P) (g : R →+* P) (_ : g.FinitePresentation)
      (T : Submonoid P) (_ : Algebra P S) (_ : IsLocalization T S),
      algebraMap R S = (algebraMap P S).comp g := by
  -- This is exactly the owner-level unpacking of essential finite presentation.
  exact
    (RingHom.essFinitePresentation_iff_exists_finitePresentation (algebraMap R S)).1 hS

/-- Helper for Lemma 15.19.4: the algebra-side factorization of an essentially finitely presented
map can be packaged directly with the finite-presentation typeclass on the intermediate algebra. -/
lemma exists_finitePresentation_localization_model
    (hS : RingHom.EssFinitePresentation (algebraMap R S)) :
    ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra.FinitePresentation R P)
      (T : Submonoid P) (_ : Algebra P S) (_ : IsLocalization T S),
      algebraMap R S = (algebraMap P S).comp (algebraMap R P) := by
  -- First extract the ring-hom factorization provided by essential finite presentation.
  obtain ⟨P, _, g, hgfin, T, hPS, hloc, hgS⟩ :=
    exists_finitePresentation_factorization (R := R) (S := S) hS
  letI : Algebra R P := g.toAlgebra
  letI : Algebra.FinitePresentation R P := by
    rw [← RingHom.finitePresentation_algebraMap]
    exact hgfin
  -- Replace the abstract map `g` by the canonical algebra map for the induced `R`-algebra
  -- structure on `P`.
  refine ⟨P, inferInstance, inferInstance, inferInstance, T, hPS, hloc, ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using hgS

omit [IsDirectedOrder Λ] [Nonempty Λ]
  [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)] [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: each stage ideal maps into the direct-limit ideal `I∞`. -/
lemma stage_ideal_map_le_directLimitIdeal (i : Λ) :
    Ideal.map (ι∞ i) (I i) ≤ I∞ := by
  -- The colimit ideal is defined as the supremum of the stagewise images.
  exact le_iSup_of_le i le_rfl

omit [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)] [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: the limit-side closed-subset hypothesis can be read primewise using
the chapter flat-locus owner. -/
lemma limit_zeroLocus_add_subset_flatOverBaseLocus_iff
    (hflat_inf : V((K∞ : Set S∞)) ⊆ Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∀ q : PrimeSpectrum S∞,
      q ∈ V((K∞ : Set S∞)) →
        Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞) := by
  -- Rewrite the closed-subset inclusion using `15.18.0.1`, then specialize to a point.
  exact
    (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
      (R := A∞) (S := S∞) (M := M∞) K∞).1 <| by
        simpa using hflat_inf

/-- Helper for Lemma 15.19.4: after replacing `S` by the canonical localization target
`Localization T`, the given finitely presented `S`-module `M` is finitely presented over that
localization ring by restriction of scalars. -/
lemma localization_target_module_finitePresentation
    {P : Type*} [CommRing P] (T : Submonoid P)
    {S : Type*} [CommRing S] [Algebra P S] [IsLocalization T S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] :
    let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
    letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
    letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
    letI : IsScalarTower (Localization T) S M := IsScalarTower.of_compHom (Localization T) S M
    Module.FinitePresentation (Localization T) M := by
  let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
  letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
  letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
  letI : IsScalarTower (Localization T) S M := IsScalarTower.of_compHom (Localization T) S M
  have hSfp : Module.FinitePresentation (Localization T) S := by
    -- The localization target acts on `S` through an isomorphism, so `S` is finitely presented as
    -- a module over `Localization T`.
    refine Module.finitePresentation_of_surjective (Algebra.linearMap (Localization T) S) ?_ ?_
    · simpa using
        (show Function.Surjective (algebraMap (Localization T) S) from by
          simpa [RingHom.algebraMap_toAlgebra, e] using e.symm.surjective)
    · have hinj : Function.Injective (algebraMap (Localization T) S) := by
        simpa [RingHom.algebraMap_toAlgebra, e] using e.symm.injective
      rw [LinearMap.ker_eq_bot.2 hinj]
      exact Submodule.fg_bot
  letI : Module.FinitePresentation (Localization T) S := hSfp
  -- With the intermediate ring itself finitely presented as a module, transitivity applies.
  exact Module.FinitePresentation.trans (Localization T) M S

/-- Helper for Lemma 15.19.4: over the canonical localization target `Localization T`, the
localized module `LocalizedModule T M` identifies with the already localized module `M`. -/
private instance localizedModule_id_isLocalizedModule
    {P : Type*} [CommRing P] (T : Submonoid P)
    {M : Type*} [AddCommGroup M] [Module P M]
    [Module (Localization T) M] [IsScalarTower P (Localization T) M] :
    IsLocalizedModule T (LinearMap.id : M →ₗ[P] M) := by
  -- The identity map is a localization map because `M` already carries the canonical localized
  -- scalar action.
  simpa using (isLocalizedModule_id T M (Localization T))

/-- Helper for Lemma 15.19.4: the canonical localization owner compares `LocalizedModule T M`
directly with the identity-localized target `M` over `Localization T`. -/
noncomputable abbrev localizedModule_linearEquiv_localizationTarget
    {P : Type*} [CommRing P] (T : Submonoid P)
    {M : Type*} [AddCommGroup M] [Module P M]
    [Module (Localization T) M] [IsScalarTower P (Localization T) M] :
    LocalizedModule T M ≃ₗ[Localization T] M :=
  -- Compare the universal localization map with the identity map into the already localized
  -- target, then promote the resulting `P`-linear equivalence to the localization ring.
  (IsLocalizedModule.linearEquiv T
    (LocalizedModule.mkLinearMap T M)
    (LinearMap.id : M →ₗ[P] M)).extendScalarsOfIsLocalization T (Localization T)

/-- Helper for Lemma 15.19.4: the localization target `Localization T` acts on `M` compatibly
with the original `P → S → M` action. -/
lemma localization_target_isScalarTower_of_algEquiv
    {P : Type*} [CommRing P] (T : Submonoid P)
    {S : Type*} [CommRing S] [Algebra P S] [IsLocalization T S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module P M] [IsScalarTower P S M] :
    let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
    letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
    letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
    IsScalarTower P (Localization T) M := by
  let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
  letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
  letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
  -- The transported `Localization T`-action restricts to the original `P`-action on `M`.
  exact IsScalarTower.of_algebraMap_smul fun p m ↦ by
    change e.symm (algebraMap P (Localization T) p) • m = p • m
    rw [e.symm.commutes]
    simpa using (IsScalarTower.algebraMap_smul P S M p m)

/-- Helper for Lemma 15.19.4: finite presentation over `Localization T` transports from the
identity-localized target `M` back to the canonical owner `LocalizedModule T M`. -/
lemma localizedModule_finitePresentation_of_localization_target
    {P : Type*} [CommRing P] (T : Submonoid P)
    {M : Type*} [AddCommGroup M] [Module P M]
    [Module (Localization T) M] [IsScalarTower P (Localization T) M]
    [Module.FinitePresentation (Localization T) M] :
    Module.FinitePresentation (Localization T) (LocalizedModule T M) := by
  -- Route correction: transport finite presentation through the canonical
  -- `Localization T`-linear comparison, rather than through an auxiliary `S`-linear equivalence.
  exact Module.FinitePresentation.of_equiv
    (localizedModule_linearEquiv_localizationTarget (T := T) (M := M)).symm

omit [Algebra R S] in
/-- Helper for Lemma 15.19.4: once `S` is presented as the localization of `P`, Lemma 10.126.4
produces a finitely presented `P`-module whose localization recovers `M`. -/
lemma exists_finitePresentation_module_model_of_localization_data
    {P : Type*} [CommRing P] [Algebra R P] [Algebra.FinitePresentation R P]
    (T : Submonoid P) [Algebra P S] [IsLocalization T S]
    [Module P M] [IsScalarTower P S M] :
    ∃ (N : Type (max u v w)) (_ : AddCommGroup N) (_ : Module P N) (_ : Module.FinitePresentation P N)
      (f : N →ₗ[P] M)
      (e : LocalizedModule T N ≃ₗ[Localization T] LocalizedModule T M),
      e.toLinearMap = LocalizedModule.map T f := by
  let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
  letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
  letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
  letI : IsScalarTower P (Localization T) M :=
    localization_target_isScalarTower_of_algEquiv (T := T) (S := S) (M := M)
  have hMfpLocalizationTarget : Module.FinitePresentation (Localization T) M :=
    localization_target_module_finitePresentation (T := T) (S := S) (M := M)
  letI : Module.FinitePresentation (Localization T) M := hMfpLocalizationTarget
  have hLocalizedFp : Module.FinitePresentation (Localization T) (LocalizedModule T M) :=
    localizedModule_finitePresentation_of_localization_target (T := T) (M := M)
  letI : Module.FinitePresentation (Localization T) (LocalizedModule T M) := hLocalizedFp
  -- Route correction: after normalizing the localization owner to `Localization T`, Lemma
  -- `10.126.4` applies directly to the canonical localized module `LocalizedModule T M`.
  simpa using
    (exists_finitePresentation_module_with_localizedLinearEquiv (R := P) (S := T) (M := M))

/-- Helper for Lemma 15.19.4: combining the essential finite-presentation factorization of
`R → S` with Lemma 10.126.4 yields a finitely presented localization model for `M`. -/
lemma exists_localization_model_with_finitely_presented_module_model
    (hS : RingHom.EssFinitePresentation (algebraMap R S)) :
    ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra.FinitePresentation R P)
      (T : Submonoid P) (_ : Algebra P S) (_ : IsLocalization T S)
      (_ : Module P M) (_ : IsScalarTower P S M)
      (N : Type (max u v w)) (_ : AddCommGroup N) (_ : Module P N) (_ : Module.FinitePresentation P N)
      (f : N →ₗ[P] M)
      (e : LocalizedModule T N ≃ₗ[Localization T] LocalizedModule T M),
      e.toLinearMap = LocalizedModule.map T f := by
  obtain ⟨P, _, _, hPfp, T, hPS, hloc, _⟩ :=
    exists_finitePresentation_localization_model (R := R) (S := S) hS
  letI : Module P M := Module.compHom M (algebraMap P S)
  letI : IsScalarTower P S M := IsScalarTower.of_compHom P S M
  obtain ⟨N, _, _, hNfp, f, e, he⟩ :=
    exists_finitePresentation_module_model_of_localization_data
      (R := R) (S := S) (M := M) (T := T)
  -- Package the algebra model and the descended finitely presented module model together.
  exact
    ⟨P, inferInstance, inferInstance, hPfp, T, hPS, hloc, inferInstance, inferInstance,
      N, inferInstance, inferInstance, hNfp, f, e, he⟩

omit [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)] in
/-- Helper for Lemma 15.19.4: a primewise flatness statement on the image of `V(K∞)` in a model
ring upgrades directly to inclusion of that image in the model flat locus. -/
lemma image_subset_flatOverBaseLocus_of_primewise
    {PInf : Type*} [CommRing PInf] [Algebra A∞ PInf]
    {NInf : Type*} [AddCommGroup NInf] [Module PInf NInf] [Module A∞ NInf]
    [IsScalarTower A∞ PInf NInf]
    (sigmaInf : PInf →+* S∞)
    (hprimewise :
      ∀ p : PrimeSpectrum PInf,
        p ∈ (PrimeSpectrum.comap sigmaInf) '' V((K∞ : Set S∞)) →
          Module.Flat A∞ (LocalizedModule.AtPrime p.asIdeal NInf)) :
    (PrimeSpectrum.comap sigmaInf) '' V((K∞ : Set S∞)) ⊆
      Module.flatOverBaseLocus A∞ PInf NInf := by
  intro p hp
  -- Rewrite the target set-membership goal through the owner characterization of the flat locus.
  exact (Module.mem_flatOverBaseLocus A∞ PInf NInf p).2 (hprimewise p hp)

/-- Helper for Lemma 15.19.4: if the image of the limit-side closed subset in the finitely
presented localization model lies in the flat locus, then finitely many basic opens on the model
already cover that image, and their images in `S∞` together with `K∞` generate the unit ideal. -/
lemma exists_finite_basicOpen_cover_for_limit_localization_model
    {PInf : Type*} [CommRing PInf] [Algebra A∞ PInf]
    {NInf : Type*} [AddCommGroup NInf] [Module PInf NInf] [Module A∞ NInf]
    [IsScalarTower A∞ PInf NInf]
    [Algebra.FinitePresentation A∞ PInf] [Module.FinitePresentation PInf NInf]
    (sigmaInf : PInf →+* S∞)
    (himage_subset :
      (PrimeSpectrum.comap sigmaInf) '' V((K∞ : Set S∞)) ⊆
        Module.flatOverBaseLocus A∞ PInf NInf) :
    ∃ n : ℕ, ∃ gInf : Fin n → PInf,
      (∀ a, (basicOpen (gInf a) : Set (PrimeSpectrum PInf)) ⊆
        Module.flatOverBaseLocus A∞ PInf NInf) ∧
      Ideal.span (Set.range (fun a => sigmaInf (gInf a))) + K∞ = ⊤ := by
  let flatLocus : Set (PrimeSpectrum PInf) := Module.flatOverBaseLocus A∞ PInf NInf
  let imageSubset : Set (PrimeSpectrum PInf) :=
    (PrimeSpectrum.comap sigmaInf) '' V((K∞ : Set S∞))
  have hopen : IsOpen flatLocus := by
    simpa [flatLocus] using
      Module.isOpen_flatOverBaseLocus_of_finitePresentation (R := A∞) (S := PInf) (M := NInf)
  have hcompact_zero : IsCompact (V((K∞ : Set S∞))) := by
    -- The closed subset defined by `K∞` is compact in the spectral space `Spec(S∞)`.
    simpa using (isClosed_zeroLocus (K∞ : Set S∞)).isCompact
  have hcompact_image : IsCompact imageSubset := by
    -- Passing to the finitely presented localization model preserves compactness.
    simpa [imageSubset] using
      hcompact_zero.image (PrimeSpectrum.continuous_comap sigmaInf)
  have hbasic :
      ∀ x : imageSubset,
        ∃ g : PInf,
          x.1 ∈ (basicOpen g : Set (PrimeSpectrum PInf)) ∧
            (basicOpen g : Set (PrimeSpectrum PInf)) ⊆ flatLocus := by
    intro x
    -- Each point of the compact image has a basic-open neighborhood inside the flat locus.
    have hxnhds : flatLocus ∈ nhds x.1 := hopen.mem_nhds (himage_subset x.2)
    rcases (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 hxnhds with
      ⟨U, hU, hxU, hUsub⟩
    rcases hU with ⟨g, rfl⟩
    exact ⟨g, hxU, hUsub⟩
  choose g hgmem hgsub using hbasic
  obtain ⟨t, ht⟩ :=
    hcompact_image.elim_finite_subcover
      (fun x : imageSubset ↦ (basicOpen (g x) : Set (PrimeSpectrum PInf)))
      (fun x ↦ (basicOpen (g x)).2)
      (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hgmem ⟨x, hx⟩⟩)
  let ι := ↥t
  let gsub : ι → PInf := fun a ↦ g a.1
  have hflat_basic :
      ∀ a : ι, (basicOpen (gsub a) : Set (PrimeSpectrum PInf)) ⊆ flatLocus := by
    intro a
    exact hgsub a.1
  have hcover :
      imageSubset ⊆ ⋃ a : ι, (basicOpen (gsub a) : Set (PrimeSpectrum PInf)) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (ht hx) with ⟨y, hyt, hy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hy⟩
  have hspan_sub : Ideal.span (Set.range (fun a ↦ sigmaInf (gsub a))) + K∞ = ⊤ := by
    -- A maximal ideal containing both `K∞` and all `sigmaInf(gsub a)` would define a point of
    -- `V(K∞)` whose image in the model lies outside the asserted finite basic-open cover.
    by_contra htop
    obtain ⟨m, hmmax, hmle⟩ :=
      Ideal.exists_le_maximal (Ideal.span (Set.range (fun a ↦ sigmaInf (gsub a))) + K∞) htop
    let q : PrimeSpectrum S∞ := ⟨m, hmmax.isPrime⟩
    have hKle : K∞ ≤ m := le_trans le_sup_right hmle
    have hqK : q ∈ V((K∞ : Set S∞)) := (mem_zeroLocus q (K∞ : Set S∞)).2 hKle
    have hq_image : PrimeSpectrum.comap sigmaInf q ∈ imageSubset := by
      exact ⟨q, hqK, rfl⟩
    rcases Set.mem_iUnion.mp (hcover hq_image) with ⟨a, ha⟩
    have hspanm :
        Ideal.span (Set.range (fun a ↦ sigmaInf (gsub a))) ≤ m := le_trans le_sup_left hmle
    have hgm : sigmaInf (gsub a) ∈ m := hspanm (Ideal.subset_span (Set.mem_range_self a))
    have ha' : q ∈ (basicOpen (sigmaInf (gsub a)) : Set (PrimeSpectrum S∞)) := by
      -- Rewrite the model basic open back along `Spec(sigmaInf)`.
      simpa [PrimeSpectrum.comap_basicOpen] using ha
    exact (PrimeSpectrum.mem_basicOpen (sigmaInf (gsub a)) q).1 ha' hgm
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let gInf : Fin (Fintype.card ι) → PInf := fun a ↦ gsub (e.symm a)
  have hflat_basic_fin :
      ∀ a : Fin (Fintype.card ι),
        (basicOpen (gInf a) : Set (PrimeSpectrum PInf)) ⊆ flatLocus := by
    intro a
    exact hflat_basic (e.symm a)
  have hrange :
      Set.range (fun a ↦ sigmaInf (gInf a)) = Set.range (fun a ↦ sigmaInf (gsub a)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e.symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e a, by simp [gInf, gsub, e]⟩
  have hspan_eq :
      Ideal.span (Set.range (fun a ↦ sigmaInf (gInf a))) =
        Ideal.span (Set.range (fun a ↦ sigmaInf (gsub a))) := by
    rw [hrange]
  refine ⟨Fintype.card ι, gInf, hflat_basic_fin, ?_⟩
  calc
    Ideal.span (Set.range (fun a ↦ sigmaInf (gInf a))) + K∞ =
        Ideal.span (Set.range (fun a ↦ sigmaInf (gsub a))) + K∞ := by
          rw [hspan_eq]
    _ = ⊤ := hspan_sub

/-- Helper for Lemma 15.19.4: once the finite cover relation is expressed as an equality with the
top ideal, the explicit witness needed for stage descent is the element `1`. -/
lemma one_mem_span_add_of_span_add_eq_top
    {T : Type*} [CommRing T] {J K : Ideal T}
    (hTop : J + K = ⊤) :
    (1 : T) ∈ J + K := by
  -- Repackage the equality with `⊤` as the concrete `1 ∈ J + K` witness used later.
  simpa [Ideal.eq_top_iff_one] using hTop

omit [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)] [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: an element coming from the colimit ideal summand already lies in
the limit-side mixed cover ideal `K∞`. -/
lemma mem_limit_coverIdeal_of_mem_limitIdeal
    {x : S∞} (hx : x ∈ Ideal.map (algebraMap A∞ S∞) I∞) :
    x ∈ K∞ := by
  -- Keep the mixed cover bookkeeping explicit by inserting the `I∞`-part into the left summand.
  exact le_sup_left hx

omit [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)] [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: a fixed `J`-term remains inside the limit-side mixed cover ideal
`K∞`. -/
lemma mem_limit_coverIdeal_of_mem_fixedIdeal
    {x : S∞} (hx : x ∈ Ideal.map (algebraMap S S∞) J) :
    x ∈ K∞ := by
  -- Route correction: the `J`-part of the cover does not need descent; it is the right summand of
  -- `K∞` by definition.
  exact le_sup_right hx

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: an element from the stage ideal summand already lies in the stage
mixed cover ideal `K[i]`. -/
lemma mem_stage_coverIdeal_of_mem_stageIdeal
    (i : Λ) {x : S[i]}
    (hx : x ∈ Ideal.map (algebraMap (A i) S[i]) (I i)) :
    x ∈ K[i] := by
  -- The stagewise `I i` contribution is the left summand of `K[i]`.
  exact le_sup_left hx

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: a fixed `J`-term remains inside every stage mixed cover ideal
`K[i]`. -/
lemma mem_stage_coverIdeal_of_mem_fixedIdeal
    (i : Λ) {x : S[i]}
    (hx : x ∈ Ideal.map (algebraMap S S[i]) J) :
    x ∈ K[i] := by
  -- The source-faithful mixed-cover descent keeps the `J`-part fixed, so it enters through the
  -- right summand of `K[i]`.
  exact le_sup_right hx

omit [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)] in
/-- Helper for Lemma 15.19.4: a localization comparison at every point of `Spec(S∞)` transports
the limit-side primewise flatness on `V(K∞)` back to the image of that closed subset in the model
spectrum. -/
lemma primewise_flat_on_comap_image_of_localization_comparison
    {PInf : Type*} [CommRing PInf] [Algebra A∞ PInf]
    {NInf : Type*} [AddCommGroup NInf] [Module PInf NInf] [Module A∞ NInf]
    [IsScalarTower A∞ PInf NInf]
    (sigmaInf : PInf →+* S∞)
    (eAtPrime :
      ∀ q : PrimeSpectrum S∞,
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmaInf q).asIdeal NInf ≃ₗ[A∞]
          LocalizedModule.AtPrime q.asIdeal M∞)
    (hflat_inf_primewise :
      ∀ q : PrimeSpectrum S∞,
        q ∈ V((K∞ : Set S∞)) →
          Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞)) :
    ∀ p : PrimeSpectrum PInf,
      p ∈ (PrimeSpectrum.comap sigmaInf) '' V((K∞ : Set S∞)) →
        Module.Flat A∞ (LocalizedModule.AtPrime p.asIdeal NInf) := by
  intro p hp
  rcases hp with ⟨q, hq, rfl⟩
  have hqflat : Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞) :=
    hflat_inf_primewise q hq
  letI : Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞) := hqflat
  -- Transport the target-side flatness across the localized comparison into the model.
  exact Module.Flat.of_linearEquiv (eAtPrime q)

omit [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)] in
/-- Helper for Lemma 15.19.4: once the localization comparison is available, the image of
`V(K∞)` in the model spectrum lies in the model flat-over-base locus. -/
lemma image_subset_flatOverBaseLocus_of_localization_comparison
    {PInf : Type*} [CommRing PInf] [Algebra A∞ PInf]
    {NInf : Type*} [AddCommGroup NInf] [Module PInf NInf] [Module A∞ NInf]
    [IsScalarTower A∞ PInf NInf]
    (sigmaInf : PInf →+* S∞)
    (eAtPrime :
      ∀ q : PrimeSpectrum S∞,
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmaInf q).asIdeal NInf ≃ₗ[A∞]
          LocalizedModule.AtPrime q.asIdeal M∞)
    (hflat_inf_primewise :
      ∀ q : PrimeSpectrum S∞,
        q ∈ V((K∞ : Set S∞)) →
          Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞)) :
    (PrimeSpectrum.comap sigmaInf) '' V((K∞ : Set S∞)) ⊆
      Module.flatOverBaseLocus A∞ PInf NInf := by
  -- Upgrade the transported primewise flatness into the source-facing flat-locus inclusion.
  exact image_subset_flatOverBaseLocus_of_primewise
    (J := J) (A := A) (φ := φ) (I := I) (sigmaInf := sigmaInf)
    (primewise_flat_on_comap_image_of_localization_comparison
      (J := J) (A := A) (φ := φ) (I := I) (sigmaInf := sigmaInf)
      eAtPrime hflat_inf_primewise)

/-- Helper for Lemma 15.19.4: once the pointwise localization comparison for the chosen
localization model is available, the generic image-in-flat-locus argument immediately produces
the finite model-side basic-open cover used in the source proof. -/
lemma exists_finite_basicOpen_cover_of_limit_hypothesis_via_localization_comparison
    {PInf : Type*} [CommRing PInf] [Algebra A∞ PInf]
    {NInf : Type*} [AddCommGroup NInf] [Module PInf NInf] [Module A∞ NInf]
    [IsScalarTower A∞ PInf NInf]
    [Algebra.FinitePresentation A∞ PInf] [Module.FinitePresentation PInf NInf]
    (sigmaInf : PInf →+* S∞)
    (eAtPrime :
      ∀ q : PrimeSpectrum S∞,
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmaInf q).asIdeal NInf ≃ₗ[A∞]
          LocalizedModule.AtPrime q.asIdeal M∞)
    (hflat_inf : V((K∞ : Set S∞)) ⊆ Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∃ n : ℕ, ∃ gInf : Fin n → PInf,
      (∀ a, (basicOpen (gInf a) : Set (PrimeSpectrum PInf)) ⊆
        Module.flatOverBaseLocus A∞ PInf NInf) ∧
      Ideal.span (Set.range (fun a => sigmaInf (gInf a))) + K∞ = ⊤ := by
  have hflat_inf_primewise :
      ∀ q : PrimeSpectrum S∞,
        q ∈ V((K∞ : Set S∞)) →
          Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞) :=
    limit_zeroLocus_add_subset_flatOverBaseLocus_iff
      (A := A) (φ := φ) (I := I) (J := J) (M := M) hflat_inf
  have himage_subset :
      (PrimeSpectrum.comap sigmaInf) '' V((K∞ : Set S∞)) ⊆
        Module.flatOverBaseLocus A∞ PInf NInf :=
    image_subset_flatOverBaseLocus_of_localization_comparison
      (A := A) (φ := φ) (I := I) (J := J) (M := M) sigmaInf eAtPrime hflat_inf_primewise
  -- With the transported image inclusion in hand, compactness yields the finite model-side cover.
  exact
    exists_finite_basicOpen_cover_for_limit_localization_model
      (J := J) (A := A) (φ := φ) (I := I) (sigmaInf := sigmaInf) himage_subset

/-- Helper for Lemma 15.19.4: a pointwise localization comparison pushes a model-side basic-open
containment in the flat locus forward along the localization map. -/
lemma image_basicOpen_subset_flatOverBaseLocus_of_localization_comparison
    {A0 : Type*} [CommRing A0]
    {P0 : Type*} [CommRing P0] [Algebra A0 P0]
    {S0 : Type*} [CommRing S0] [Algebra A0 S0]
    {N0 : Type*} [AddCommGroup N0] [Module P0 N0] [Module A0 N0]
    [IsScalarTower A0 P0 N0]
    {M0 : Type*} [AddCommGroup M0] [Module S0 M0] [Module A0 M0]
    [IsScalarTower A0 S0 M0]
    (sigma : P0 →+* S0)
    (eAtPrime :
      ∀ q : PrimeSpectrum S0,
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigma q).asIdeal N0 ≃ₗ[A0]
          LocalizedModule.AtPrime q.asIdeal M0)
    {g : P0}
    (hbasic :
      (basicOpen g : Set (PrimeSpectrum P0)) ⊆ Module.flatOverBaseLocus A0 P0 N0) :
    (basicOpen (sigma g) : Set (PrimeSpectrum S0)) ⊆
      Module.flatOverBaseLocus A0 S0 M0 := by
  intro q hq
  have hpbasic :
      PrimeSpectrum.comap sigma q ∈ (basicOpen g : Set (PrimeSpectrum P0)) := by
    -- Pull the basic-open membership back along the spectrum map induced by `sigma`.
    simpa [PrimeSpectrum.comap_basicOpen] using hq
  have hpflat :
      Module.Flat A0
        (LocalizedModule.AtPrime (PrimeSpectrum.comap sigma q).asIdeal N0) :=
    (Module.mem_flatOverBaseLocus A0 P0 N0 _).1 (hbasic hpbasic)
  letI :
      Module.Flat A0
        (LocalizedModule.AtPrime (PrimeSpectrum.comap sigma q).asIdeal N0) := hpflat
  have hqflat : Module.Flat A0 (LocalizedModule.AtPrime q.asIdeal M0) := by
    -- Transport the model-side flatness back to the target-side localization at `q`.
    exact Module.Flat.of_linearEquiv (eAtPrime q).symm
  exact (Module.mem_flatOverBaseLocus A0 S0 M0 q).2 hqflat

/-- Helper for Lemma 15.19.4: base changing the localization model `P → S` along `R → B`
identifies `S ⊗[R] B` as the localization of `P ⊗[R] B` at the image of `T`. -/
lemma tensor_baseChange_isLocalization_of_localization_model
    {P : Type*} [CommRing P] [Algebra R P]
    (sigmaP : P →ₐ[R] S) (T : Submonoid P)
    {B : Type*} [CommRing B] [Algebra R B] :
    let sigmaB : (P ⊗[R] B) →+* (S ⊗[R] B) :=
      (Algebra.TensorProduct.map
        (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
        sigmaP (AlgHom.id R B)).toRingHom
    let U : Submonoid (P ⊗[R] B) := Algebra.algebraMapSubmonoid (P ⊗[R] B) T
    letI : Algebra (P ⊗[R] B) (S ⊗[R] B) := sigmaB.toAlgebra
    letI : Algebra P (P ⊗[R] B) := Algebra.TensorProduct.leftAlgebra
    letI : Algebra P (S ⊗[R] B) := Algebra.compHom (S ⊗[R] B) (algebraMap P (P ⊗[R] B))
    IsLocalization U (S ⊗[R] B) := by
  let sigmaB : (P ⊗[R] B) →+* (S ⊗[R] B) :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
      sigmaP (AlgHom.id R B)).toRingHom
  let U : Submonoid (P ⊗[R] B) := Algebra.algebraMapSubmonoid (P ⊗[R] B) T
  letI : Algebra (P ⊗[R] B) (S ⊗[R] B) := sigmaB.toAlgebra
  letI : Algebra P (P ⊗[R] B) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra P (S ⊗[R] B) := Algebra.compHom (S ⊗[R] B) (algebraMap P (P ⊗[R] B))
  -- The tensor square is the canonical pushout of `P → S` along `P → P ⊗[R] B`, so the
  -- localization owner identifies the codomain as the required base-changed localization.
  rw [Algebra.isLocalization_iff_isPushout
    (R := P) (S := T) (A := S) (T := P ⊗[R] B) (B := S ⊗[R] B)]
  infer_instance

/-- Helper for Lemma 15.19.4: if `S₀` is any localization target of `A` at `U`, then localizing
`LocalizedModule U X` at a prime of `S₀` is the same as localizing `X` at the contracted prime,
first over `S₀`. -/
noncomputable def localized_atPrime_linearEquiv_over_isLocalization_target
    {A : Type*} [CommRing A]
    {S₀ : Type*} [CommRing S₀] [Algebra A S₀]
    {X : Type*} [AddCommGroup X] [Module A X]
    (U : Submonoid A) [IsLocalization U S₀]
    (q : PrimeSpectrum S₀) :
    LocalizedModule.AtPrime q.asIdeal (LocalizedModule U X) ≃ₗ[S₀]
      LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal X := by
  let e :
      Localization.AtPrime
          (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal ≃ₐ[A]
        Localization.AtPrime q.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization U q.asIdeal
  let _ : Module (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal X) :=
    Module.compHom _ e.symm.toRingHom
  let _ : Module S₀
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal X) :=
    Module.compHom _
      (e.symm.toRingHom.comp
        (algebraMap S₀ (Localization.AtPrime q.asIdeal)))
  let _ : IsScalarTower S₀ (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal X) := by
    -- Both scalar actions are transported along the same iterated-localization ring map.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro z m
    change e.symm (algebraMap S₀ (Localization.AtPrime q.asIdeal) z) • m = z • m
    rfl
  let gId :
      LocalizedModule.AtPrime
          (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal X →ₗ[S₀]
        LocalizedModule.AtPrime
          (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal X :=
    LinearMap.id
  let _ : IsLocalizedModule q.asIdeal.primeCompl gId := by
    -- After transporting the codomain actions, the target already has the required owner
    -- localization structure over `S₀`.
    simpa using
      (isLocalizedModule_id q.asIdeal.primeCompl
        (LocalizedModule.AtPrime
          (PrimeSpectrum.comap (algebraMap A S₀) q).asIdeal X)
        (Localization.AtPrime q.asIdeal))
  -- Compare the universal at-prime localization map on `LocalizedModule U X` with the identity
  -- map on the already normalized target.
  exact IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (LocalizedModule U X))
    gId

/-- Helper for Lemma 15.19.4: before passing to a prime localization, base change the
localization-model equivalence itself to `S ⊗[R] B`. -/
lemma tensor_baseChange_source_localizedModule_equiv
    {P : Type*} [CommRing P] [Algebra R P]
    {N : Type*} [AddCommGroup N] [Module P N]
    (sigmaP : P →ₐ[R] S) (T : Submonoid P)
    {B : Type*} [CommRing B] [Algebra R B] :
    let sigmaB : (P ⊗[R] B) →+* (S ⊗[R] B) :=
      (Algebra.TensorProduct.map
        (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
        sigmaP (AlgHom.id R B)).toRingHom
    let U : Submonoid (P ⊗[R] B) := Algebra.algebraMapSubmonoid (P ⊗[R] B) T
    letI : Algebra (P ⊗[R] B) (S ⊗[R] B) := sigmaB.toAlgebra
    letI : IsLocalization U (S ⊗[R] B) :=
      tensor_baseChange_isLocalization_of_localization_model
        (R := R) (S := S) sigmaP T
    LocalizedModule U ((P ⊗[R] B) ⊗[P] N) ≃ₗ[S ⊗[R] B] ((S ⊗[R] B) ⊗[P] N) := by
  let sigmaB : (P ⊗[R] B) →+* (S ⊗[R] B) :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
      sigmaP (AlgHom.id R B)).toRingHom
  let U : Submonoid (P ⊗[R] B) := Algebra.algebraMapSubmonoid (P ⊗[R] B) T
  letI : Algebra (P ⊗[R] B) (S ⊗[R] B) := sigmaB.toAlgebra
  letI : IsLocalization U (S ⊗[R] B) :=
    tensor_baseChange_isLocalization_of_localization_model
      (R := R) (S := S) sigmaP T
  letI : Algebra P (P ⊗[R] B) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra P (S ⊗[R] B) := Algebra.compHom (S ⊗[R] B) (algebraMap P (P ⊗[R] B))
  let eLocalized :
      LocalizedModule U ((P ⊗[R] B) ⊗[P] N) ≃ₗ[S ⊗[R] B]
        ((S ⊗[R] B) ⊗[P ⊗[R] B] ((P ⊗[R] B) ⊗[P] N)) :=
    (IsLocalizedModule.linearEquiv U
        (LocalizedModule.mkLinearMap U ((P ⊗[R] B) ⊗[P] N))
        (TensorProduct.mk (P ⊗[R] B) (S ⊗[R] B) ((P ⊗[R] B) ⊗[P] N) 1)).extendScalarsOfIsLocalization
      U (S ⊗[R] B)
  -- First rewrite the localized source as the honest tensor over `P ⊗[R] B`, then cancel the
  -- middle base-change factor over `P`.
  exact eLocalized.trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      P (P ⊗[R] B) (S ⊗[R] B) (S ⊗[R] B) N)

/-- Helper for Lemma 15.19.4: after scalar extension along the localization model, the target-side
localized module comparison collapses back to the stated `S`-tensor form. -/
lemma tensor_baseChange_target_localizedModule_equiv
    {P : Type*} [CommRing P] [Algebra R P]
    (sigmaP : P →ₐ[R] S) (T : Submonoid P)
    {B : Type*} [CommRing B] [Algebra R B] :
    let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
    letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
    letI : Algebra (Localization T) (S ⊗[R] B) :=
      Algebra.compHom (S ⊗[R] B) e.symm.toRingHom
    letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
    letI : IsScalarTower P (Localization T) M :=
      localization_target_isScalarTower_of_algEquiv (T := T) (S := S) (M := M)
    ((S ⊗[R] B) ⊗[Localization T] LocalizedModule T M) ≃ₗ[S ⊗[R] B] ((S ⊗[R] B) ⊗[S] M) := by
  let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
  letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
  letI : Algebra (Localization T) (S ⊗[R] B) := Algebra.compHom (S ⊗[R] B) e.symm.toRingHom
  letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
  letI : IsScalarTower P (Localization T) M :=
    localization_target_isScalarTower_of_algEquiv (T := T) (S := S) (M := M)
  let eLocalizedTarget :
      ((S ⊗[R] B) ⊗[Localization T] LocalizedModule T M) ≃ₗ[S ⊗[R] B]
        ((S ⊗[R] B) ⊗[Localization T] M) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (S ⊗[R] B) (S ⊗[R] B))
      (localizedModule_linearEquiv_localizationTarget (T := T) (M := M))
  let eToP :
      ((S ⊗[R] B) ⊗[Localization T] M) ≃ₗ[S ⊗[R] B]
        ((S ⊗[R] B) ⊗[P] M) :=
    ((IsLocalization.moduleTensorEquiv T (Localization T) (S ⊗[R] B) M).restrictScalars P).extendScalarsOfIsLocalization
      T (S ⊗[R] B)
  let ePToS :
      ((S ⊗[R] B) ⊗[P] M) ≃ₗ[S ⊗[R] B] ((S ⊗[R] B) ⊗[S] M) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        P S (S ⊗[R] B) (S ⊗[R] B) M).symm).trans
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (S ⊗[R] B) (S ⊗[R] B))
        (IsLocalization.moduleLid T S M))
  -- Normalize the localization-target tensor to the `P`-tensor first, then collapse the
  -- intermediate `S ⊗[P] M` factor by the localization owner `moduleLid`.
  exact eLocalizedTarget.trans (eToP.trans ePToS)

/-- Helper for Lemma 15.19.4: before passing to a prime localization, base change the
localization-model equivalence itself to `S ⊗[R] B`. -/
lemma tensor_baseChange_localizedModule_linearEquiv_of_localization_model
    {P : Type*} [CommRing P] [Algebra R P]
    {N : Type*} [AddCommGroup N] [Module P N]
    [Module P M] [IsScalarTower P S M]
    (sigmaP : P →ₐ[R] S) (T : Submonoid P)
    (f : N →ₗ[P] M)
    (eT : LocalizedModule T N ≃ₗ[Localization T] LocalizedModule T M)
    (heT : eT.toLinearMap = LocalizedModule.map T f)
    {B : Type*} [CommRing B] [Algebra R B] :
    let sigmaB : (P ⊗[R] B) →+* (S ⊗[R] B) :=
      (Algebra.TensorProduct.map
        (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
        sigmaP (AlgHom.id R B)).toRingHom
    let U : Submonoid (P ⊗[R] B) := Algebra.algebraMapSubmonoid (P ⊗[R] B) T
    letI : Algebra (P ⊗[R] B) (S ⊗[R] B) := sigmaB.toAlgebra
    letI : IsLocalization U (S ⊗[R] B) :=
      tensor_baseChange_isLocalization_of_localization_model
        (R := R) (S := S) sigmaP T
    LocalizedModule U ((P ⊗[R] B) ⊗[P] N) ≃ₗ[S ⊗[R] B] ((S ⊗[R] B) ⊗[S] M) := by
  -- Route correction: first base change the localization-model equivalence over `S ⊗[R] B`, and
  -- only then localize at a prime.
  let sigmaB : (P ⊗[R] B) →+* (S ⊗[R] B) :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
      sigmaP (AlgHom.id R B)).toRingHom
  let U : Submonoid (P ⊗[R] B) := Algebra.algebraMapSubmonoid (P ⊗[R] B) T
  letI : Algebra (P ⊗[R] B) (S ⊗[R] B) := sigmaB.toAlgebra
  letI : IsLocalization U (S ⊗[R] B) :=
    tensor_baseChange_isLocalization_of_localization_model
      (R := R) (S := S) sigmaP T
  letI : Algebra P (P ⊗[R] B) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra P (S ⊗[R] B) := Algebra.compHom (S ⊗[R] B) (algebraMap P (P ⊗[R] B))
  let e : S ≃ₐ[P] Localization T := IsLocalization.algEquiv T S (Localization T)
  letI : Algebra (Localization T) S := e.symm.toRingHom.toAlgebra
  letI : Algebra (Localization T) (S ⊗[R] B) := Algebra.compHom (S ⊗[R] B) e.symm.toRingHom
  letI : Module (Localization T) M := Module.compHom M e.symm.toRingHom
  letI : IsScalarTower P (Localization T) M :=
    localization_target_isScalarTower_of_algEquiv (T := T) (S := S) (M := M)
  let eSource :
      LocalizedModule U ((P ⊗[R] B) ⊗[P] N) ≃ₗ[S ⊗[R] B] ((S ⊗[R] B) ⊗[P] N) :=
    tensor_baseChange_source_localizedModule_equiv
      (R := R) (S := S) (sigmaP := sigmaP) (T := T)
  let eInsert :
      ((S ⊗[R] B) ⊗[P] N) ≃ₗ[S ⊗[R] B]
        ((S ⊗[R] B) ⊗[Localization T] LocalizedModule T N) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        P (Localization T) (S ⊗[R] B) (S ⊗[R] B) N).symm).trans
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (S ⊗[R] B) (S ⊗[R] B))
        (LocalizedModule.equivTensorProduct T N).symm)
  let eMiddle :
      ((S ⊗[R] B) ⊗[Localization T] LocalizedModule T N) ≃ₗ[S ⊗[R] B]
        ((S ⊗[R] B) ⊗[Localization T] LocalizedModule T M) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (S ⊗[R] B) (S ⊗[R] B))
      eT
  let eTarget :
      ((S ⊗[R] B) ⊗[Localization T] LocalizedModule T M) ≃ₗ[S ⊗[R] B]
        ((S ⊗[R] B) ⊗[S] M) :=
    tensor_baseChange_target_localizedModule_equiv
      (R := R) (S := S) (M := M) (sigmaP := sigmaP) (T := T)
  let _ := f
  let _ := heT
  -- The whole comparison is now a flat chain of canonical owner equivalences: source
  -- normalization, insertion of the `Localization T` tensor factor, scalar-extended model
  -- comparison, and target normalization back to the stated `S`-tensor.
  exact eSource.trans (eInsert.trans (eMiddle.trans eTarget))

/-- Helper for Lemma 15.19.4: once the localization model `P → S` and the localized module model
`N` are fixed, the remaining transport seam is the primewise comparison between the base-changed
model localization and the base-changed target localization. -/
lemma localizedModule_atPrime_equiv_of_localization_model
    {P : Type*} [CommRing P] [Algebra R P]
    {N : Type*} [AddCommGroup N] [Module P N]
    [Module P M] [IsScalarTower P S M]
    (sigmaP : P →ₐ[R] S) (T : Submonoid P)
    (f : N →ₗ[P] M)
    (eT : LocalizedModule T N ≃ₗ[Localization T] LocalizedModule T M)
    (heT : eT.toLinearMap = LocalizedModule.map T f)
    {B : Type*} [CommRing B] [Algebra R B]
    (q : PrimeSpectrum (S ⊗[R] B)) :
    LocalizedModule.AtPrime
        (PrimeSpectrum.comap
          ((Algebra.TensorProduct.map (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
              sigmaP (AlgHom.id R B)).toRingHom) q).asIdeal
        ((P ⊗[R] B) ⊗[P] N) ≃ₗ[B]
      LocalizedModule.AtPrime q.asIdeal ((S ⊗[R] B) ⊗[S] M) := by
  -- Route correction: isolate the ring-normalized at-prime comparison before any stage descent.
  let sigmaB : (P ⊗[R] B) →+* (S ⊗[R] B) :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := B) (C := S) (D := B)
      sigmaP (AlgHom.id R B)).toRingHom
  let U : Submonoid (P ⊗[R] B) := Algebra.algebraMapSubmonoid (P ⊗[R] B) T
  letI : Algebra (P ⊗[R] B) (S ⊗[R] B) := sigmaB.toAlgebra
  letI : IsLocalization U (S ⊗[R] B) :=
    tensor_baseChange_isLocalization_of_localization_model
      (R := R) (S := S) sigmaP T
  let eTensor :
      LocalizedModule U ((P ⊗[R] B) ⊗[P] N) ≃ₗ[S ⊗[R] B] ((S ⊗[R] B) ⊗[S] M) :=
    tensor_baseChange_localizedModule_linearEquiv_of_localization_model
      (R := R) (S := S) (M := M) (sigmaP := sigmaP) (T := T) (f := f) eT heT
  let eModelAtPrime :
      LocalizedModule.AtPrime q.asIdeal (LocalizedModule U ((P ⊗[R] B) ⊗[P] N)) ≃ₗ[S ⊗[R] B]
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmaB q).asIdeal ((P ⊗[R] B) ⊗[P] N) :=
    localized_atPrime_linearEquiv_over_isLocalization_target
      (A := P ⊗[R] B) (S₀ := S ⊗[R] B) U q
  let eTargetAtPrime :
      LocalizedModule.AtPrime q.asIdeal (LocalizedModule U ((P ⊗[R] B) ⊗[P] N)) ≃ₗ[S ⊗[R] B]
        LocalizedModule.AtPrime q.asIdeal ((S ⊗[R] B) ⊗[S] M) :=
    LinearEquiv.extendScalarsOfIsLocalization q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) eTensor
  -- After both comparisons are linear over `S ⊗[R] B`, the advertised `B`-linear statement is
  -- just scalar restriction along `B → S ⊗[R] B`.
  exact (eModelAtPrime.symm.trans eTargetAtPrime).restrictScalars B

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: descend an element of the fixed `J`-summand of `K∞` to a stage
above a prescribed lower bound. -/
lemma exists_stage_fixed_coverIdeal_element_above_of_mem_fixedIdeal
    {i₀ : Λ} {x : S∞}
    (hx : x ∈ Ideal.map (algebraMap S S∞) J) :
    ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ xj : S[j],
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj = x ∧
        xj ∈ Ideal.map (algebraMap S S[j]) J := by
  classical
  -- Route correction: keep the `J`-generators fixed in `S` and descend only the finitely many
  -- limit-side coefficients needed to express `x`.
  rw [Ideal.map, ← Ideal.submodule_span_eq] at hx
  rcases (Submodule.mem_span_set'.mp hx) with ⟨n, coeff, generators, hsum⟩
  have hpre :
      ∀ k : Fin n, ∃ a : J, algebraMap S S∞ a = (generators k : S∞) := by
    intro k
    rcases (generators k).2 with ⟨a, haJ, haeq⟩
    exact ⟨⟨a, haJ⟩, haeq⟩
  choose fixed hfixed using hpre
  obtain ⟨i, coeffi, hcoeffi⟩ :=
    exists_common_stage_lifts_of_finite_limit_family
      (R := R) (S := S) (M := M) (A := A) (φ := φ) (fInf := coeff)
  rcases exists_ge_ge i₀ i with ⟨j, hi₀j, hij⟩
  let coeffj : Fin n → S[j] :=
    fun k ↦ tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij (coeffi k)
  let xj : S[j] := ∑ k, coeffj k * algebraMap S S[j] (fixed k : S)
  have hcoeffj :
      ∀ k : Fin n,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj k) = coeff k := by
    intro k
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj k) =
          tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) i (coeffi k) := by
            exact
              tensorBaseChange_toLimit_comp_stageMap
                (A := A) (φ := φ) (S := S) i j hij (coeffi k)
      _ = coeff k := hcoeffi k
  refine ⟨j, hi₀j, xj, ?_, ?_⟩
  · -- All coefficients now live at the common stage `j`, so applying the limit map reconstructs
    -- the original finite `J`-linear combination for `x`.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj =
          ∑ k,
            tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj k) *
              algebraMap S S∞ (fixed k : S) := by
            simp [xj, coeffj, map_mul]
      _ = ∑ k, coeff k * (generators k : S∞) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hcoeffj k, hfixed k]
      _ = x := by
            simpa [smul_eq_mul] using hsum
  · -- Each summand uses a fixed generator from `J`, so the reconstructed stage element lies in
    -- the mapped ideal `Ideal.map (algebraMap S S[j]) J`.
    unfold xj
    refine Ideal.sum_mem _ ?_
    intro k hk
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem (algebraMap S S[j]) (fixed k).2)

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: a finite family of generators in the colimit ideal `I∞` can be
realized simultaneously in one stage ideal above any prescribed lower bound. -/
lemma exists_common_stage_limitIdeal_generators_above
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {i₀ : Λ} {n : ℕ} (yInf : Fin n → A∞)
    (hyInf : ∀ a, yInf a ∈ I∞) :
    ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ yj : Fin n → A j,
      (∀ a, ι∞ j (yj a) = yInf a) ∧
        (∀ a, yj a ∈ I j) := by
  classical
  have hLift :
      ∀ {n : ℕ} (i₀ : Λ) (yInf : Fin n → A∞),
        ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ yj : Fin n → A j,
          ∀ a, ι∞ j (yj a) = yInf a := by
    intro n
    induction n with
    | zero =>
        intro i₀ yInf
        refine ⟨i₀, le_rfl, Fin.elim0, ?_⟩
        intro a
        exact Fin.elim0 a
    | succ n ih =>
        intro i₀ yInf
        rcases Ring.DirectLimit.exists_of (G := A) (f := ρ) (yInf 0) with ⟨iHead, yHead, hyHead⟩
        rcases exists_ge_ge i₀ iHead with ⟨j₀, hi₀j₀, hiHeadj₀⟩
        obtain ⟨j, hj₀j, yTail, hyTail⟩ := ih j₀ (fun a : Fin n ↦ yInf a.succ)
        refine
          ⟨j, le_trans hi₀j₀ hj₀j,
            Fin.cases (φ iHead j (le_trans hiHeadj₀ hj₀j) yHead) yTail, ?_⟩
        intro a
        refine Fin.cases ?_ ?_ a
        · -- The head is first represented at some stage and then transported to the common stage.
          calc
            ι∞ j (φ iHead j (le_trans hiHeadj₀ hj₀j) yHead) = ι∞ iHead yHead := by
              simpa using
                (Ring.DirectLimit.of_f (f := ρ) (le_trans hiHeadj₀ hj₀j) yHead)
            _ = yInf 0 := hyHead
        · intro b
          exact hyTail b
  obtain ⟨j₀, hi₀j₀, y₀, hy₀eq⟩ := hLift i₀ yInf
  have hy₀mem : ∀ a, ι∞ j₀ (y₀ a) ∈ I∞ := by
    intro a
    rw [hy₀eq a]
    exact hyInf a
  obtain ⟨j, hj₀j, hyj_mem⟩ :=
    exists_common_stage_mem_directLimit_ideal_of_stage_family_above
      (A := A) (φ := φ) (I := I) hI (i := j₀) (j₀ := j₀) le_rfl y₀ hy₀mem
  refine ⟨j, le_trans hi₀j₀ hj₀j, fun a ↦ φ j₀ j hj₀j (y₀ a), ?_, ?_⟩
  · -- After transporting the common-stage lifts further to `j`, they still realize the original
    -- direct-limit generators.
    intro a
    calc
      ι∞ j (φ j₀ j hj₀j (y₀ a)) = ι∞ j₀ (y₀ a) := by
        simpa using (Ring.DirectLimit.of_f (f := ρ) hj₀j (y₀ a))
      _ = yInf a := hy₀eq a
  · -- The previous lemma arranged that these transported generators lie inside the stage ideal.
    exact hyj_mem

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: descend an element of the mapped colimit-ideal summand of `K∞` to a
stage above a prescribed lower bound. -/
lemma exists_stage_mapped_limitIdeal_element_above
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {i₀ : Λ} {x : S∞}
    (hx : x ∈ Ideal.map (algebraMap A∞ S∞) I∞) :
    ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ xj : S[j],
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj = x ∧
        xj ∈ Ideal.map (algebraMap (A j) S[j]) (I j) := by
  -- Route correction: first descend the left summand `Ideal.map (algebraMap A∞ S∞) I∞` before
  -- trying to descend arbitrary elements of the mixed cover ideal `K∞`.
  classical
  rw [Ideal.map, ← Ideal.submodule_span_eq] at hx
  rcases (Submodule.mem_span_set'.mp hx) with ⟨n, coeff, generators, hsum⟩
  have hpre :
      ∀ k : Fin n, ∃ a : I∞, algebraMap A∞ S∞ a = (generators k : S∞) := by
    intro k
    rcases (generators k).2 with ⟨a, ha, haeq⟩
    exact ⟨⟨a, ha⟩, haeq⟩
  choose yInf hyInf_eq using hpre
  obtain ⟨jI, hi₀jI, yjI, hyjI_eq, hyjI_mem⟩ :=
    exists_common_stage_limitIdeal_generators_above
      (J := J) (A := A) (φ := φ) (I := I) hI (i₀ := i₀) (n := n)
      (fun a ↦ (yInf a : A∞)) (fun a ↦ (yInf a).2)
  obtain ⟨iCoeff, coeffi, hcoeffi⟩ :=
    exists_common_stage_lifts_of_finite_limit_family
      (R := R) (S := S) (M := M) (A := A) (φ := φ) (fInf := coeff)
  rcases exists_ge_ge jI iCoeff with ⟨j, hjIj, hiCoeffj⟩
  let yj : Fin n → A j := fun a ↦ φ jI j hjIj (yjI a)
  let coeffj : Fin n → S[j] :=
    fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) (S := S) iCoeff j hiCoeffj (coeffi a)
  let xj : S[j] := ∑ a, coeffj a * algebraMap (A j) S[j] (yj a)
  have hyj_eq : ∀ a, ι∞ j (yj a) = (yInf a : A∞) := by
    intro a
    calc
      ι∞ j (yj a) = ι∞ jI (yjI a) := by
        simpa [yj] using (Ring.DirectLimit.of_f (f := ρ) hjIj (yjI a))
      _ = (yInf a : A∞) := hyjI_eq a
  have hyj_mem : ∀ a, yj a ∈ I j := by
    intro a
    exact (hI hjIj) (Ideal.mem_map_of_mem _ (hyjI_mem a))
  have hcoeffj :
      ∀ a,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj a) = coeff a := by
    intro a
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj a) =
          tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) iCoeff (coeffi a) := by
            exact
              tensorBaseChange_toLimit_comp_stageMap
                (A := A) (φ := φ) (S := S) iCoeff j hiCoeffj (coeffi a)
      _ = coeff a := hcoeffi a
  have hgenj :
      ∀ a,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j
            (algebraMap (A j) S[j] (yj a)) =
          (generators a : S∞) := by
    intro a
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j
          (algebraMap (A j) S[j] (yj a)) =
        algebraMap A∞ S∞ (ι∞ j (yj a)) := by
          rw [tensorBaseChangeToLimit, Algebra.TensorProduct.map_tmul]
          rfl
      _ = algebraMap A∞ S∞ (yInf a : A∞) := by
          rw [hyj_eq a]
      _ = (generators a : S∞) := hyInf_eq a
  refine ⟨j, le_trans hi₀jI hjIj, xj, ?_, ?_⟩
  · -- Once both coefficients and ideal generators live at the same stage, the limit map
    -- reconstructs the original finite expression for `x`.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj =
          ∑ a,
            tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj a) *
              tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j
                (algebraMap (A j) S[j] (yj a)) := by
              simp [xj, coeffj, map_mul]
      _ = ∑ a, coeff a * (generators a : S∞) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [hcoeffj a, hgenj a]
      _ = x := by
            simpa [smul_eq_mul] using hsum
  · -- Each summand uses a stage generator from `I j`, so the reconstructed element lies in the
    -- mapped stage ideal.
    unfold xj
    refine Ideal.sum_mem _ ?_
    intro a ha
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem (algebraMap (A j) S[j]) (hyj_mem a))

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: the mixed cover ideal `K[i]` maps into `K[j]` along every stage
transition once the stage ideals are compatible. -/
lemma stage_coverIdeal_map_le
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {i j : Λ} (hij : i ≤ j) :
    Ideal.map ((tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij).toRingHom) K[i] ≤ K[j] := by
  -- Push the two defining summands of `K[i]` separately along the stage transition.
  change
    Ideal.map ((tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij).toRingHom)
        (Ideal.map (algebraMap (A i) S[i]) (I i) + Ideal.map (algebraMap S S[i]) J) ≤
      K[j]
  rw [Ideal.add_eq_sup, Ideal.map_sup]
  refine sup_le ?_ ?_
  · -- The stage-ideal summand uses the directed-system compatibility hypothesis `hI`.
    calc
      Ideal.map ((tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij).toRingHom)
          (Ideal.map (algebraMap (A i) S[i]) (I i)) =
        Ideal.map (algebraMap (A j) S[j]) (Ideal.map (φ i j hij) (I i)) := by
          rw [Ideal.map_map, Ideal.map_map]
          congr 1
          ext x
          simp [tensorBaseChangeMap]
      _ ≤ Ideal.map (algebraMap (A j) S[j]) (I j) := Ideal.map_mono (hI hij)
      _ ≤ K[j] := le_sup_left
  · -- The fixed `J`-summand is preserved exactly by further base change.
    calc
      Ideal.map ((tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij).toRingHom)
          (Ideal.map (algebraMap S S[i]) J) =
        Ideal.map (algebraMap S S[j]) J := by
          rw [Ideal.map_map]
          congr 1
          ext s
          simp [tensorBaseChangeMap]
      _ ≤ K[j] := le_sup_right

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: every element of the mixed cover ideal `K∞` descends to a later
stage cover ideal `K[j]` above any prescribed lower bound. -/
lemma exists_common_stage_coverIdeal_sum_above
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {i₀ iI iJ : Λ} {xI xJ : S∞} {yI : S[iI]} {yJ : S[iJ]}
    (hiI : i₀ ≤ iI) (hiJ : i₀ ≤ iJ)
    (hyIeq : tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) iI yI = xI)
    (hyJeq : tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) iJ yJ = xJ)
    (hyI : yI ∈ Ideal.map (algebraMap (A iI) S[iI]) (I iI))
    (hyJ : yJ ∈ Ideal.map (algebraMap S S[iJ]) J) :
    ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ yj : S[j],
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j yj = xI + xJ ∧
        yj ∈ K[j] := by
  rcases exists_ge_ge iI iJ with ⟨j, hiIj, hiJj⟩
  let yIj : S[j] :=
    tensorBaseChangeMap (A := A) (φ := φ) (S := S) iI j hiIj yI
  let yJj : S[j] :=
    tensorBaseChangeMap (A := A) (φ := φ) (S := S) iJ j hiJj yJ
  let yj : S[j] := yIj + yJj
  refine ⟨j, le_trans hiI hiIj, yj, ?_, ?_⟩
  · -- After transporting both summands to the common stage `j`, the limit map recovers `xI + xJ`.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j yj =
          tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j yIj +
            tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j yJj := by
              simp [yj, yIj, yJj]
      _ = tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) iI yI +
            tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) iJ yJ := by
              rw [tensorBaseChange_toLimit_comp_stageMap (A := A) (φ := φ) (S := S) iI j hiIj yI,
                tensorBaseChange_toLimit_comp_stageMap (A := A) (φ := φ) (S := S) iJ j hiJj yJ]
      _ = xI + xJ := by rw [hyIeq, hyJeq]
  · -- Each summand lands in `K[j]` after transport, so their sum also lies in the mixed cover ideal.
    have hyI_stage : yI ∈ K[iI] :=
      mem_stage_coverIdeal_of_mem_stageIdeal
        (J := J) (A := A) (φ := φ) (I := I) iI hyI
    have hyJ_stage : yJ ∈ K[iJ] :=
      mem_stage_coverIdeal_of_mem_fixedIdeal
        (J := J) (A := A) (φ := φ) (I := I) iJ hyJ
    have hyIj_mem : yIj ∈ K[j] := by
      have hyIj_map :
          yIj ∈ Ideal.map
            ((tensorBaseChangeMap (A := A) (φ := φ) (S := S) iI j hiIj).toRingHom) K[iI] := by
        exact Ideal.mem_map_of_mem _ hyI_stage
      exact
        (stage_coverIdeal_map_le (J := J) (A := A) (φ := φ) (I := I) hI hiIj) hyIj_map
    have hyJj_mem : yJj ∈ K[j] := by
      have hyJj_map :
          yJj ∈ Ideal.map
            ((tensorBaseChangeMap (A := A) (φ := φ) (S := S) iJ j hiJj).toRingHom) K[iJ] := by
        exact Ideal.mem_map_of_mem _ hyJ_stage
      exact
        (stage_coverIdeal_map_le (J := J) (A := A) (φ := φ) (I := I) hI hiJj) hyJj_map
    simpa [yj] using Ideal.add_mem (K[j]) hyIj_mem hyJj_mem

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: every element of the mixed cover ideal `K∞` descends to a later
stage cover ideal `K[j]` above any prescribed lower bound. -/
lemma exists_stage_coverIdeal_element_above_of_mem_limit_coverIdeal
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {i₀ : Λ} {x : S∞}
    (hx : x ∈ K∞) :
    ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ xj : S[j],
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj = x ∧
        xj ∈ K[j] := by
  rcases Submodule.mem_sup.1 hx with ⟨xI, hxI, xJ, hxJ, rfl⟩
  have hIStage :
      ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ xj : S[j],
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj = xI ∧
          xj ∈ Ideal.map (algebraMap (A j) S[j]) (I j) :=
    exists_stage_mapped_limitIdeal_element_above
      (J := J) (A := A) (φ := φ) (I := I) hI hxI
  have hJStage :
      ∃ j : Λ, ∃ hij : i₀ ≤ j, ∃ xj : S[j],
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj = xJ ∧
          xj ∈ Ideal.map (algebraMap S S[j]) J :=
    exists_stage_fixed_coverIdeal_element_above_of_mem_fixedIdeal
      (J := J) (A := A) (φ := φ) (I := I) hxJ
  rcases hIStage with ⟨jI, hiI, yI, hyIeq, hyI⟩
  rcases hJStage with ⟨jJ, hiJ, yJ, hyJeq, hyJ⟩
  -- Synchronize the two descended summands at a common later stage and add them inside `K[j]`.
  simpa using
    (exists_common_stage_coverIdeal_sum_above
      (J := J) (A := A) (φ := φ) (I := I) hI hiI hiJ hyIeq hyJeq hyI hyJ)

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: the stage-to-limit tensor-base-change map commutes with tensoring
`sigmaP` on the left factor. -/
lemma tensorBaseChangeToLimit_comp_tensorProductMap
    {P : Type*} [CommRing P] [Algebra R P]
    (sigmaP : P →ₐ[R] S) (j : Λ) :
    ((tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j).toRingHom.comp
        ((Algebra.TensorProduct.map
            (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
            sigmaP (AlgHom.id R (A j))).toRingHom)) =
      (((Algebra.TensorProduct.map
            (R := R) (S := R) (A := P) (B := A∞) (C := S) (D := A∞)
            sigmaP (AlgHom.id R A∞)).toRingHom).comp
        (tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) j).toRingHom) := by
  -- Both composites apply `sigmaP` to the left tensor factor and the stage-to-limit map to the
  -- right tensor factor, so they agree on pure tensors and hence everywhere.
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro p a
    simp [tensorBaseChangeToLimit, Algebra.TensorProduct.map_tmul]
  · intro x y hx hy
    simp [hx, hy]

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: if two stage elements have the same image in the tensor direct
limit, then they become equal after passing to a later stage. -/
lemma tensorBaseChange_eventually_eq_of_equal_in_limit
    {i : Λ} {x y : S[i]}
    (hxy :
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) i x =
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) i y) :
    ∃ j : Λ, ∃ hij : i ≤ j,
      tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij x =
        tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij y := by
  let ρS := fun i j h ↦
    (tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j h).toRingHom
  have hzero :
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) i (x - y) = 0 := by
    -- Equality in the direct limit is reduced to a vanishing statement by subtraction.
    simpa [map_sub] using sub_eq_zero.mpr hxy
  rcases Ring.DirectLimit.of.zero_exact (G := fun i ↦ S[i]) (f' := ρS) hzero with
    ⟨j, hij, hj⟩
  refine ⟨j, hij, ?_⟩
  -- Rewrite the later-stage vanishing of `x - y` back into the required equality.
  exact sub_eq_zero.mp (by simpa [ρS, map_sub] using hj)

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: descend a finite span element in the limit-side cover relation to a
later stage above a prescribed lower bound. -/
lemma exists_stage_span_element_above_of_mem_limit_span
    {P : Type*} [CommRing P] [Algebra R P]
    (sigmaP : P →ₐ[R] S)
    {n : ℕ} {i i₀ : Λ}
    (gInf : Fin n → (P ⊗[R] A∞))
    (gi : Fin n → (P ⊗[R] A i))
    (hgi :
      ∀ a,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) i (gi a) = gInf a)
    {x : S∞}
    (hx :
      x ∈
        Ideal.span
          (Set.range
            (fun a ↦
              ((Algebra.TensorProduct.map
                  (R := R) (S := R) (A := P) (B := A∞) (C := S) (D := A∞)
                  sigmaP (AlgHom.id R A∞)).toRingHom) (gInf a)))) :
    ∃ j : Λ, ∃ hij₀ : i₀ ≤ j, ∃ hij : i ≤ j, ∃ xj : S[j],
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj = x ∧
        xj ∈
          Ideal.span
            (Set.range
              (fun a ↦
                ((Algebra.TensorProduct.map
                    (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
                    sigmaP (AlgHom.id R (A j))).toRingHom)
                  (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))) := by
  classical
  let sigmaInf : (P ⊗[R] A∞) →+* S∞ :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := A∞) (C := S) (D := A∞)
      sigmaP (AlgHom.id R A∞)).toRingHom
  rw [← Ideal.submodule_span_eq] at hx
  rcases (Submodule.mem_span_set'.mp hx) with ⟨m, coeff, generators, hsum⟩
  have hpre :
      ∀ k : Fin m, ∃ a : Fin n, sigmaInf (gInf a) = (generators k : S∞) := by
    intro k
    rcases (generators k).2 with ⟨a, haeq⟩
    exact ⟨a, haeq⟩
  choose idx hidx using hpre
  obtain ⟨iCoeff, coeffi, hcoeffi⟩ :=
    exists_common_stage_lifts_of_finite_limit_family
      (R := R) (S := S) (M := M) (A := A) (φ := φ) (fInf := coeff)
  rcases exists_ge_ge i₀ i with ⟨j₀, hi₀j₀, hij₀⟩
  rcases exists_ge_ge j₀ iCoeff with ⟨j, hj₀j, hiCoeffj⟩
  let hij : i ≤ j := le_trans hij₀ hj₀j
  let sigmaj : (P ⊗[R] A j) →+* S[j] :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
      sigmaP (AlgHom.id R (A j))).toRingHom
  let coeffj : Fin m → S[j] :=
    fun k ↦ tensorBaseChangeMap (A := A) (φ := φ) (S := S) iCoeff j hiCoeffj (coeffi k)
  let xj : S[j] :=
    ∑ k, coeffj k * sigmaj (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi (idx k)))
  have hcoeffj :
      ∀ k : Fin m,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj k) = coeff k := by
    intro k
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj k) =
          tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) iCoeff (coeffi k) := by
            exact
              tensorBaseChange_toLimit_comp_stageMap
                (A := A) (φ := φ) (S := S) iCoeff j hiCoeffj (coeffi k)
      _ = coeff k := hcoeffi k
  have hgenj :
      ∀ k : Fin m,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j
            (sigmaj (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi (idx k)))) =
          (generators k : S∞) := by
    intro k
    have hcomp :=
      tensorBaseChangeToLimit_comp_tensorProductMap
        (J := J) (A := A) (φ := φ) (I := I) (sigmaP := sigmaP) j
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j
          (sigmaj (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi (idx k)))) =
        sigmaInf
          (tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) j
            (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi (idx k)))) := by
            simpa [sigmaj, sigmaInf, RingHom.comp_apply] using
              congrArg
                (fun f : (P ⊗[R] A j) →+* S∞ ↦
                  f (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi (idx k))))
                hcomp
      _ = sigmaInf (gInf (idx k)) := by
            rw [tensorBaseChange_toLimit_comp_stageMap
              (A := A) (φ := φ) (S := P) i j hij (gi (idx k)), hgi]
      _ = (generators k : S∞) := hidx k
  refine ⟨j, le_trans hi₀j₀ hj₀j, hij, xj, ?_, ?_⟩
  · -- After descending the finitely many coefficients to the common stage `j`, the limit map
    -- reconstructs the original span element.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj =
          ∑ k,
            tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (coeffj k) *
              tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j
                (sigmaj
                  (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi (idx k)))) := by
              simp [xj, coeffj, map_mul]
      _ = ∑ k, coeff k * (generators k : S∞) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hcoeffj k, hgenj k]
      _ = x := by
            simpa [smul_eq_mul] using hsum
  · -- Each summand uses one of the transported generators, so the reconstructed stage element
    -- lies in the span of the whole transported family.
    unfold xj
    refine Ideal.sum_mem _ ?_
    intro k hk
    exact
      Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨idx k, rfl⟩)

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: descend the mixed cover relation through the explicit witness
`1 ∈ span + K∞`, keeping the fixed `J`-summand inside `K[j]`. -/
lemma exists_stage_one_mem_span_add_of_limit_cover
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {P : Type*} [CommRing P] [Algebra R P]
    (sigmaP : P →ₐ[R] S)
    {n : ℕ} {i : Λ}
    (gInf : Fin n → (P ⊗[R] A∞))
    (gi : Fin n → (P ⊗[R] A i))
    (hgi :
      ∀ a,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) i (gi a) = gInf a)
    (hOne :
      (1 : S∞) ∈
        Ideal.span
            (Set.range
              (fun a ↦
                ((Algebra.TensorProduct.map
                    (R := R) (S := R) (A := P) (B := A∞) (C := S) (D := A∞)
                    sigmaP (AlgHom.id R A∞)).toRingHom) (gInf a))) +
          K∞) :
    ∃ j : Λ, ∃ hij : i ≤ j,
      (1 : S[j]) ∈
        Ideal.span
            (Set.range
              (fun a ↦
                ((Algebra.TensorProduct.map
                    (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
                    sigmaP (AlgHom.id R (A j))).toRingHom)
                  (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))) +
          K[j] := by
  rcases Submodule.mem_sup.1 hOne with ⟨xSpan, hxSpan, xK, hxK, hEq⟩
  obtain ⟨jK, hijK, xKj, hxKj_eq, hxKj_mem⟩ :
      ∃ j : Λ, ∃ hij : i ≤ j, ∃ xj : S[j],
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xj = xK ∧
          xj ∈ K[j] :=
    exists_stage_coverIdeal_element_above_of_mem_limit_coverIdeal
      (J := J) (A := A) (φ := φ) (I := I) hI hxK
  obtain ⟨j, hjKj, hij, xSpanj, hxSpanj_eq, hxSpanj_mem⟩ :=
    exists_stage_span_element_above_of_mem_limit_span
      (J := J) (A := A) (φ := φ) (I := I) (sigmaP := sigmaP)
      (i₀ := jK) gInf gi hgi hxSpan
  let xKj' : S[j] :=
    tensorBaseChangeMap (A := A) (φ := φ) (S := S) jK j hjKj xKj
  have hxKj'_eq :
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xKj' = xK := by
    -- Transporting the descended `K∞`-term further to `j` does not change its limit image.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xKj' =
          tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) jK xKj := by
            exact
              tensorBaseChange_toLimit_comp_stageMap
                (A := A) (φ := φ) (S := S) jK j hjKj xKj
      _ = xK := hxKj_eq
  have hxKj'_mem : xKj' ∈ K[j] := by
    -- The previously descended `K[jK]` witness remains inside the mixed cover ideal after
    -- transporting it to the common stage `j`.
    have hxKj'_map :
        xKj' ∈
          Ideal.map
            ((tensorBaseChangeMap (A := A) (φ := φ) (S := S) jK j hjKj).toRingHom) K[jK] := by
      exact Ideal.mem_map_of_mem _ hxKj_mem
    exact
      (stage_coverIdeal_map_le (J := J) (A := A) (φ := φ) (I := I) hI hjKj) hxKj'_map
  let yj : S[j] := xSpanj + xKj'
  have hyj_mem :
      yj ∈
        Ideal.span
            (Set.range
              (fun a ↦
                ((Algebra.TensorProduct.map
                    (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
                    sigmaP (AlgHom.id R (A j))).toRingHom)
                  (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))) +
          K[j] := by
    -- Once the span and `K` witnesses live at the same stage, their sum lies in the mixed cover
    -- ideal there by construction.
    simpa [yj] using Ideal.add_mem
      (Ideal.span
        (Set.range
          (fun a ↦
            ((Algebra.TensorProduct.map
                (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
                sigmaP (AlgHom.id R (A j))).toRingHom)
              (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))))
      hxSpanj_mem hxKj'_mem
  have hyj_eq :
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j yj = 1 := by
    -- The reconstructed common-stage witness has the same limit image as the original equality
    -- `xSpan + xK = 1`.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j yj =
          tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xSpanj +
            tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j xKj' := by
              simp [yj]
      _ = xSpan + xK := by rw [hxSpanj_eq, hxKj'_eq]
      _ = 1 := hEq
  have hyj_eq' :
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j yj =
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := S) j (1 : S[j]) := by
    -- Rewrite the explicit unit equality into the form expected by the direct-limit exactness
    -- lemma.
    rw [hyj_eq, map_one]
  obtain ⟨k, hjk, hyk_eq⟩ :=
    tensorBaseChange_eventually_eq_of_equal_in_limit
      (J := J) (A := A) (φ := φ) (I := I) hyj_eq'
  let τS : S[j] →+* S[k] :=
    (tensorBaseChangeMap (A := A) (φ := φ) (S := S) j k hjk).toRingHom
  let τP : (P ⊗[R] A j) →+* (P ⊗[R] A k) :=
    (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk).toRingHom
  let σj : (P ⊗[R] A j) →+* S[j] :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
      sigmaP (AlgHom.id R (A j))).toRingHom
  let σk : (P ⊗[R] A k) →+* S[k] :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := A k) (C := S) (D := A k)
      sigmaP (AlgHom.id R (A k))).toRingHom
  let coverj : Ideal S[j] :=
    Ideal.span
      (Set.range
        (fun a ↦ σj (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))) +
      K[j]
  let coverk : Ideal S[k] :=
    Ideal.span
      (Set.range
        (fun a ↦
          σk
            (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i k (le_trans hij hjk) (gi a)))) +
      K[k]
  have hyj_cover : yj ∈ coverj := by
    -- Package the current-stage mixed-cover witness using the local abbreviation `coverj`.
    simpa [coverj] using hyj_mem
  have hσ :
      τS.comp σj = σk.comp τP := by
    -- Both composites act by `sigmaP` on the left tensor factor and the stage transition on the
    -- right tensor factor.
    ext x
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [τS, τP, σj, σk]
    | tmul p a =>
        simp [τS, τP, σj, σk, tensorBaseChangeMap, Algebra.TensorProduct.map_tmul]
    | add x y hx hy =>
        simp [hx, hy, τS, τP, σj, σk]
  have hmap_span_le :
      Ideal.map τS
          (Ideal.span
            (Set.range
              (fun a ↦ σj (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))))) ≤
        coverk := by
    -- The span generators push forward to the corresponding rebased generators at stage `k`.
    rw [Ideal.map_span]
    refine le_trans (Ideal.span_le.2 ?_) le_sup_left
    rintro _ ⟨a, rfl⟩
    have himage :
        τS (σj (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))) =
          σk (τP (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))) := by
      simpa [RingHom.comp_apply] using
        congrArg
          (fun f : (P ⊗[R] A j) →+* S[k] ↦
            f (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))
          hσ
    have htransport :
        τP (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)) =
          tensorBaseChangeMap (A := A) (φ := φ) (S := P) i k (le_trans hij hjk) (gi a) := by
      simpa [τP, tensorBaseChangeMap]
    rw [himage, htransport]
    exact Ideal.subset_span (Set.mem_range_self a)
  have hmap_coverj_le : Ideal.map τS coverj ≤ coverk := by
    -- Push the span and mixed-cover summands separately to the later stage.
    rw [coverj, Ideal.add_eq_sup, Ideal.map_sup]
    exact sup_le hmap_span_le
      (stage_coverIdeal_map_le (J := J) (A := A) (φ := φ) (I := I) hI hjk)
  have hyk_mem : τS yj ∈ coverk := by
    -- The common-stage witness remains inside the transported cover ideal at stage `k`.
    have hyk_map : τS yj ∈ Ideal.map τS coverj :=
      Ideal.mem_map_of_mem τS hyj_cover
    exact hmap_coverj_le hyk_map
  have hOnek : (1 : S[k]) ∈ coverk := by
    -- The direct-limit exactness step identifies the transported witness with `1`.
    simpa [τS] using (hyk_eq ▸ hyk_mem)
  refine ⟨k, le_trans hij hjk, ?_⟩
  simpa [coverk] using hOnek

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: once the explicit unit witness has been descended to a stage, the
mixed span-plus-cover ideal there is the top ideal. -/
lemma exists_stage_span_add_eq_top_of_limit_cover
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {P : Type*} [CommRing P] [Algebra R P]
    (sigmaP : P →ₐ[R] S)
    {n : ℕ} {i : Λ}
    (gInf : Fin n → (P ⊗[R] A∞))
    (gi : Fin n → (P ⊗[R] A i))
    (hgi :
      ∀ a,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) i (gi a) = gInf a)
    (hTop :
      Ideal.span
          (Set.range
            (fun a ↦
              ((Algebra.TensorProduct.map
                  (R := R) (S := R) (A := P) (B := A∞) (C := S) (D := A∞)
                  sigmaP (AlgHom.id R A∞)).toRingHom) (gInf a))) +
        K∞ = ⊤) :
    ∃ j : Λ, ∃ hij : i ≤ j,
      Ideal.span
          (Set.range
            (fun a ↦
              ((Algebra.TensorProduct.map
                  (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
                  sigmaP (AlgHom.id R (A j))).toRingHom)
                (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))) +
        K[j] = ⊤ := by
  -- First normalize the cover equality to the explicit unit witness used in the stage descent.
  have hOne :
      (1 : S∞) ∈
        Ideal.span
            (Set.range
              (fun a ↦
                ((Algebra.TensorProduct.map
                    (R := R) (S := R) (A := P) (B := A∞) (C := S) (D := A∞)
                    sigmaP (AlgHom.id R A∞)).toRingHom) (gInf a))) +
          K∞ :=
    one_mem_span_add_of_span_add_eq_top hTop
  -- After descending that witness, the stage ideal equality is just `Ideal.eq_top_iff_one`.
  obtain ⟨j, hij, hOnej⟩ :=
    exists_stage_one_mem_span_add_of_limit_cover
      (J := J) (A := A) (φ := φ) (I := I) hI sigmaP gInf gi hgi hOne
  refine ⟨j, hij, ?_⟩
  simpa [Ideal.eq_top_iff_one] using hOnej

omit [Module.FinitePresentation S M] in
/-- Helper for Lemma 15.19.4: the mixed cover ideal `K[i]` maps into `K[j]` along every stage
transition once the stage ideals are compatible. -/
/-- Helper for Lemma 15.19.4: once a mixed span-plus-cover relation is the unit ideal at one
stage, pushing it forward to any later stage keeps it equal to the unit ideal. -/
lemma stage_cover_top_persists_above
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    {P : Type*} [CommRing P] [Algebra R P]
    (sigmaP : P →ₐ[R] S)
    {n : ℕ} {j k : Λ} (hjk : j ≤ k)
    (gj : Fin n → (P ⊗[R] A j))
    (hTopj :
      Ideal.span
          (Set.range
            (fun a ↦
              ((Algebra.TensorProduct.map
                  (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
                  sigmaP (AlgHom.id R (A j))).toRingHom) (gj a))) +
        K[j] = ⊤) :
    Ideal.span
        (Set.range
          (fun a ↦
            ((Algebra.TensorProduct.map
                (R := R) (S := R) (A := P) (B := A k) (C := S) (D := A k)
                sigmaP (AlgHom.id R (A k))).toRingHom)
              (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk (gj a)))) +
      K[k] = ⊤ := by
  let τS : S[j] →+* S[k] :=
    (tensorBaseChangeMap (A := A) (φ := φ) (S := S) j k hjk).toRingHom
  let τP : (P ⊗[R] A j) →+* (P ⊗[R] A k) :=
    (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk).toRingHom
  let σj : (P ⊗[R] A j) →+* S[j] :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
      sigmaP (AlgHom.id R (A j))).toRingHom
  let σk : (P ⊗[R] A k) →+* S[k] :=
    (Algebra.TensorProduct.map
      (R := R) (S := R) (A := P) (B := A k) (C := S) (D := A k)
      sigmaP (AlgHom.id R (A k))).toRingHom
  let coverj : Ideal S[j] :=
    Ideal.span (Set.range (fun a ↦ σj (gj a))) + K[j]
  let coverk : Ideal S[k] :=
    Ideal.span (Set.range (fun a ↦ σk (τP (gj a)))) + K[k]
  have hOnej : (1 : S[j]) ∈ coverj := by
    -- Rewrite the top-ideal equality as the explicit unit witness used in the pushforward step.
    simpa [coverj, Ideal.eq_top_iff_one] using hTopj
  have hσ :
      τS.comp σj = σk.comp τP := by
    -- Both composites are the tensor-product map induced by `sigmaP` on the left factor and the
    -- stage transition `A j → A k` on the right factor.
    ext x
    induction x using TensorProduct.induction_on with
    | zero =>
        simp [τS, τP, σj, σk]
    | tmul p a =>
        simp [τS, τP, σj, σk, tensorBaseChangeMap, Algebra.TensorProduct.map_tmul]
    | add x y hx hy =>
        simp [hx, hy, τS, τP, σj, σk]
  have hmap_span_le :
      Ideal.map τS (Ideal.span (Set.range (fun a ↦ σj (gj a)))) ≤ coverk := by
    -- The generators of the span are pushed forward to the corresponding rebased generators.
    rw [Ideal.map_span]
    refine le_trans (Ideal.span_le.2 ?_) le_sup_left
    rintro _ ⟨a, rfl⟩
    have himage : τS (σj (gj a)) = σk (τP (gj a)) := by
      simpa [RingHom.comp_apply] using congrArg (fun f : (P ⊗[R] A j) →+* S[k] ↦ f (gj a)) hσ
    exact himage ▸ Ideal.subset_span (Set.mem_range_self a)
  have hmap_stageIdeal_le :
      Ideal.map τS (Ideal.map (algebraMap (A j) S[j]) (I j)) ≤ coverk := by
    -- The `I j`-summand is transported along the directed system and then inserted into `K[k]`.
    calc
      Ideal.map τS (Ideal.map (algebraMap (A j) S[j]) (I j)) =
          Ideal.map (algebraMap (A k) S[k]) (Ideal.map (φ j k hjk) (I j)) := by
            rw [Ideal.map_map, Ideal.map_map]
            congr 1
            ext x
            simp [τS, tensorBaseChangeMap]
      _ ≤ Ideal.map (algebraMap (A k) S[k]) (I k) := Ideal.map_mono (hI hjk)
      _ ≤ coverk := le_trans le_sup_left le_sup_right
  have hmap_fixedIdeal_le :
      Ideal.map τS (Ideal.map (algebraMap S S[j]) J) ≤ coverk := by
    -- The fixed `J`-summand is unchanged by further tensoring along the stage map.
    calc
      Ideal.map τS (Ideal.map (algebraMap S S[j]) J) =
          Ideal.map (algebraMap S S[k]) J := by
            rw [Ideal.map_map]
            congr 1
            ext s
            simp [τS, tensorBaseChangeMap]
      _ ≤ K[k] := le_sup_right
      _ ≤ coverk := le_sup_right
  have hmap_Kj_le : Ideal.map τS K[j] ≤ coverk := by
    -- Reuse the extracted transport lemma for the mixed cover ideal, then enlarge to `coverk`.
    exact le_trans
      (stage_coverIdeal_map_le (J := J) (A := A) (φ := φ) (I := I) hI hjk)
      le_sup_right
  have hmap_coverj_le : Ideal.map τS coverj ≤ coverk := by
    -- Push each summand of the mixed cover ideal separately.
    rw [coverj, Ideal.add_eq_sup, Ideal.map_sup]
    exact sup_le hmap_span_le hmap_Kj_le
  have hOnek : (1 : S[k]) ∈ coverk := by
    -- Apply the ideal inclusion to the pushed-forward unit witness.
    have hmem_map : τS (1 : S[j]) ∈ Ideal.map τS coverj :=
      Ideal.mem_map_of_mem τS hOnej
    exact hmap_coverj_le (by simpa [τS] using hmem_map)
  simpa [coverk, Ideal.eq_top_iff_one] using hOnek

-- Proof sketch: write `S` as a localization of a finitely presented `R`-algebra, descend the
-- finitely many basic opens covering the closed subset defined by `I∞` and `J` from the direct
-- limit to one stage, and then apply the finite-presentation flatness descent lemma stagewise to
-- conclude flatness on that entire closed subset.
/-- Lemma 15.19.4: if `R → S` is essentially of finite presentation, `M` is a finitely presented
`S`-module, and the source condition `(15.19.1.1)` holds after base change to the
direct limit of a directed system of `R`-algebras for the colimit ideal `I∞`, then the same
condition already holds after base change to some stage ring `A i` for the corresponding stage
ideal `I i`. -/
theorem exists_stage_zeroLocus_add_subset_flatOverBaseLocus_of_direct_limit_base_change
    (hS : RingHom.EssFinitePresentation (algebraMap R S))
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (φ i j hij) (I i) ≤ I j)
    (hflat_inf : V((K∞ : Set S∞)) ⊆ Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∃ i : Λ,
      V((K[i] : Set S[i])) ⊆ Module.flatOverBaseLocus (A i) S[i] M[i] := by
  classical
  -- First reduce the essentially finitely presented algebra to a finitely presented model plus
  -- localization data; this is the algebra side of the source-faithful setup.
  obtain ⟨P, _, _, hPfp, T, hPS, hloc, hPScomp⟩ :=
    exists_finitePresentation_localization_model (R := R) (S := S) hS
  letI : Module P M := Module.compHom M (algebraMap P S)
  letI : IsScalarTower P S M := IsScalarTower.of_compHom P S M
  obtain ⟨N, _, _, hNfp, f, eT, heT⟩ :=
    exists_finitePresentation_module_model_of_localization_data
      (R := R) (S := S) (M := M) (T := T)
  have hPScomp_apply : ∀ r : R, (algebraMap P S) ((algebraMap R P) r) = (algebraMap R S) r := by
    intro r
    exact (congrArg (fun g : R →+* S ↦ g r) hPScomp).symm
  -- The direct-limit ideal family already gives stagewise inclusions into the limit ideal.
  have hstageI : ∀ i : Λ, Ideal.map (ι∞ i) (I i) ≤ I∞ := by
    intro i
    exact stage_ideal_map_le_directLimitIdeal
      (A := A) (φ := φ) (I := I) i
  -- The limit-side hypothesis is also available in the primewise form needed for later descent.
  have hflat_inf_primewise :
      ∀ q : PrimeSpectrum S∞,
        q ∈ V((K∞ : Set S∞)) →
          Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞) :=
    limit_zeroLocus_add_subset_flatOverBaseLocus_iff
      (A := A) (φ := φ) (I := I) (J := J) (M := M) hflat_inf
  let sigmaP : P →ₐ[R] S :=
    { toRingHom := algebraMap P S
      commutes' := by
        intro r
        exact hPScomp_apply r }
  let sigmaInf : (P ⊗[R] A∞) →+* S∞ :=
    (Algebra.TensorProduct.map (R := R) (S := R) (A := P) (B := A∞) (C := S) (D := A∞)
      sigmaP (AlgHom.id R A∞)).toRingHom
  letI : Algebra.FinitePresentation A∞ (P ⊗[R] A∞) :=
    (finitePresentation_tensorBaseChange (R := R) (S := P) (M := N) A∞).1
  letI : Module.FinitePresentation (P ⊗[R] A∞) ((P ⊗[R] A∞) ⊗[P] N) :=
    (finitePresentation_tensorBaseChange (R := R) (S := P) (M := N) A∞).2
  have hcoverModel_of_eAtPrime :
      (∀ q : PrimeSpectrum S∞,
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmaInf q).asIdeal
            ((P ⊗[R] A∞) ⊗[P] N) ≃ₗ[A∞]
          LocalizedModule.AtPrime q.asIdeal M∞) →
        ∃ n : ℕ, ∃ gInf : Fin n → (P ⊗[R] A∞),
          (∀ a,
              (basicOpen (gInf a) : Set (PrimeSpectrum (P ⊗[R] A∞))) ⊆
                Module.flatOverBaseLocus A∞ (P ⊗[R] A∞) ((P ⊗[R] A∞) ⊗[P] N)) ∧
            Ideal.span (Set.range (fun a => sigmaInf (gInf a))) + K∞ = ⊤ := by
    intro eAtPrime
    -- Once the explicit at-prime comparison is available, the finite-cover extraction is now
    -- fully delegated to the generic localization-comparison helpers proved above.
    exact
      exists_finite_basicOpen_cover_of_limit_hypothesis_via_localization_comparison
        (A := A) (φ := φ) (I := I) (J := J) (M := M) sigmaInf eAtPrime hflat_inf
  have eAtPrimeInf :
      ∀ q : PrimeSpectrum S∞,
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmaInf q).asIdeal
            ((P ⊗[R] A∞) ⊗[P] N) ≃ₗ[A∞]
          LocalizedModule.AtPrime q.asIdeal M∞ := by
    intro q
    -- The repeated localization comparison is now isolated in the dedicated helper above.
    exact localizedModule_atPrime_equiv_of_localization_model
      (R := R) (S := S) (M := M) (sigmaP := sigmaP) (T := T) (f := f) eT heT
      (B := A∞) q
  obtain ⟨n, gInf, hbasicModelInf, hspanModelInf⟩ := hcoverModel_of_eAtPrime eAtPrimeInf
  obtain ⟨i, gi, hgi⟩ :=
    exists_common_stage_lifts_of_finite_limit_family
      (R := R) (S := P) (M := N) (A := A) (φ := φ) (fInf := gInf)
  have hflatAwayModelInf :
      ∀ a, Module.Flat A∞ (LocalizedModule.Away (gInf a) ((P ⊗[R] A∞) ⊗[P] N)) := by
    intro a
    -- Each model basic-open patch gives the corresponding away-localized flatness statement.
    exact flat_localizedAway_of_basicOpen_subset_flatOverBaseLocus
      (A := A∞) (T := P ⊗[R] A∞) (N := ((P ⊗[R] A∞) ⊗[P] N))
      (g := gInf a) (hbasicModelInf a)
  obtain ⟨j, hij, hflatAwayModelj⟩ :=
    exists_common_stage_flat_localizedAway_family_above
      (R := R) (S := P) (M := N) (A := A) (φ := φ) (I := I)
      (fInf := gInf) (i := i) (fi := gi) hgi hflatAwayModelInf
  have hbasicModelj :
      ∀ a,
        (basicOpen
            (tensorBaseChangeMap (R := R) (S := P) (M := N) (A := A) (φ := φ) i j hij (gi a)) :
          Set (PrimeSpectrum (P ⊗[R] A j))) ⊆
          Module.flatOverBaseLocus (A j) (P ⊗[R] A j) ((P ⊗[R] A j) ⊗[P] N) := by
    intro a
    -- Convert the descended away-flatness back into a stagewise model basic-open containment.
    exact basicOpen_subset_flatOverBaseLocus_of_flat_localizedAway
      (A := A j) (T := P ⊗[R] A j) (N := ((P ⊗[R] A j) ⊗[P] N))
      (g := tensorBaseChangeMap (R := R) (S := P) (M := N) (A := A) (φ := φ) i j hij (gi a))
      (hflatAwayModelj a)
  let sigmaj : (P ⊗[R] A j) →+* S[j] :=
    (Algebra.TensorProduct.map (R := R) (S := R) (A := P) (B := A j) (C := S) (D := A j)
      sigmaP (AlgHom.id R (A j))).toRingHom
  have eAtPrimej :
      ∀ q : PrimeSpectrum S[j],
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmaj q).asIdeal
            ((P ⊗[R] A j) ⊗[P] N) ≃ₗ[A j]
          LocalizedModule.AtPrime q.asIdeal M[j] := by
    intro q
    -- The same comparison helper specializes to the stage ring once the direct-limit stage is
    -- fixed.
    exact localizedModule_atPrime_equiv_of_localization_model
      (R := R) (S := S) (M := M) (sigmaP := sigmaP) (T := T) (f := f) eT heT
      (B := A j) q
  have hbasicTargetj :
      ∀ a,
        (basicOpen
            (sigmaj
              (tensorBaseChangeMap (R := R) (S := P) (M := N) (A := A) (φ := φ)
                i j hij (gi a))) : Set (PrimeSpectrum S[j])) ⊆
          Module.flatOverBaseLocus (A j) S[j] M[j] := by
    intro a
    -- Push each descended model patch forward to the target side using the primewise
    -- localization comparison at stage `j`.
    exact image_basicOpen_subset_flatOverBaseLocus_of_localization_comparison
      (A0 := A j) (P0 := P ⊗[R] A j) (S0 := S[j])
      (N0 := ((P ⊗[R] A j) ⊗[P] N)) (M0 := M[j])
      sigmaj eAtPrimej
      (g := tensorBaseChangeMap (R := R) (S := P) (M := N) (A := A) (φ := φ) i j hij (gi a))
      (hbasicModelj a)
  have hgj :
      ∀ a,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) j
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)) = gInf a := by
    intro a
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) j
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)) =
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) i (gi a) := by
          exact
            tensorBaseChange_toLimit_comp_stageMap
              (A := A) (φ := φ) (S := P) i j hij (gi a)
      _ = gInf a := hgi a
  have hspanStage_exists :
      ∃ k : Λ, ∃ hjk : j ≤ k,
        Ideal.span
            (Set.range
              (fun a ↦
                ((Algebra.TensorProduct.map
                    (R := R) (S := R) (A := P) (B := A k) (C := S) (D := A k)
                    sigmaP (AlgHom.id R (A k))).toRingHom)
                  (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
                    (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))))) +
          K[k] = ⊤ := by
    -- The mixed cover equality is now reduced to the dedicated stage-descent helper.
    exact
      exists_stage_span_add_eq_top_of_limit_cover
        (J := J) (A := A) (φ := φ) (I := I) hI sigmaP gInf
        (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))
        hgj hspanModelInf
  -- Route correction: the at-prime transport seam is now isolated in
  -- `localizedModule_atPrime_equiv_of_localization_model`, and the stagewise model flatness has
  -- already been descended and pushed forward to `Spec(S[j])`; the mixed cover relation has also
  -- been reduced to a dedicated later-stage existence statement `hspanStage_exists`.
  obtain ⟨k, hjk, hspank⟩ := hspanStage_exists
  have hgk :
      ∀ a,
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) k
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
            (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))) = gInf a := by
    intro a
    -- The synchronized stage-`k` lifts still represent the original limit generators.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) k
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
            (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))) =
        tensorBaseChangeToLimit (A := A) (φ := φ) (S := P) j
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)) := by
          exact
            tensorBaseChange_toLimit_comp_stageMap
              (A := A) (φ := φ) (S := P) j k hjk
              (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))
      _ = gInf a := hgj a
  obtain ⟨l, hkl, hflatAwayModell⟩ :=
    exists_common_stage_flat_localizedAway_family_above
      (R := R) (S := P) (M := N) (A := A) (φ := φ) (I := I)
      (fInf := gInf)
      (i := k)
      (fi := fun a ↦
        tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))
      hgk hflatAwayModelInf
  have hspanl :
      Ideal.span
          (Set.range
            (fun a ↦
              ((Algebra.TensorProduct.map
                  (R := R) (S := R) (A := P) (B := A l) (C := S) (D := A l)
                  sigmaP (AlgHom.id R (A l))).toRingHom)
                (tensorBaseChangeMap (A := A) (φ := φ) (S := P) k l hkl
                  (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
                    (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))))) +
        K[l] = ⊤ := by
    -- Push the stage-`k` mixed cover equality to the later stage `l` where the away-localized
    -- model flatness has also been synchronized.
    exact
      stage_cover_top_persists_above
        (J := J) (A := A) (φ := φ) (I := I) hI sigmaP hkl
        (fun a ↦
          tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
            (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))
        hspank
  have hbasicModell :
      ∀ a,
        (basicOpen
            (tensorBaseChangeMap (A := A) (φ := φ) (S := P) k l hkl
              (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
                (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))) :
          Set (PrimeSpectrum (P ⊗[R] A l))) ⊆
          Module.flatOverBaseLocus (A l) (P ⊗[R] A l) ((P ⊗[R] A l) ⊗[P] N) := by
    intro a
    -- Convert the synchronized away-flatness back into the corresponding basic-open inclusion on
    -- the later stage `l`.
    exact basicOpen_subset_flatOverBaseLocus_of_flat_localizedAway
      (A := A l) (T := P ⊗[R] A l) (N := ((P ⊗[R] A l) ⊗[P] N))
      (g := tensorBaseChangeMap (A := A) (φ := φ) (S := P) k l hkl
        (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))))
      (hflatAwayModell a)
  let sigmal : (P ⊗[R] A l) →+* S[l] :=
    (Algebra.TensorProduct.map (R := R) (S := R) (A := P) (B := A l) (C := S) (D := A l)
      sigmaP (AlgHom.id R (A l))).toRingHom
  have eAtPrimel :
      ∀ q : PrimeSpectrum S[l],
        LocalizedModule.AtPrime (PrimeSpectrum.comap sigmal q).asIdeal
            ((P ⊗[R] A l) ⊗[P] N) ≃ₗ[A l]
          LocalizedModule.AtPrime q.asIdeal M[l] := by
    intro q
    -- The localization-model comparison is uniform in the chosen base ring, so it specializes to
    -- the synchronized stage `l`.
    exact localizedModule_atPrime_equiv_of_localization_model
      (R := R) (S := S) (M := M) (sigmaP := sigmaP) (T := T) (f := f) eT heT
      (B := A l) q
  have hbasicTargetl :
      ∀ a,
        (basicOpen
            (sigmal
              (tensorBaseChangeMap (A := A) (φ := φ) (S := P) k l hkl
                (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
                  (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))))) :
          Set (PrimeSpectrum S[l])) ⊆
          Module.flatOverBaseLocus (A l) S[l] M[l] := by
    intro a
    -- Push the synchronized stage-`l` model patches forward to `Spec(S[l])` using the primewise
    -- localization comparison at the same stage.
    exact image_basicOpen_subset_flatOverBaseLocus_of_localization_comparison
      (A0 := A l) (P0 := P ⊗[R] A l) (S0 := S[l])
      (N0 := ((P ⊗[R] A l) ⊗[P] N)) (M0 := M[l])
      sigmal eAtPrimel
      (g := tensorBaseChangeMap (A := A) (φ := φ) (S := P) k l hkl
        (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a))))
      (hbasicModell a)
  -- The mixed cover relation and the target-side basic-open flatness family now live at the same
  -- later stage `l`, so the standard finite-cover argument closes the theorem.
  refine ⟨l, ?_⟩
  simpa using
    (zeroLocus_subset_flatOverBaseLocus_of_basicOpen_cover
      (A := A l) (T := S[l]) (N := M[l])
      (f := fun a ↦
        sigmal
          (tensorBaseChangeMap (A := A) (φ := φ) (S := P) k l hkl
            (tensorBaseChangeMap (A := A) (φ := φ) (S := P) j k hjk
              (tensorBaseChangeMap (A := A) (φ := φ) (S := P) i j hij (gi a)))))
      (J := K[l]) hbasicTargetl hspanl)
  let _ := hstageI
  let _ := hflat_inf_primewise
  let _ := hbasicTargetj

end

end DirectLimitDescent
