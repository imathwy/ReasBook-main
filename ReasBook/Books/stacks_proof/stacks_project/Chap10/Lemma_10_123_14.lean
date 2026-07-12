import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Topology

/-
Domain-style sampling:
- primary domain: quasi-finite finite-type algebras, integral closures, and the algebraic
  Zariski Main Theorem;
- sampled owner declarations:
  `Algebra.ZariskisMainProperty`,
  `Algebra.ZariskisMainProperty.of_finiteType`,
  `Algebra.ZariskisMainProperty.exists_fg_and_exists_notMem_and_awayMap_bijective`,
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`;
- best owner abstraction: the primewise local comparison data are owned upstream by
  `Algebra.ZariskisMainProperty`; the present lemma is the `source-facing` globalized integral
  closure statement built from those local owners together with the induced map on prime spectra;
- primitive data: an intermediate subalgebra `S'' : Subalgebra R S`, the inclusion
  `S'' ≤ integralClosure R S`, finiteness `Module.Finite R S''`, the open-embedding statement on
  `PrimeSpectrum`, and the away-map bijectivity clause for basic opens in the image;
- derived API to avoid as primitive wrappers: one-off conjunction packages for “finite subalgebra
  of the integral closure” and for the combined Zariski-main comparison property.

Source/core/bridge triage:
- `source-facing`: the global open-embedding and finite intermediate-subalgebra formulation of
  Lemma `10.123.14`;
- `core/canonical`: `Algebra.ZariskisMainProperty` for the local comparison ingredient;
- `bridge/view`: passing from the primewise owner theorem to the global spectrum/open-cover
  formulation used here.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: a finite supremum of module-finite subalgebras is
module-finite. -/
private theorem moduleFinite_finset_sup_subalgebra {ι : Type*} (s : Finset ι)
    (A : ι → Subalgebra R S) (hA : ∀ i ∈ s, Module.Finite R (A i)) :
    Module.Finite R (s.sup A : Subalgebra R S) := by
  classical
  -- Induct over the finite set, using finiteness of `⊥` and stability under finite suprema.
  revert hA
  refine Finset.induction_on s ?_ ?_
  · intro hA
    simpa using (Subalgebra.finite_bot : Module.Finite R (⊥ : Subalgebra R S))
  · intro a s has ih hA
    rw [Finset.sup_insert]
    exact @Subalgebra.finite_sup R S _ _ _ (A a) (s.sup A)
      (hA a (Finset.mem_insert_self a s))
      (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

/-- Helper for Chap10 Lemma 10 123 14: pointwise Zariski-main neighborhoods admit a finite
subalgebra cover of `Spec S`. -/
private theorem existsFiniteSubalgebraAwayCover :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Subalgebra R S) (r : ∀ i, A i),
      (∀ i, Module.Finite R (A i)) ∧
      (∀ i, A i ≤ integralClosure R S) ∧
      (∀ q : PrimeSpectrum S, ∃ i, (r i : S) ∉ q.asIdeal) ∧
      (∀ i, Function.Bijective (Localization.awayMap (A i).val.toRingHom (r i))) := by
  classical
  -- At each prime, unpack the algebraic Zariski-main theorem into a finite subalgebra and
  -- a principal open on which the away map is bijective.
  have hpoint : ∀ q : PrimeSpectrum S,
      ∃ A : Subalgebra R S, A.toSubmodule.FG ∧ A ≤ integralClosure R S ∧ ∃ r : A,
        r.1 ∉ q.asIdeal ∧ Function.Bijective (Localization.awayMap A.val.toRingHom r) := by
    intro q
    obtain ⟨A, hAfg, r, hrq, hrbij⟩ :=
      (Algebra.ZariskisMainProperty.of_finiteType (R := R) q.asIdeal)
        |>.exists_fg_and_exists_notMem_and_awayMap_bijective q.asIdeal
    have hAle : A ≤ integralClosure R S := by
      intro x hx
      rw [mem_integralClosure_iff]
      exact IsIntegral.of_mem_of_fg A hAfg x hx
    exact ⟨A, hAfg, hAle, r, hrq, hrbij⟩
  choose A hAfg hAle r hrq hrbij using hpoint
  let U : PrimeSpectrum S → Set (PrimeSpectrum S) :=
    fun q => PrimeSpectrum.basicOpen ((r q : A q) : S)
  have hUo : ∀ q, IsOpen (U q) := fun q => (PrimeSpectrum.basicOpen _).2
  have hcov : (Set.univ : Set (PrimeSpectrum S)) ⊆ ⋃ q, U q := by
    intro q hq
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    simpa [U, PrimeSpectrum.mem_basicOpen] using hrq q
  -- Quasi-compactness of the prime spectrum extracts finitely many of these principal opens.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hcov
  let ι := { q : PrimeSpectrum S // q ∈ t }
  refine ⟨ι, inferInstance, (fun i => A i.1), (fun i => r i.1), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (Module.Finite.iff_fg (N := (A i.1).toSubmodule)).2 (hAfg i.1)
  · intro i
    exact hAle i.1
  · intro q
    have hq : q ∈ ⋃ q₀, ⋃ (_ : q₀ ∈ t), U q₀ := ht (Set.mem_univ q)
    obtain ⟨q₀, hq₀⟩ := Set.mem_iUnion.mp hq
    obtain ⟨hq₀t, hqU⟩ := Set.mem_iUnion.mp hq₀
    refine ⟨⟨q₀, hq₀t⟩, ?_⟩
    simpa [U, PrimeSpectrum.mem_basicOpen] using hqU
  · intro i
    exact hrbij i.1

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: away-map bijectivity passes from a finite subalgebra to
any larger subalgebra of `S`. -/
private theorem awayMap_bijective_of_subalgebra_le
    {A B : Subalgebra R S} (hAB : A ≤ B) (r : A)
    (hr : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    Function.Bijective
      (Localization.awayMap B.val.toRingHom (Subalgebra.inclusion hAB r)) := by
  constructor
  · -- Injectivity is inherited from the inclusion into `S`.
    exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective
  · -- Surjectivity is the same clearing-denominators statement, with the numerator coerced to
    -- the larger subalgebra.
    have hsurj := hr.2
    rw [Localization.awayMap_surjective_iff] at hsurj ⊢
    intro s
    obtain ⟨b, m, hb⟩ := hsurj s
    refine ⟨Subalgebra.inclusion hAB b, m, ?_⟩
    simpa using hb

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: if `D(g)` is in the range of `Spec S → Spec A`, then
the chosen Zariski-main basic opens span after localizing `A` at `g`. -/
private theorem localizationAway_span_of_basicOpen_subset_range
    {A : Subalgebra R S} {ι : Type*} (r : ι → A) (g : A)
    (hcover : ∀ q : PrimeSpectrum S, ∃ i, (r i : S) ∉ q.asIdeal)
    (hg : ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
      Set.range (PrimeSpectrum.comap A.val.toRingHom))) :
    Ideal.span (Set.range (fun i => algebraMap A (Localization.Away g) (r i))) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  ext p
  simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion,
    Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  -- A prime of `A_g` contracts to a prime of `A` lying in `D(g)`.
  have hnotg : algebraMap A (Localization.Away g) g ∉ p.asIdeal := by
    intro hp
    obtain ⟨u, hu⟩ :=
      (IsLocalization.Away.algebraMap_isUnit g :
        IsUnit (algebraMap A (Localization.Away g) g))
    have hone : (1 : Localization.Away g) ∈ p.asIdeal := by
      rw [← Units.inv_mul u, hu]
      exact p.asIdeal.mul_mem_left _ hp
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)
  let pA : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A (Localization.Away g)) p
  have hpA : pA ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
    simpa [pA, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal] using hnotg
  -- The range hypothesis supplies a prime of `S` over this contraction, and the cover gives
  -- one chosen element avoiding it.
  obtain ⟨q, hq⟩ := hg hpA
  obtain ⟨i, hri⟩ := hcover q
  refine ⟨i, ?_⟩
  intro hp
  have hpAri : r i ∈ pA.asIdeal := by
    simpa [pA, PrimeSpectrum.comap_asIdeal] using hp
  have hqri : (r i : S) ∈ q.asIdeal := by
    rw [← hq] at hpAri
    simpa [PrimeSpectrum.comap_asIdeal] using hpAri
  exact hri hqri

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: a source principal open contained in the spectrum image
has bijective away map, provided the source is covered by principal opens with bijective away
maps. -/
private theorem subalgebra_awayMap_bijective_of_basicOpen_subset_range_of_cover
    {A : Subalgebra R S} {ι : Type*} (r : ι → A)
    (hcover : ∀ q : PrimeSpectrum S, ∃ i, (r i : S) ∉ q.asIdeal)
    (hbij : ∀ i, Function.Bijective (Localization.awayMap A.val.toRingHom (r i)))
    (g : A)
    (hg : ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
      Set.range (PrimeSpectrum.comap A.val.toRingHom))) :
    Function.Bijective (Localization.awayMap A.val.toRingHom g) := by
  -- Bijectivity is local on a source principal cover of `A_g`; the previous lemma provides
  -- the required spanning family.
  refine RingHom.Bijective.ofLocalizationSpan (Localization.awayMap A.val.toRingHom g)
    (Set.range (fun i => algebraMap A (Localization.Away g) (r i)))
    (localizationAway_span_of_basicOpen_subset_range r g hcover hg) ?_
  intro a
  obtain ⟨i, hi⟩ := a.2
  rw [← hi]
  constructor
  · have hginj : Function.Injective (Localization.awayMap A.val.toRingHom g) :=
      IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective
    rw [Localization.awayMap_injective_iff]
    intro x hx
    have hx0 : (Localization.awayMap A.val.toRingHom g) x =
        (Localization.awayMap A.val.toRingHom g) 0 := by
      rw [map_zero]
      exact hx
    have hxzero : x = 0 := hginj hx0
    have hxpow : (algebraMap A (Localization.Away g) (r i)) ^ 0 * x = 0 := by
      simpa [hxzero]
    exact ⟨0, hxpow⟩
  · -- The twice-localized map at `g` and `rᵢ` is surjective because it is the localization at
    -- `g * rᵢ`, and bijectivity at `rᵢ` persists after further localization.
    have hprod : Function.Bijective (Localization.awayMap A.val.toRingHom (g * r i)) := by
      exact Localization.awayMap_bijective_of_dvd A.val.toRingHom
        ⟨g, mul_comm g (r i)⟩ (hbij i)
    simpa using Localization.awayMap_awayMap_surjective A.val.toRingHom g (r i) hprod.2

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: a continuous map is an open embedding when its
restrictions over target opens covering its range are open embeddings. -/
private theorem isOpenEmbedding_of_range_subset_iUnion_and_restrictPreimage
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (U : ι → TopologicalSpace.Opens Y) (hf : Continuous f)
    (hrange : Set.range f ⊆ ⋃ i, (U i : Set Y))
    (hlocal : ∀ i, IsOpenEmbedding ((U i : Set Y).restrictPreimage f)) :
    IsOpenEmbedding f := by
  -- The local embeddings separate points because every image point lies in one chart.
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap hf ?_ ?_
  · intro x y hxy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hrange ⟨x, rfl⟩)
    have hyi : f y ∈ (U i : Set Y) := by
      simpa [hxy.symm] using hxi
    have hsub :
        ((U i : Set Y).restrictPreimage f) ⟨x, hxi⟩ =
          ((U i : Set Y).restrictPreimage f) ⟨y, hyi⟩ := by
      ext
      exact hxy
    exact congrArg Subtype.val ((hlocal i).injective hsub)
  · intro V hV
    -- The image of an open set is the union of its images inside the local target charts.
    have himage : f '' V =
        ⋃ i, Subtype.val ''
          (((U i : Set Y).restrictPreimage f) '' (Subtype.val ⁻¹' V)) := by
      ext y
      constructor
      · rintro ⟨x, hxV, rfl⟩
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hrange ⟨x, rfl⟩)
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        refine ⟨⟨f x, hxi⟩, ?_, rfl⟩
        refine ⟨⟨x, hxi⟩, ?_, rfl⟩
        exact hxV
      · intro hy
        obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
        obtain ⟨yU, hyU, rfl⟩ := hyi
        obtain ⟨xU, hxV, hmap⟩ := hyU
        refine ⟨xU.1, hxV, ?_⟩
        exact congrArg Subtype.val hmap
    rw [himage]
    refine isOpen_iUnion ?_
    intro i
    exact (U i).2.isOpenEmbedding_subtypeVal.isOpenMap _
      ((hlocal i).isOpenMap _ (hV.preimage continuous_subtype_val))

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: the preimage of a principal open under a spectrum
comap is the corresponding principal open. -/
private theorem primeSpectrum_basicOpen_preimage_comap
    {P Q : Type*} [CommRing P] [CommRing Q] (φ : P →+* Q) (r : P) :
    (PrimeSpectrum.basicOpen (φ r) : Set (PrimeSpectrum Q)) =
      (PrimeSpectrum.comap φ) ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum P)) := by
  -- This is the definitional computation behind `PrimeSpectrum.comap_basicOpen`.
  rfl

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: the localization-away comparison map commutes with
the two algebra maps from the original rings. -/
private theorem awayMap_comp_algebraMap
    {P Q : Type*} [CommRing P] [CommRing Q] (φ : P →+* Q) (r : P) :
    (Localization.awayMap φ r).comp (algebraMap P (Localization.Away r)) =
      (algebraMap Q (Localization.Away (φ r))).comp φ := by
  -- Reduce the away map to the universal localization map and use its source computation.
  rw [Localization.awayMap]
  have hy : Submonoid.powers r ≤ Submonoid.comap φ (Submonoid.powers (φ r)) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simp
  exact IsLocalization.map_comp (Q := Localization.Away (φ r)) (g := φ)
    (T := Submonoid.powers (φ r)) hy

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: a bijective localization-away map identifies the
restricted spectrum map over the corresponding principal open with an open embedding. -/
private theorem primeSpectrum_restrictPreimage_basicOpen_isOpenEmbedding_of_awayMap_bijective
    {P Q : Type*} [CommRing P] [CommRing Q] (φ : P →+* Q) (r : P)
    (hbij : Function.Bijective (Localization.awayMap φ r)) :
    IsOpenEmbedding ((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum P)).restrictPreimage
      (PrimeSpectrum.comap φ)) := by
  -- Compare both principal opens with their localization charts.
  let eTarget : PrimeSpectrum (Localization.Away r) ≃ₜ
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum P)) :=
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away r) r).1.toHomeomorph.trans
      (Homeomorph.setCongr
        (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r))
  let eSource : PrimeSpectrum (Localization.Away (φ r)) ≃ₜ
      ((PrimeSpectrum.comap φ) ⁻¹' (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum P))) :=
    ((PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away (φ r)) (φ r)).1
      |>.toHomeomorph.trans
        (Homeomorph.setCongr
          (PrimeSpectrum.localization_away_comap_range (Localization.Away (φ r)) (φ r)))).trans
      (Homeomorph.setCongr (primeSpectrum_basicOpen_preimage_comap φ r))
  have hchart :
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum P)).restrictPreimage
          (PrimeSpectrum.comap φ) ∘ eSource =
        eTarget ∘ PrimeSpectrum.comap (Localization.awayMap φ r) := by
    -- The square of localization charts commutes by functoriality of `awayMap`.
    funext x
    dsimp only [Function.comp_apply]
    apply Subtype.ext
    have hleft : ↑((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum P)).restrictPreimage
        (PrimeSpectrum.comap φ) (eSource x)) =
        PrimeSpectrum.comap φ
          (PrimeSpectrum.comap (algebraMap Q (Localization.Away (φ r))) x) := by
      dsimp only [eSource]
      rfl
    have hright : ↑(eTarget (PrimeSpectrum.comap (Localization.awayMap φ r) x)) =
        PrimeSpectrum.comap (algebraMap P (Localization.Away r))
          (PrimeSpectrum.comap (Localization.awayMap φ r) x) := by
      dsimp only [eTarget]
      rfl
    rw [hleft, hright]
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
    rw [awayMap_comp_algebraMap]
  have hcomp : IsOpenEmbedding
      ((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum P)).restrictPreimage
          (PrimeSpectrum.comap φ) ∘ eSource) := by
    -- After charting, the restricted map is a homeomorphism followed by an open chart.
    rw [hchart]
    exact eTarget.isOpenEmbedding.comp
      (PrimeSpectrum.isHomeomorph_comap_of_bijective hbij).isOpenEmbedding
  -- Cancel the source chart homeomorphism to recover the original restricted map.
  simpa [Function.comp_def] using hcomp.comp eSource.symm.isOpenEmbedding

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: a source cover by principal opens gives the range
containment needed for target-side gluing. -/
private theorem primeSpectrum_comap_range_subset_iUnion_basicOpen_of_source_cover
    {A : Subalgebra R S} {ι : Type*} (r : ι → A)
    (hcover : ∀ q : PrimeSpectrum S, ∃ i, (r i : S) ∉ q.asIdeal) :
    Set.range (PrimeSpectrum.comap A.val.toRingHom) ⊆
      ⋃ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum A)) := by
  -- A point in the image comes from a prime of `S`, where the given cover supplies a chart.
  rintro _ ⟨q, rfl⟩
  obtain ⟨i, hri⟩ := hcover q
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  simpa [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal] using hri

omit [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] in
/-- Helper for Chap10 Lemma 10 123 14: a principal-open source cover with bijective away maps
gives an open embedding on prime spectra. -/
private theorem subalgebra_primeSpectrum_comap_isOpenEmbedding_of_cover
    {A : Subalgebra R S} {ι : Type*} (r : ι → A)
    (hcover : ∀ q : PrimeSpectrum S, ∃ i, (r i : S) ∉ q.asIdeal)
    (hbij : ∀ i, Function.Bijective (Localization.awayMap A.val.toRingHom (r i))) :
    IsOpenEmbedding (PrimeSpectrum.comap A.val.toRingHom) := by
  -- Glue the local principal-open charts over the open subset containing the image.
  refine isOpenEmbedding_of_range_subset_iUnion_and_restrictPreimage
    (fun i => PrimeSpectrum.basicOpen (r i))
    (PrimeSpectrum.continuous_comap A.val.toRingHom)
    (primeSpectrum_comap_range_subset_iUnion_basicOpen_of_source_cover r hcover) ?_
  intro i
  exact primeSpectrum_restrictPreimage_basicOpen_isOpenEmbedding_of_awayMap_bijective
    A.val.toRingHom (r i) (hbij i)

/-- Chap10 Lemma 10 123 14: if `S' = integralClosure R S` and `R → S` is finite type and
quasi-finite, then the induced map `Spec(S) → Spec(S')` is a homeomorphism onto an open subset,
i.e. an open embedding. This is part (1) of Lemma 10.123.14. -/
-- Proof sketch: apply Zariski's Main Theorem pointwise to each prime of `S` to obtain basic open
-- neighborhoods on which `Spec(S) → Spec(S')` is identified with the spectrum map of a bijective
-- localization-away map. Quasi-compactness of `Spec(S)` then lets one glue these local
-- identifications into a global open embedding.
@[stacks 00QB]
theorem primeSpectrum_comap_integralClosure_isOpenEmbedding :
    IsOpenEmbedding (PrimeSpectrum.comap (integralClosure R S).val.toRingHom) := by
  -- Use the finite ZMT cover, transporting each local bijectivity statement to the full
  -- integral closure, then invoke the remaining open-embedding gluing criterion.
  obtain ⟨ι, hι, A, r, hfin, hle, hcover, hbij⟩ := existsFiniteSubalgebraAwayCover (R := R) (S := S)
  letI : Fintype ι := hι
  let r' : ι → integralClosure R S := fun i => ⟨(r i : S), hle i (r i).2⟩
  have hcover' : ∀ q : PrimeSpectrum S, ∃ i, (r' i : S) ∉ q.asIdeal := by
    simpa [r'] using hcover
  have hbij' :
      ∀ i, Function.Bijective
        (Localization.awayMap (integralClosure R S).val.toRingHom (r' i)) := by
    intro i
    exact awayMap_bijective_of_subalgebra_le (hle i) (r i) (hbij i)
  exact subalgebra_primeSpectrum_comap_isOpenEmbedding_of_cover r' hcover' hbij'

/-- Lemma 10.123.14 (2): if `g ∈ S' = integralClosure R S` and the basic open `D(g)` of
`Spec(S')` is contained in the image of `Spec(S) → Spec(S')`, then the canonical localization map
`S'_g → S_g` is bijective, equivalently `S'_g ≅ S_g`. -/
-- Proof sketch: cover the image of `Spec(S) → Spec(S')` by finitely many principal opens coming
-- from the pointwise Zariski-main theorem. Over each overlap with `D(g)` the away map is
-- bijective; apply the standard local-on-a-principal-cover criterion to descend bijectivity to the
-- away map at `g`.
@[stacks 00QB]
theorem awayMap_bijective_of_basicOpen_subset_range_integralClosure
    (g : integralClosure R S)
    (hg :
      ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (integralClosure R S))) ⊆
        Set.range (PrimeSpectrum.comap (integralClosure R S).val.toRingHom))) :
    Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom g) := by
  -- Reuse the same finite cover, now applying the algebraic source-local bijectivity criterion
  -- after localizing the integral closure at `g`.
  obtain ⟨ι, hι, A, r, hfin, hle, hcover, hbij⟩ := existsFiniteSubalgebraAwayCover (R := R) (S := S)
  letI : Fintype ι := hι
  let r' : ι → integralClosure R S := fun i => ⟨(r i : S), hle i (r i).2⟩
  have hcover' : ∀ q : PrimeSpectrum S, ∃ i, (r' i : S) ∉ q.asIdeal := by
    simpa [r'] using hcover
  have hbij' :
      ∀ i, Function.Bijective
        (Localization.awayMap (integralClosure R S).val.toRingHom (r' i)) := by
    intro i
    exact awayMap_bijective_of_subalgebra_le (hle i) (r i) (hbij i)
  exact subalgebra_awayMap_bijective_of_basicOpen_subset_range_of_cover r' hcover' hbij' g hg

/-- Lemma 10.123.14 (3): there exists a finite `R`-subalgebra `S''` of the integral closure
`S' = integralClosure R S` such that the induced map `Spec(S) → Spec(S'')` is an open embedding,
and whenever a basic open `D(g)` of `Spec(S'')` is contained in its image, the canonical
localization map `S''_g → S_g` is bijective. -/
-- Proof sketch: choose finitely many elements of the integral closure whose principal opens cover
-- `Spec(S)` and on which the away maps to `S` are bijective. Generate an `R`-subalgebra of the
-- integral closure by these elements together with finitely many auxiliary generators for the
-- corresponding localized rings; this subalgebra is module-finite over `R` and inherits the two
-- local properties from the chosen finite cover.
@[stacks 00QB]
theorem exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties :
    ∃ S'' : Subalgebra R S,
      S'' ≤ integralClosure R S ∧
      Module.Finite R S'' ∧
      IsOpenEmbedding (PrimeSpectrum.comap S''.val.toRingHom) ∧
      ∀ g : S'',
        ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S'')) ⊆
          Set.range (PrimeSpectrum.comap S''.val.toRingHom)) →
          Function.Bijective (Localization.awayMap S''.val.toRingHom g) := by
  classical
  -- Take the finite supremum of the finite local subalgebras from the ZMT cover.
  obtain ⟨ι, hι, A, r, hfin, hle, hcover, hbij⟩ := existsFiniteSubalgebraAwayCover (R := R) (S := S)
  letI : Fintype ι := hι
  let S'' : Subalgebra R S := Finset.univ.sup A
  have hS''le : S'' ≤ integralClosure R S := by
    dsimp [S'']
    exact (Finset.sup_le_iff).2 fun i hi => hle i
  have hS''finite : Module.Finite R S'' := by
    dsimp [S'']
    exact moduleFinite_finset_sup_subalgebra (Finset.univ : Finset ι) A
      (fun i hi => hfin i)
  let r'' : ι → S'' := fun i =>
    ⟨(r i : S), (Finset.le_sup (s := Finset.univ) (f := A) (Finset.mem_univ i)) (r i).2⟩
  have hcover'' : ∀ q : PrimeSpectrum S, ∃ i, (r'' i : S) ∉ q.asIdeal := by
    simpa [r''] using hcover
  have hbij'' :
      ∀ i, Function.Bijective (Localization.awayMap S''.val.toRingHom (r'' i)) := by
    intro i
    exact awayMap_bijective_of_subalgebra_le
      (Finset.le_sup (s := Finset.univ) (f := A) (Finset.mem_univ i)) (r i) (hbij i)
  refine ⟨S'', hS''le, hS''finite, ?_, ?_⟩
  · -- The open embedding follows from the same principal-open gluing criterion for the finite
    -- supremum subalgebra.
    exact subalgebra_primeSpectrum_comap_isOpenEmbedding_of_cover r'' hcover'' hbij''
  · intro g hg
    exact subalgebra_awayMap_bijective_of_basicOpen_subset_range_of_cover r'' hcover'' hbij'' g hg

end
