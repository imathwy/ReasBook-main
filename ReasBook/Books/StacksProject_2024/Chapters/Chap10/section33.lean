import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_33_1 (from Chap10) -/
noncomputable section

universe u

section

open PrimeSpectrum

variable {R : Type u} [CommRing R] (S : Submonoid R)

-- Semantic search tool unavailable in this environment; local API checks used
-- `PrimeSpectrum.comap`, `PrimeSpectrum.localization_comap_range`, and nearby quotient/localization
-- precedent in `Lemma_10_33_2` and `Definition_10_54_1`.

/-- Helper for Lemma 10.33.1: the closed image hypothesis identifies the image of
`Spec(S⁻¹R) → Spec(R)` with the zero locus of the kernel of the localization map. -/
lemma range_comap_eq_zeroLocus_kernel_of_isClosed
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
      PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R (Localization S))) := by
  -- The closed image already equals its closure, and the closure is the zero locus of the kernel.
  simpa [hclosed.closure_eq] using
    (PrimeSpectrum.closure_range_comap (f := algebraMap R (Localization S)))

/-- Helper for Lemma 10.33.1: every element of the multiplicative set becomes a unit in the
quotient by the kernel of the localization map. -/
lemma isUnit_quotient_mk_of_mem_submonoid
    (hzero : Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
      PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R (Localization S)))) (s : S) :
    IsUnit (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization S))) s) := by
  let I : Ideal R := RingHom.ker (algebraMap R (Localization S))
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  by_contra hs
  -- A nonunit in the quotient lies in some maximal ideal of the quotient ring.
  have hs_nonunit : q s ∈ nonunits (R ⧸ I) := by
    exact mem_nonunits_iff.mpr hs
  obtain ⟨J, hJmax, hsJ⟩ := exists_max_ideal_of_mem_nonunits hs_nonunit
  let x : PrimeSpectrum (R ⧸ I) := ⟨J, hJmax.isPrime⟩
  have hx_zero : PrimeSpectrum.comap q x ∈ PrimeSpectrum.zeroLocus I := by
    rw [PrimeSpectrum.mem_zeroLocus]
    simpa [I, q] using (Ideal.ker_le_comap q : RingHom.ker q ≤ Ideal.comap q x.asIdeal)
  have hx_range :
      PrimeSpectrum.comap q x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) := by
    rw [hzero]
    simpa [I] using hx_zero
  have hrange :
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))) =
        { p : PrimeSpectrum R | Disjoint (S : Set R) p.asIdeal } :=
    PrimeSpectrum.localization_comap_range (S := Localization S) (M := S)
  have hdisjoint :
      Disjoint (S : Set R) (PrimeSpectrum.comap q x).asIdeal := by
    rw [hrange] at hx_range
    exact hx_range
  have hs_mem : (s : R) ∈ (PrimeSpectrum.comap q x).asIdeal := by
    change q s ∈ x.asIdeal
    exact hsJ
  exact hdisjoint.le_bot ⟨s.2, hs_mem⟩

/-- Helper for Lemma 10.33.1: the quotient by the kernel of the localization map surjects onto
the localization. -/
lemma kernel_quotient_kerLift_surjective_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Function.Surjective
      (RingHom.kerLift (algebraMap R (Localization S)) :
        R ⧸ RingHom.ker (algebraMap R (Localization S)) →+* Localization S) := by
  let I : Ideal R := RingHom.ker (algebraMap R (Localization S))
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  let g : R ⧸ I →+* Localization S := RingHom.kerLift (algebraMap R (Localization S))
  have hzero := range_comap_eq_zeroLocus_kernel_of_isClosed (R := R) (S := S) hclosed
  let h : Localization S →+* R ⧸ I :=
    IsLocalization.lift
      (M := S)
      (S := Localization S)
      (g := q)
      (fun s ↦ isUnit_quotient_mk_of_mem_submonoid (R := R) (S := S) hzero s)
  have hcomp : h.comp (algebraMap R (Localization S)) = q := by
    -- The lift is the unique map extending the quotient map on the base ring.
    simpa [h] using
      (IsLocalization.lift_comp
        (M := S)
        (S := Localization S)
        (g := q)
        (hg := fun s ↦ isUnit_quotient_mk_of_mem_submonoid (R := R) (S := S) hzero s))
  have hright : g.comp h = RingHom.id (Localization S) := by
    -- It suffices to check the composite on the image of `R`.
    apply IsLocalization.ringHom_ext (M := S)
    ext r
    have hcomp_apply := congrArg (fun k : R →+* R ⧸ I => k r) hcomp
    calc
      g (h (algebraMap R (Localization S) r))
          = g (q r) := by
              exact congrArg g hcomp_apply
      _ = algebraMap R (Localization S) r := by
            exact RingHom.kerLift_mk (f := algebraMap R (Localization S)) r
  intro z
  -- The right inverse produced by the localization lift gives surjectivity.
  refine ⟨h z, ?_⟩
  simpa [RingHom.comp_apply] using congrArg (fun k : Localization S →+* Localization S => k z) hright

/-- Helper for Lemma 10.33.1: the quotient by the kernel of the localization map is isomorphic to
the localization. -/
theorem kernel_quotient_ringEquiv_localization_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Nonempty ((R ⧸ RingHom.ker (algebraMap R (Localization S))) ≃+* Localization S) := by
  -- The kernel lift is injective in general and surjective under the closed-image hypothesis.
  exact ⟨RingEquiv.ofBijective
    (RingHom.kerLift (algebraMap R (Localization S)))
    ⟨RingHom.kerLift_injective (f := algebraMap R (Localization S)),
      kernel_quotient_kerLift_surjective_of_isClosed_range_comap (R := R) (S := S) hclosed⟩⟩

/-- Lemma 10.33.1: if the image of `Spec(S⁻¹R) → Spec(R)` is closed, then `S⁻¹R` is isomorphic to
the quotient `R / I` for some ideal `I ⊆ R`. -/
theorem exists_ideal_ringEquiv_quotient_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    ∃ I : Ideal R, Nonempty (Localization S ≃+* R ⧸ I) := by
  -- Use the kernel of the localization map as the quotient ideal.
  refine ⟨RingHom.ker (algebraMap R (Localization S)), ?_⟩
  obtain ⟨e⟩ :=
    kernel_quotient_ringEquiv_localization_of_isClosed_range_comap (R := R) (S := S) hclosed
  exact ⟨e.symm⟩

/-- Closed image of `Spec(S⁻¹R) → Spec(R)` forces the localization map `R → S⁻¹R` to be
surjective. -/
theorem algebraMap_surjective_of_isClosed_range_comap
    (hclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R (Localization S))))) :
    Function.Surjective (algebraMap R (Localization S)) := by
  let I : Ideal R := RingHom.ker (algebraMap R (Localization S))
  have hsurj :
      Function.Surjective
        (RingHom.kerLift (algebraMap R (Localization S)) : R ⧸ I →+* Localization S) :=
    kernel_quotient_kerLift_surjective_of_isClosed_range_comap (R := R) (S := S) hclosed
  intro z
  -- First lift `z` to the kernel quotient, then choose a representative in `R`.
  obtain ⟨y, hy⟩ := hsurj z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨r, ?_⟩
  simpa [I] using hy

end

/-! ### Lemma_10_33_2 (from Chap10) -/
/-
Domain triage:
* primary domain: localization images on prime spectra and idempotent splittings of commutative
  rings;
* sampled owner declarations:
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `algebraMap_surjective_of_isClosed_range_comap`,
  `IsLocalization.away_of_isIdempotentElem`,
  `AlgEquiv.prodQuotientOfIsIdempotentElem`;
* best owner abstraction: the image of `Spec(S⁻¹R) → Spec(R)` as a clopen/basic-open subset,
  classified by an idempotent and then converted to a canonical product decomposition;
* layer: `source-facing`, since Lemma 10.33.2 adds the textbook closed-image-to-product statement
  rather than merely recalling one owner theorem.

Primitive-vs-derived split:
* primitive data: the submonoid `S`, the closedness of the image of `Spec(S⁻¹R) → Spec(R)`, and
  the auxiliary hypothesis that `Spec(R)` is Noetherian or `S` is finitely generated;
* derived API: the unique idempotent cutting out that image, the induced `Away e` comparison, and
  the product decomposition `R ≃ Localization S × R/(e)`.
-/

universe u

open PrimeSpectrum TopologicalSpace Topology
open Algebra.HasGoingDown

section

variable {R : Type u} [CommRing R]

private theorem isConstructible_of_isClosed [NoetherianSpace (PrimeSpectrum R)]
    {s : Set (PrimeSpectrum R)} (hs : IsClosed s) : IsConstructible s := by
  have hs' : IsConstructible sᶜ := (NoetherianSpace.isCompact sᶜ).isConstructible hs.isOpen_compl
  simpa using hs'.compl

private theorem disjoint_closure_finset_iff {s : Finset R} (p : Ideal R) [hp : p.IsPrime] :
    Disjoint ((Submonoid.closure (s : Set R) : Submonoid R) : Set R) p ↔ ∀ x ∈ s, x ∉ p := by
  constructor
  · intro h x hx hx'
    exact Set.disjoint_left.mp h (Submonoid.subset_closure (by simpa using hx)) hx'
  · intro h
    rw [Set.disjoint_left]
    intro x hx hx'
    induction hx using Submonoid.closure_induction with
    | mem y hy => exact h y (by simpa using hy) hx'
    | one =>
        exact ((Ideal.ne_top_iff_one p).mp (Ideal.IsPrime.ne_top hp)) hx'
    | mul x y hx hy ihx ihy =>
        exact (Ideal.IsPrime.mem_or_mem hp hx').elim ihx ihy

private theorem isOpen_range_comap_of_fg (S : Submonoid R) (hS : S.FG) :
    IsOpen (Set.range (comap (algebraMap R (Localization S)))) := by
  rcases hS with ⟨s, rfl⟩
  rw [PrimeSpectrum.localization_comap_range (Localization (Submonoid.closure (s : Set R)))
    (Submonoid.closure (s : Set R))]
  have hEq :
      ({p | Disjoint ((Submonoid.closure (s : Set R) : Submonoid R) : Set R) p.asIdeal} :
        Set (PrimeSpectrum R)) = (basicOpen (s.prod id) : Set (PrimeSpectrum R)) := by
    ext p
    change Disjoint ((Submonoid.closure (s : Set R) : Submonoid R) : Set R) p.asIdeal ↔
      s.prod id ∉ p.asIdeal
    rw [disjoint_closure_finset_iff]
    simp [Ideal.IsPrime.prod_mem_iff_exists_mem]
  rw [hEq]
  exact isOpen_basicOpen

end

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)

local notation "imageSet" => Set.range (comap (algebraMap R (Localization S)))

private theorem isClopen_range_comap_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    IsClopen imageSet := by
  have hgeneralizing : StableUnderGeneralization imageSet := by
    simpa using
      (iff_generalizingMap_primeSpectrumComap.mp
        (inferInstance : Algebra.HasGoingDown R (Localization S))).stableUnderGeneralization_range
  rcases h with hSpec | hfg
  · letI := hSpec
    exact ⟨hclosed,
      PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible hgeneralizing
        (isConstructible_of_isClosed hclosed)⟩
  · exact ⟨hclosed, by simpa using isOpen_range_comap_of_fg S hfg⟩

/-- Lemma 10.33.2 (1): if the image of `Spec(S⁻¹R) → Spec(R)` is closed and either `Spec(R)` is a
Noetherian topological space or `S` is finitely generated, then this image is the basic open
`D(e)` of a unique idempotent `e`. -/
theorem existsUnique_idempotent_basicOpen_eq_range_comap_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃! e : R, IsIdempotentElem e ∧ imageSet = basicOpen e := by
  exact
    existsUnique_idempotent_basicOpen_eq_of_isClopen
      (isClopen_range_comap_of_isClosed_range_comap S hclosed h)

/-- Lemma 10.33.2 (2): if the image of `Spec(S⁻¹R) → Spec(R)` is closed and either `Spec(R)` is a
Noetherian topological space or `S` is finitely generated, then there is an idempotent `e ∈ R`
such that `R` splits canonically as `S⁻¹R × R/(e)`. -/
theorem exists_idempotent_algEquiv_localization_prod_quotient_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃ (e : R) (_ : IsIdempotentElem e)
      (φ : R ≃ₐ[R] (Localization S × (R ⧸ Ideal.span ({e} : Set R)))),
        (RingHom.fst (Localization S) (R ⧸ Ideal.span ({e} : Set R))).comp φ.toRingHom =
          algebraMap R (Localization S) := by
  obtain ⟨e, he, hrange⟩ :=
    existsUnique_idempotent_basicOpen_eq_range_comap_of_isClosed_range_comap S hclosed h |>.exists
  let J : Ideal R := Ideal.span ({1 - e} : Set R)
  let K : Ideal R := Ideal.span ({e} : Set R)
  have hsurj : Function.Surjective (algebraMap R (Localization S)) :=
    algebraMap_surjective_of_isClosed_range_comap S hclosed
  have hzeroI : zeroLocus (RingHom.ker (algebraMap R (Localization S))) =
      (basicOpen e : Set (PrimeSpectrum R)) := by
    rw [← range_comap_of_surjective (Localization S) (algebraMap R (Localization S)) hsurj]
    simpa using hrange
  have hkernel : RingHom.ker (algebraMap R (Localization S)) = Ideal.span ({1 - e} : Set R) := by
    have hquotientKerBijective :
        Function.Bijective (Ideal.kerLiftAlg (Algebra.ofId R (Localization S))) := by
      refine ⟨Ideal.kerLiftAlg_injective (Algebra.ofId R (Localization S)), ?_⟩
      intro z
      obtain ⟨r, rfl⟩ := hsurj z
      exact ⟨Ideal.Quotient.mk _ r, Ideal.kerLiftAlg_mk (Algebra.ofId R (Localization S)) r⟩
    have quotientKerEquiv : (R ⧸ RingHom.ker (algebraMap R (Localization S))) ≃ₐ[R] Localization S :=
      AlgEquiv.ofBijective (Ideal.kerLiftAlg (Algebra.ofId R (Localization S)))
        hquotientKerBijective
    haveI : (RingHom.ker (algebraMap R (Localization S))).Pure :=
      Module.Flat.of_linearEquiv quotientKerEquiv.toLinearEquiv
    have awayQuotientEquiv : (R ⧸ J) ≃ₐ[R] Localization.Away e := by
      letI : IsLocalization.Away e (R ⧸ J) := by
        simpa using IsLocalization.Away.quotient_of_isIdempotentElem he
      exact IsLocalization.algEquiv (Submonoid.powers e) (R ⧸ J) (Localization.Away e)
    haveI : J.Pure := Module.Flat.of_linearEquiv awayQuotientEquiv.toLinearEquiv
    have hzeroJ : zeroLocus J = (basicOpen e : Set (PrimeSpectrum R)) := by
      rw [zeroLocus_span]
      exact (basicOpen_eq_zeroLocus_of_isIdempotentElem e he).symm
    exact (Ideal.zeroLocus_inj_of_pure).mp <| hzeroI.trans hzeroJ.symm
  have localizationFactorEquiv : (R ⧸ J) ≃ₐ[R] Localization S := by
    letI : IsLocalization.Away e (R ⧸ J) := by
      simpa using IsLocalization.Away.quotient_of_isIdempotentElem he
    let awayQuotientEquiv : (R ⧸ J) ≃ₐ[R] Localization.Away e :=
      IsLocalization.algEquiv (Submonoid.powers e) (R ⧸ J) (Localization.Away e)
    letI : IsLocalization.Away e (Localization S) :=
      IsLocalization.away_of_isIdempotentElem he hkernel hsurj
    exact awayQuotientEquiv.trans <|
      IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e) (Localization S)
  let splitQuot : R ≃ₐ[R] ((R ⧸ J) × (R ⧸ K)) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he (by simp) (by simp [sub_mul, he.eq])
  let φ : R ≃ₐ[R] (Localization S × (R ⧸ K)) :=
    splitQuot.trans <| AlgEquiv.prodCongr localizationFactorEquiv
      (AlgEquiv.refl : (R ⧸ K) ≃ₐ[R] (R ⧸ K))
  refine ⟨e, he, φ, ?_⟩
  ext r
  simpa [φ] using localizationFactorEquiv.commutes r

/-- Lemma 10.33.2 (3): if the image of `Spec(S⁻¹R) → Spec(R)` is closed and either `Spec(R)` is a
Noetherian topological space or `S` is finitely generated, then `R` is isomorphic to a product
`S⁻¹R × R'` for some commutative ring `R'`. -/
theorem exists_complementary_factor_ringEquiv_localization_prod_of_isClosed_range_comap
    (hclosed : IsClosed imageSet) (h : NoetherianSpace (PrimeSpectrum R) ∨ S.FG) :
    ∃ (R' : Type u) (_ : CommRing R') (φ : R ≃+* (Localization S × R')),
      (RingHom.fst (Localization S) R').comp φ.toRingHom = algebraMap R (Localization S) := by
  obtain ⟨e, _, φ, hfst⟩ :=
    exists_idempotent_algEquiv_localization_prod_quotient_of_isClosed_range_comap S hclosed h
  exact ⟨R ⧸ Ideal.span ({e} : Set R), inferInstance, φ.toRingEquiv, hfst⟩

end
