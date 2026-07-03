import Mathlib
import StacksProject_2024.Chap10.Lemma_10_33_1
import StacksProject_2024.Chap10.Lemma_10_41_3

-- Declarations for this item will be appended below by the statement pipeline.

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
