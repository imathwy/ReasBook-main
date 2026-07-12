import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_1_Basic
import StacksProject_2024.Chap10.Definition_10_136_5
import StacksProject_2024.Chap10.Lemma_10_136_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {Sbar : Type v} [CommRing Sbar] [Algebra (R ⧸ I) Sbar]

/-- Helper for Chap10 Lemma 10 136 18: syntomicity of an algebra map supplies algebraic finite
presentation of the target. -/
private lemma finitePresentationOfSyntomicAlgebraMap
    {A : Type v} [CommRing A] [Algebra R A]
    (hA : (algebraMap R A).Syntomic) :
    Algebra.FinitePresentation R A := by
  -- Project the finite-presentation field of syntomicity and translate it to the algebra owner.
  exact RingHom.finitePresentation_algebraMap.mp hA.finitePresentation

/-- Helper for Chap10 Lemma 10 136 18: finite presentation over the base is preserved by the
trivial principal localization `D(1)`. -/
private lemma finitePresentation_localizationAway_one_of_finitePresentation
    {A : Type v} [CommRing A] [Algebra R A]
    (hfp : Algebra.FinitePresentation R A) :
    Algebra.FinitePresentation R (Localization.Away (1 : A)) := by
  -- Compose the finite-presentation algebra map with the finite-presentation localization map.
  have hloc :
      (algebraMap A (Localization.Away (1 : A))).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr
      (IsLocalization.Away.finitePresentation (S := Localization.Away (1 : A)) (1 : A))
  let g : A →+* Localization.Away (1 : A) := algebraMap A (Localization.Away (1 : A))
  have hbase : (algebraMap R A).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr hfp
  have hcomp : (g.comp (algebraMap R A)).FinitePresentation :=
    RingHom.FinitePresentation.comp hloc hbase
  have hEq : g.comp (algebraMap R A) = algebraMap R (Localization.Away (1 : A)) := by
    -- The composite is definitionally the algebra map into the localized algebra.
    ext r
    rfl
  exact (RingHom.finitePresentation_algebraMap).mp <| hEq ▸ hcomp

/-- Helper for Chap10 Lemma 10 136 18: syntomic fibers give a local complete-intersection fiber
over the prime contracted from a chosen target prime. -/
private lemma fiberLCIAtUnderPrime_of_syntomic
    {A : Type v} [CommRing A] [Algebra R A]
    (hA : (algebraMap R A).Syntomic) (q : PrimeSpectrum A) :
    _root_.IsLocalCompleteIntersection (q.asIdeal.under R).ResidueField
      ((q.asIdeal.under R).Fiber A) := by
  -- Specialize the fiberwise LCI field at the contraction of `q`.
  have hfib : (algebraMap R A).HasLocalCompleteIntersectionFibers :=
    hA.hasLocalCompleteIntersectionFibers
  rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap] at hfib
  simpa [Ideal.under] using hfib (PrimeSpectrum.comap (algebraMap R A) q)

/-- Helper for Chap10 Lemma 10 136 18: finite presentation, local flatness, and an LCI fiber at
a target prime spread to a relative global complete-intersection principal-open neighborhood. -/
private theorem relativeGlobalCompleteIntersectionNeighborhood_of_finitePresentation_flat_lciFiber
    {A : Type v} [CommRing A] [Algebra R A] (q : PrimeSpectrum A)
    (hfinite : Algebra.FinitePresentation R A)
    (hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl).Flat)
    (hfiber :
      _root_.IsLocalCompleteIntersection (q.asIdeal.under R).ResidueField
        ((q.asIdeal.under R).Fiber A)) :
    ∃ g : A, g ∉ q.asIdeal ∧ IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  -- The global finite-presentation hypothesis already gives the finite-presentation chart on
  -- the trivial principal neighbourhood of `q`.
  have hone : (1 : A) ∉ q.asIdeal := by
    simpa [Ideal.eq_top_iff_one] using q.2.ne_top
  have hchart : Algebra.FinitePresentation R (Localization.Away (1 : A)) :=
    finitePresentation_localizationAway_one_of_finitePresentation hfinite
  -- TODO: prove the Lemma 10.136.15 spreading direction here or in an earlier support owner:
  -- first package `hchart` on `D(1)`, `hone`, `hflat`, and `hfiber` into the at-prime
  -- finite-presentation/flat/fiber-CI criterion, then apply the presentation-level shrink from
  -- Lemma 10.136.10 and clear any iterated localization back to one element of `A`.
  sorry

/-- Helper for Chap10 Lemma 10 136 18: a syntomic algebra has a relative global complete
intersection principal-open neighborhood at each target prime. -/
private theorem relativeGlobalCompleteIntersectionNeighborhoodOfSyntomicAtPrime
    {A : Type v} [CommRing A] [Algebra R A]
    (hA : (algebraMap R A).Syntomic) (q : PrimeSpectrum A) :
    ∃ g : A, g ∉ q.asIdeal ∧ IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  -- Route correction: importing the earlier at-prime TFAE forces Lake to rebuild broken upstream
  -- files in this task.  The target-local route therefore keeps the same mathematical frontier:
  -- syntomicity gives finite presentation, local flatness, and LCI fibers at `q`; the missing
  -- primitive theorem converts that package into an RGCI principal open.
  have hfinite : Algebra.FinitePresentation R A :=
    finitePresentationOfSyntomicAlgebraMap hA
  have hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl).Flat := by
    -- Localize the flat syntomic map at the contracted source prime and the target prime.
    exact RingHom.Flat.localRingHom hA.flat q.asIdeal (q.asIdeal.under R) rfl
  have hfiber :
      _root_.IsLocalCompleteIntersection (q.asIdeal.under R).ResidueField
        ((q.asIdeal.under R).Fiber A) :=
    fiberLCIAtUnderPrime_of_syntomic hA q
  -- Apply the isolated primitive spreading theorem to the syntomic side conditions.
  exact
    relativeGlobalCompleteIntersectionNeighborhood_of_finitePresentation_flat_lciFiber
      q hfinite hflat hfiber

/-- Helper for Chap10 Lemma 10 136 18: a family of principal opens covering every prime has
unit ideal span. -/
private lemma span_eq_top_of_basicOpen_cover {A : Type v} [CommRing A] (s : Set A)
    (hs : ∀ q : PrimeSpectrum A, ∃ g ∈ s, g ∉ q.asIdeal) :
    Ideal.span s = ⊤ := by
  -- Convert the pointwise principal-open cover into the top open of `Spec A`.
  have hscover :
      (⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤ := by
    apply SetLike.ext'
    change (↑(⨆ g ∈ s, PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum A)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro q
    rcases hs q with ⟨g, hgs, hgq⟩
    have hgmem : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgq
    exact
      (show (PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum A)) ≤
          ⨆ h ∈ s, PrimeSpectrum.basicOpen h from
        le_iSup_of_le g <| le_iSup_of_le hgs le_rfl) hgmem
  -- The standard affine-spectrum criterion identifies such covers with unit ideal spans.
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hscover

/-- Helper for Chap10 Lemma 10 136 18: a syntomic algebra is covered by principal opens that are
relative global complete intersections. -/
private theorem relativeGlobalCompleteIntersectionCoverOfSyntomic
    {A : Type v} [CommRing A] [Algebra R A]
    (hA : (algebraMap R A).Syntomic) :
    ∃ s : Set A, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  classical
  let s : Set A := {g | IsRelativeGlobalCompleteIntersection R (Localization.Away g)}
  refine ⟨s, ?_, ?_⟩
  · -- The pointwise syntomic neighborhood criterion supplies a principal-open cover by elements
    -- already in the chosen set `s`.
    exact span_eq_top_of_basicOpen_cover s fun q ↦ by
      rcases relativeGlobalCompleteIntersectionNeighborhoodOfSyntomicAtPrime hA q with
        ⟨g, hgq, hgci⟩
      exact ⟨g, hgci, hgq⟩
  · -- Membership in `s` is exactly the chart condition required by the cover.
    intro g hg
    exact hg

/-- Helper for Chap10 Lemma 10 136 18: coefficients in a quotient presentation lift along
`R → R ⧸ I`. -/
private lemma presentationHasCoeffsOfQuotient {T : Type v} [CommRing T] [Algebra (R ⧸ I) T]
    [Algebra R T] [IsScalarTower R (R ⧸ I) T] {ι σ : Type*}
    (P : Algebra.Presentation (R ⧸ I) T ι σ) :
    P.HasCoeffs R := by
  -- Each coefficient has a representative in `R`, so the whole coefficient set lies in the
  -- image of the base-change map.
  refine ⟨?_⟩
  intro x _hx
  simpa using (Ideal.Quotient.mk_surjective x : ∃ y : R, Ideal.Quotient.mk I y = x)

/-- Helper for Chap10 Lemma 10 136 18: the model obtained by lifting presentation coefficients
reduces modulo `I` to the original quotient presentation. -/
private noncomputable def reducedPresentationQuotientEquiv {T : Type v} [CommRing T]
    [Algebra (R ⧸ I) T] [Algebra R T] [IsScalarTower R (R ⧸ I) T] {ι σ : Type*}
    (P : Algebra.Presentation (R ⧸ I) T ι σ) [P.HasCoeffs R] :
    (P.ModelOfHasCoeffs R ⧸ Ideal.map (algebraMap R (P.ModelOfHasCoeffs R)) I) ≃ₐ[R ⧸ I] T :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (P.ModelOfHasCoeffs R) I).trans
    (P.tensorModelOfHasCoeffsEquiv R)

/-- Helper for Chap10 Lemma 10 136 18: relative global complete intersections are invariant
under algebra equivalence over the base. -/
private theorem relativeGlobalCompleteIntersection_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (hA : IsRelativeGlobalCompleteIntersection R A) (e : A ≃ₐ[R] B) :
    IsRelativeGlobalCompleteIntersection R B := by
  -- Transport the presentation witness through the algebra equivalence and compare fibers by the
  -- induced tensor-product equivalence.
  rcases hA.exists_presentation with ⟨n, c, P, hP⟩
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P.ofAlgEquiv e) ?_
  intro p hp
  let ep : p.asIdeal.Fiber B ≃ₐ[R] p.asIdeal.Fiber A :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[R] p.asIdeal.ResidueField)
      e.symm
  have hpA : Nonempty (PrimeSpectrum (p.asIdeal.Fiber A)) := by
    -- Nonemptiness transfers back across the fiber equivalence.
    have hp_nontrivial : Nontrivial (p.asIdeal.Fiber B) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    let _ : Nontrivial (p.asIdeal.Fiber B) := hp_nontrivial
    have hpA_nontrivial : Nontrivial (p.asIdeal.Fiber A) :=
      RingHom.domain_nontrivial ep.symm.toRingHom
    exact PrimeSpectrum.nonempty_iff_nontrivial.mpr hpA_nontrivial
  calc
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim (p.asIdeal.Fiber A) := by
      simpa [ep] using (ringKrullDim_eq_of_ringEquiv ep.toRingEquiv)
    _ = P.dimension := hP p hpA
    _ = (P.ofAlgEquiv e).dimension := by
      exact_mod_cast P.dimension_ofAlgEquiv e

/-- Helper for Chap10 Lemma 10 136 18: mapping an ideal through a composite algebra tower agrees
with mapping it in two steps. -/
private lemma localizationIdealMapEq {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (K : Ideal A) :
    Ideal.map (algebraMap A C) K = Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) K) := by
  -- Rewrite the algebra map through the tower before applying the canonical ideal-map formula.
  calc
    Ideal.map (algebraMap A C) K
        = Ideal.map (((algebraMap B C) : B →+* C).comp (algebraMap A B)) K := by
            rw [IsScalarTower.algebraMap_eq A B C]
    _ = Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) K) := by
          rw [Ideal.map_map]

/-- Helper for Chap10 Lemma 10 136 18: an algebra structure defined by a composite has that
composite as its algebra map. -/
private lemma algebraMapEqCompOfToAlgebra {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] :
    let _ : Algebra A C := RingHom.toAlgebra (((algebraMap B C) : B →+* C).comp (algebraMap A B))
    ∀ a : A, algebraMap A C a = algebraMap B C (algebraMap A B a) := by
  -- Unfold the chosen `RingHom.toAlgebra` structure to expose its defining map.
  dsimp
  intro a
  simp [RingHom.algebraMap_toAlgebra]

/-- Helper for Chap10 Lemma 10 136 18: if the localizing element is already a unit after
reducing modulo `I`, then reducing the away localization gives back the reduced source ring. -/
private lemma localizationAwayReductionEquivOfUnitModIdeal {A : Type*} [CommRing A]
    [Algebra R A] {g : A}
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) g)) :
    Nonempty
      ((A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I]
        (Localization.Away g ⧸
          Ideal.map (algebraMap R (Localization.Away g)) I)) := by
  classical
  let J : Ideal A := Ideal.map (algebraMap R A) I
  let S : Type _ := Localization.Away g
  letI : CommRing S := inferInstance
  letI : Algebra A S := inferInstance
  letI : Algebra R S := inferInstance
  -- First rewrite the quotient ideal in the localization through the intermediate ring `A`.
  have hmapJS :
      Ideal.map (algebraMap R S) I = Ideal.map (algebraMap A S) J := by
    simpa [S, J] using localizationIdealMapEq (A := R) (B := A) (C := S) I
  have hunitJ : IsUnit (Ideal.Quotient.mk J g) := by
    simpa [J] using hg
  letI : Algebra (A ⧸ J) (S ⊗[A] (A ⧸ J)) :=
    Algebra.TensorProduct.rightAlgebra (R := A) (A := S) (B := A ⧸ J)
  let eQuotTensor :
      (S ⧸ Ideal.map (algebraMap A S) J) ≃ₐ[A ⧸ J] ((A ⧸ J) ⊗[A] S) :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor S J
  let eTensorComm :
      ((A ⧸ J) ⊗[A] S) ≃ₐ[A ⧸ J] (S ⊗[A] (A ⧸ J)) :=
    { __ := Algebra.TensorProduct.comm A (A ⧸ J) S
      commutes' := fun _ ↦ rfl }
  let eTensorAway :
      (S ⊗[A] (A ⧸ J)) ≃ₐ[A ⧸ J] Localization.Away (Ideal.Quotient.mk J g) :=
    IsLocalization.Away.tensorRightEquiv (R := A) (S := A ⧸ J) (A := S) (r := g)
  let eAwayCollapse :
      Localization.Away (Ideal.Quotient.mk J g) ≃ₐ[A ⧸ J] (A ⧸ J) :=
    (IsLocalization.atUnit (A ⧸ J) (Localization.Away (Ideal.Quotient.mk J g))
      (Ideal.Quotient.mk J g) hunitJ).symm
  -- Compose the quotient-tensor, tensor-commutation, and unit-collapse equivalences over `A/I`.
  let eReduced :
      (S ⧸ Ideal.map (algebraMap A S) J) ≃ₐ[A ⧸ J] (A ⧸ J) :=
    eQuotTensor.trans (eTensorComm.trans (eTensorAway.trans eAwayCollapse))
  letI : Algebra (R ⧸ I) (S ⧸ Ideal.map (algebraMap A S) J) :=
    RingHom.toAlgebra
      (((algebraMap (A ⧸ J) (S ⧸ Ideal.map (algebraMap A S) J)) :
          (A ⧸ J) →+* (S ⧸ Ideal.map (algebraMap A S) J)).comp
        (algebraMap (R ⧸ I) (A ⧸ J)))
  let eReducedRbar :
      (S ⧸ Ideal.map (algebraMap A S) J) ≃ₐ[R ⧸ I] (A ⧸ J) :=
    { __ := eReduced.toRingEquiv
      commutes' := by
        intro r
        rw [algebraMapEqCompOfToAlgebra (A := R ⧸ I) (B := A ⧸ J)
          (C := S ⧸ Ideal.map (algebraMap A S) J) r]
        exact eReduced.commutes ((algebraMap (R ⧸ I) (A ⧸ J)) r) }
  have hmapJSquot :
      Ideal.map (algebraMap A S) J =
        (Ideal.map (algebraMap R S) I).map (RingEquiv.refl S : S →+* S) := by
    simpa using hmapJS.symm
  let eMapEq :
      (S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I]
        (S ⧸ Ideal.map (algebraMap A S) J) :=
    { __ := Ideal.quotientEquiv _ _ (RingEquiv.refl S) hmapJSquot
      commutes' := by
        rintro ⟨r⟩
        rfl }
  exact ⟨eReducedRbar.symm.trans eMapEq.symm⟩

/-- Helper for Chap10 Lemma 10 136 18: a coefficient-lifted quotient presentation whose fibers
have the expected dimension on `V(I)` admits a relative-GCI principal localization by an element
equal to one modulo `I`. -/
private theorem existsLocalizationAwayOneModIdealOfModelOfHasCoeffsFiberDimensionOnClosedSet
    {T : Type v} [CommRing T] [Algebra (R ⧸ I) T] [Algebra R T]
    [IsScalarTower R (R ⧸ I) T] {n c : ℕ}
    (P : Algebra.Presentation (R ⧸ I) T (Fin n) (Fin c)) [P.HasCoeffs R]
    (hdim : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber (P.ModelOfHasCoeffs R))) →
        ringKrullDim (p.asIdeal.Fiber (P.ModelOfHasCoeffs R)) =
          (n - c : WithBot ℕ∞)) :
    ∃ g : P.ModelOfHasCoeffs R,
      Ideal.Quotient.mk (Ideal.map (algebraMap R (P.ModelOfHasCoeffs R)) I) g = 1 ∧
        IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  classical
  -- Apply Lemma 10.136.10 to the explicit quotient model cut out by the lifted relations.
  obtain ⟨h, g, e, _hgpoly, hgmod, hgciDisplayed⟩ :=
    _root_.exists_relativeGlobalCompleteIntersection_localizationAway_of_fiberDimension_on_closedSet
      (R := R) (n := n) (c := c) (f := P.relationOfHasCoeffs R) I hdim
  refine ⟨g, hgmod, ?_⟩
  -- The owner theorem gives RGCI on the displayed localization quotient; transport it back to
  -- the actual away localization used in this file.
  exact relativeGlobalCompleteIntersection_of_algEquiv hgciDisplayed e.symm

/-- Helper for Chap10 Lemma 10 136 18: a prime of `R` containing `I` descends to a prime of
`R ⧸ I`. -/
private def quotientPrimeOfLe (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) :
    PrimeSpectrum (R ⧸ I) :=
  ⟨Ideal.map (Ideal.Quotient.mk I) p.asIdeal, Ideal.isPrime_map_quotientMk_of_isPrime hpI⟩

/-- Helper for Chap10 Lemma 10 136 18: the descended quotient prime contracts back to the
original prime. -/
private lemma quotientPrimeOfLe_comap (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I) (quotientPrimeOfLe (I := I) p hpI) = p := by
  -- This pins down the quotient-prime correspondence used by the later fiber transport.
  ext x
  change x ∈ Ideal.comap (Ideal.Quotient.mk I)
      (Ideal.map (Ideal.Quotient.mk I) p.asIdeal) ↔ x ∈ p.asIdeal
  rw [Ideal.comap_map_mk hpI]

/-- Helper for Chap10 Lemma 10 136 18: the residue fields at `p` and at the descended quotient
prime are canonically ring-equivalent. -/
private noncomputable def quotientPrimeResidueFieldEquiv (p : PrimeSpectrum R)
    (hpI : I ≤ p.asIdeal) :
    p.asIdeal.ResidueField ≃+* (quotientPrimeOfLe (I := I) p hpI).asIdeal.ResidueField :=
  RingEquiv.ofBijective
    (Ideal.ResidueField.map p.asIdeal (quotientPrimeOfLe (I := I) p hpI).asIdeal
      (Ideal.Quotient.mk I)
      (congrArg PrimeSpectrum.asIdeal (quotientPrimeOfLe_comap (I := I) p hpI).symm))
    (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_surjective
        (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I)))
      p.asIdeal (quotientPrimeOfLe (I := I) p hpI).asIdeal
      (congrArg PrimeSpectrum.asIdeal (quotientPrimeOfLe_comap (I := I) p hpI).symm))

/-- Helper for Chap10 Lemma 10 136 18: the quotient-prime residue-field equivalence is compatible
with the quotient map from `R`. -/
private lemma quotientPrimeResidueFieldEquiv_apply_algebraMap
    (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) (r : R) :
    quotientPrimeResidueFieldEquiv (I := I) p hpI
        (algebraMap R p.asIdeal.ResidueField r) =
      algebraMap (R ⧸ I) (quotientPrimeOfLe (I := I) p hpI).asIdeal.ResidueField
        (Ideal.Quotient.mk I r) := by
  -- This is the computation rule needed to align the two tensor-product fiber surfaces.
  dsimp [quotientPrimeResidueFieldEquiv]
  rw [Ideal.ResidueField.map_algebraMap]

/-- Helper for Chap10 Lemma 10 136 18: the residue-field equivalence at a prime over `I` is an
`R`-algebra equivalence. -/
private noncomputable def quotientPrimeResidueFieldAlgEquiv (p : PrimeSpectrum R)
    (hpI : I ≤ p.asIdeal) :
    p.asIdeal.ResidueField ≃ₐ[R] (quotientPrimeOfLe (I := I) p hpI).asIdeal.ResidueField :=
  { __ := quotientPrimeResidueFieldEquiv (I := I) p hpI
    commutes' := by
      intro r
      -- The ring equivalence is defined by the quotient residue-field map, so it respects the
      -- original `R`-algebra structures after unfolding the scalar tower through `R ⧸ I`.
      simpa [IsScalarTower.algebraMap_apply R (R ⧸ I)
        (quotientPrimeOfLe (I := I) p hpI).asIdeal.ResidueField] using
        quotientPrimeResidueFieldEquiv_apply_algebraMap (I := I) p hpI r }

/-- Helper for Chap10 Lemma 10 136 18: the lifted coefficient model fiber over a prime
containing `I` is ring-equivalent to the original quotient-presentation fiber over the descended
prime. -/
private noncomputable def fiberOfModelOfHasCoeffsAtPrimeQuotientRingEquiv
    {T : Type v} [CommRing T] [Algebra (R ⧸ I) T] [Algebra R T]
    [IsScalarTower R (R ⧸ I) T] {n c : ℕ}
    (P : Algebra.Presentation (R ⧸ I) T (Fin n) (Fin c)) [P.HasCoeffs R]
    (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) :
    p.asIdeal.Fiber (P.ModelOfHasCoeffs R) ≃+*
      (quotientPrimeOfLe (I := I) p hpI).asIdeal.Fiber T := by
  let pbar : PrimeSpectrum (R ⧸ I) := quotientPrimeOfLe (I := I) p hpI
  let S0 := P.ModelOfHasCoeffs R
  let eResid : p.asIdeal.ResidueField ≃ₐ[R] pbar.asIdeal.ResidueField :=
    quotientPrimeResidueFieldAlgEquiv (I := I) p hpI
  let eChange₁ : p.asIdeal.ResidueField ⊗[R] S0 ≃ₐ[R]
      pbar.asIdeal.ResidueField ⊗[R] S0 :=
    Algebra.TensorProduct.congr eResid (AlgEquiv.refl : S0 ≃ₐ[R] S0)
  let eCancel : pbar.asIdeal.ResidueField ⊗[R] S0 ≃ₐ[pbar.asIdeal.ResidueField]
      pbar.asIdeal.ResidueField ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] S0) :=
    (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I) pbar.asIdeal.ResidueField
      pbar.asIdeal.ResidueField S0).symm
  let eModel : pbar.asIdeal.ResidueField ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] S0)
      ≃ₐ[pbar.asIdeal.ResidueField] pbar.asIdeal.ResidueField ⊗[R ⧸ I] T :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl :
        pbar.asIdeal.ResidueField ≃ₐ[pbar.asIdeal.ResidueField]
          pbar.asIdeal.ResidueField)
      (P.tensorModelOfHasCoeffsEquiv R)
  -- The bridge first changes residue fields, then cancels the `R ⧸ I` base change, and finally
  -- uses the lifted-presentation tensor equivalence.
  exact (eChange₁.toRingEquiv.trans eCancel.toRingEquiv).trans eModel.toRingEquiv

/-- Helper for Chap10 Lemma 10 136 18: the lifted coefficient model has the same expected fiber
dimension over primes of `R` containing `I` as the original quotient presentation. -/
private lemma liftedPresentationFiberDimensionOnClosedSet
    {T : Type v} [CommRing T] [Algebra (R ⧸ I) T] [Algebra R T]
    [IsScalarTower R (R ⧸ I) T] {n c : ℕ}
    (P : Algebra.Presentation (R ⧸ I) T (Fin n) (Fin c)) [P.HasCoeffs R]
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber (P.ModelOfHasCoeffs R))) →
        ringKrullDim (p.asIdeal.Fiber (P.ModelOfHasCoeffs R)) =
          (n - c : WithBot ℕ∞) := by
  intro p hpI hpne
  -- The quotient presentation controls the fiber at the descended prime `p / I`.
  let pbar : PrimeSpectrum (R ⧸ I) := quotientPrimeOfLe (I := I) p hpI
  have hpbar_contract : PrimeSpectrum.comap (Ideal.Quotient.mk I) pbar = p :=
    quotientPrimeOfLe_comap (I := I) p hpI
  let e := fiberOfModelOfHasCoeffsAtPrimeQuotientRingEquiv (R := R) (I := I) P p hpI
  have hpbar_ne : Nonempty (PrimeSpectrum (pbar.asIdeal.Fiber T)) := by
    -- Nonemptiness of spectra is transported as nontriviality across the fiber equivalence.
    have hsrc : Nontrivial (p.asIdeal.Fiber (P.ModelOfHasCoeffs R)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hpne
    let _ : Nontrivial (p.asIdeal.Fiber (P.ModelOfHasCoeffs R)) := hsrc
    have htar : Nontrivial (pbar.asIdeal.Fiber T) :=
      RingHom.domain_nontrivial e.symm.toRingHom
    exact PrimeSpectrum.nonempty_iff_nontrivial.mpr htar
  -- Transfer Krull dimension through the same equivalence and apply the quotient presentation
  -- dimension hypothesis at the descended prime.
  calc
    ringKrullDim (p.asIdeal.Fiber (P.ModelOfHasCoeffs R)) =
        ringKrullDim (pbar.asIdeal.Fiber T) := by
          simpa [e] using (ringKrullDim_eq_of_ringEquiv e)
    _ = P.dimension := hP pbar hpbar_ne
    _ = (n - c : WithBot ℕ∞) := by
      simp [Algebra.Presentation.dimension]

/-- Helper for Chap10 Lemma 10 136 18: a single quotient-relative-GCI chart lifts to a relative
global complete intersection over the original base. -/
private theorem existsRelativeGlobalCompleteIntersectionLiftOfQuotientRelativeGlobalCompleteIntersection
    {T : Type v} [CommRing T] [Algebra (R ⧸ I) T] [Algebra R T]
    [IsScalarTower R (R ⧸ I) T]
    (hT : IsRelativeGlobalCompleteIntersection (R ⧸ I) T) :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
      (_ : IsRelativeGlobalCompleteIntersection R S),
        Nonempty (T ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := by
  classical
  -- Choose a quotient-relative-GCI presentation and lift its coefficients from `R ⧸ I` to `R`.
  rcases hT.exists_presentation with ⟨n, c, P, hP⟩
  letI : P.HasCoeffs R := presentationHasCoeffsOfQuotient (R := R) (I := I) P
  let S0 := P.ModelOfHasCoeffs R
  letI : CommRing S0 := inferInstance
  letI : Algebra R S0 := inferInstance
  have hdim : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber S0)) →
        ringKrullDim (p.asIdeal.Fiber S0) = (n - c : WithBot ℕ∞) := by
    -- The quotient-prime fiber transport is now isolated in the dedicated bridge lemma.
    exact liftedPresentationFiberDimensionOnClosedSet (R := R) (I := I) P hP
  -- The closed-set shrink supplies the localizing element and the lifted RGCI chart.
  obtain ⟨g, hgmod, hgciLoc⟩ :=
    existsLocalizationAwayOneModIdealOfModelOfHasCoeffsFiberDimensionOnClosedSet
      (R := R) (I := I) P hdim
  let e0 : (S0 ⧸ Ideal.map (algebraMap R S0) I) ≃ₐ[R ⧸ I] T :=
    reducedPresentationQuotientEquiv (R := R) (I := I) P
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.map (algebraMap R S0) I) g) := by
    -- The chosen element is congruent to `1` modulo `I`, hence becomes a unit after reduction.
    rw [hgmod]
    exact isUnit_one
  obtain ⟨eRed⟩ :=
    localizationAwayReductionEquivOfUnitModIdeal (R := R) (I := I) (A := S0) (g := g) hunit
  let eTLoc : T ≃ₐ[R ⧸ I]
      (Localization.Away g ⧸ Ideal.map (algebraMap R (Localization.Away g)) I) :=
    e0.symm.trans eRed
  -- Lift the localization into the target universe and transport both the RGCI owner and quotient
  -- comparison across the tautological `ULift` algebra equivalence.
  let U : Type (max u v) := ULift.{v} (Localization.Away g)
  letI : CommRing U := inferInstance
  letI : Algebra R U := inferInstance
  let fUL : Localization.Away g →ₐ[R] U :=
    { toRingHom :=
        { toFun := ULift.up
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      commutes' := fun _ ↦ rfl }
  have hfUL : Function.Bijective fUL := by
    constructor
    · intro x y hxy
      exact congrArg ULift.down hxy
    · intro y
      refine ⟨y.down, ?_⟩
      cases y
      rfl
  let eUL : Localization.Away g ≃ₐ[R] U := AlgEquiv.ofBijective fUL hfUL
  have hciU : IsRelativeGlobalCompleteIntersection R U := by
    -- Relative GCI is invariant under algebra equivalence over the base.
    exact relativeGlobalCompleteIntersection_of_algEquiv hgciLoc eUL
  have hULmap :
      Ideal.map (algebraMap R (Localization.Away g)) I =
        (Ideal.map (algebraMap R U) I).map (eUL.symm : U →+* Localization.Away g) := by
    -- Compare the quotient ideals after replacing the localization by its `ULift`.
    calc
      Ideal.map (algebraMap R (Localization.Away g)) I
          = Ideal.map (((eUL.symm : U →+* Localization.Away g).comp (algebraMap R U))) I := by
              congr 1
              ext r
              simpa using eUL.symm.commutes r
      _ = (Ideal.map (algebraMap R U) I).map (eUL.symm : U →+* Localization.Away g) := by
            rw [Ideal.map_map]
  let eULquotR :
      (U ⧸ Ideal.map (algebraMap R U) I) ≃ₐ[R]
        (Localization.Away g ⧸ Ideal.map (algebraMap R (Localization.Away g)) I) :=
    Ideal.quotientEquivAlg _ _ eUL.symm hULmap
  let eULquot :
      (U ⧸ Ideal.map (algebraMap R U) I) ≃ₐ[R ⧸ I]
        (Localization.Away g ⧸ Ideal.map (algebraMap R (Localization.Away g)) I) :=
    { __ := eULquotR
      commutes' := by
        rintro ⟨r⟩
        change Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.Away g)) I)
            (eUL.symm (algebraMap R U r)) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.Away g)) I)
            (algebraMap R (Localization.Away g) r)
        exact congrArg
          (Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.Away g)) I))
          (eUL.symm.commutes r) }
  exact ⟨U, inferInstance, inferInstance, hciU, ⟨eTLoc.trans eULquot.symm⟩⟩

-- Proof sketch: apply Lemma `10.136.15` to obtain a cover of `Spec S̄` by basic opens on which
-- the localization is a relative global complete intersection over `R ⧸ I`. For each such
-- localization, choose a presentation from Definition `10.136.5`, lift the defining equations to
-- `R`, form the corresponding quotient algebra over `R`, and then use Lemma `10.136.10` to shrink
-- once more so that this lift is itself a relative global complete intersection over `R`.
/-- Lemma 10.136.18: a syntomic `(R ⧸ I)`-algebra admits a unit-ideal cover by basic opens whose
localizations are reductions modulo `I` of relative global complete intersections over `R`. -/
@[stacks 00T0]
theorem exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic
    (hSbar : (algebraMap (R ⧸ I) Sbar).Syntomic) :
    ∃ s : Set Sbar, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsRelativeGlobalCompleteIntersection R S),
          Nonempty ((Localization.Away g) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := by
  classical
  -- First cover the quotient algebra by relative-GCI principal opens over `R ⧸ I`.
  obtain ⟨s, hs, hcharts⟩ :=
    relativeGlobalCompleteIntersectionCoverOfSyntomic
      (R := R ⧸ I) (A := Sbar) hSbar
  refine ⟨s, hs, ?_⟩
  intro g hg
  let T := Localization.Away g
  letI : Algebra R T :=
    RingHom.toAlgebra (((algebraMap (R ⧸ I) T) : (R ⧸ I) →+* T).comp (Ideal.Quotient.mk I))
  letI : IsScalarTower R (R ⧸ I) T :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hT : IsRelativeGlobalCompleteIntersection (R ⧸ I) T := hcharts g hg
  -- Then lift each quotient-relative-GCI chart independently.
  simpa [T] using
    existsRelativeGlobalCompleteIntersectionLiftOfQuotientRelativeGlobalCompleteIntersection
      (R := R) (I := I) (T := T) hT

end

end Algebra
