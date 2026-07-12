import Mathlib
import StacksProject_2024.Chap10.Lemma_10_116_5
import StacksProject_2024.Chap10.Lemma_10_125_6
import StacksProject_2024.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u

noncomputable section

section

namespace Algebra

variable {R : Type u} [CommRing R]

/-- Helper for Chap10 Lemma 10 136 11: finitely many polynomial relations have coefficients in
a finite type `ℤ`-subalgebra and therefore admit simultaneous lifts to that subalgebra. -/
private theorem exists_coeffSubalgebra_lifts_relations
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R) :
    ∃ (R₀ : Subalgebra ℤ R), Algebra.FiniteType ℤ R₀ ∧
      ∃ f₀ : Fin c → MvPolynomial (Fin n) R₀,
        ∀ i, MvPolynomial.map R₀.val (f₀ i) = f i := by
  classical
  -- Collect all coefficients of all displayed relations into one finite set.
  let coeffs : Finset R := Finset.univ.biUnion fun i => (f i).coeffs
  let R₀ : Subalgebra ℤ R := Algebra.adjoin ℤ (coeffs : Set R)
  have hcoeffsFinite : (coeffs : Set R).Finite := coeffs.finite_toSet
  have hfinite : Algebra.FiniteType ℤ R₀ :=
    Algebra.FiniteType.adjoin_of_finite hcoeffsFinite
  have hcoeffs : ∀ i, ((f i).coeffs : Set R) ⊆ Set.range R₀.val.toRingHom := by
    intro i r hr
    -- Each coefficient belongs to the adjoined subalgebra by construction.
    have hr_coeffs : r ∈ (coeffs : Set R) :=
      Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hr⟩)
    have hr_R₀ : r ∈ R₀ := Algebra.subset_adjoin hr_coeffs
    exact ⟨⟨r, hr_R₀⟩, rfl⟩
  have hmem : ∀ i, f i ∈ Set.range (MvPolynomial.map R₀.val.toRingHom) := by
    intro i
    -- The coefficient-range criterion turns coefficient containment into a polynomial lift.
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    exact hcoeffs i
  choose f₀ hf₀ using hmem
  refine ⟨R₀, hfinite, f₀, ?_⟩
  intro i
  simpa using hf₀ i

/-- Helper for Chap10 Lemma 10 136 11: lifting polynomial coefficients from a smaller
subalgebra to a larger one and then to the ambient ring is the same as mapping directly to the
ambient ring. -/
private theorem map_relationLift_inclusion
    {A B : Subalgebra ℤ R} (hAB : A ≤ B) {n : ℕ} (p : MvPolynomial (Fin n) A) :
    MvPolynomial.map B.val.toRingHom
        (MvPolynomial.map (Subalgebra.inclusion hAB).toRingHom p) =
      MvPolynomial.map A.val.toRingHom p := by
  -- Normalize the two coefficient maps to their composite on the ambient ring.
  rw [MvPolynomial.map_map]
  rfl

/-- Helper for Chap10 Lemma 10 136 11: two finite type `ℤ`-subalgebras containing a fixed
finite type subalgebra are dominated by a finite type `ℤ`-subalgebra. -/
private theorem finiteTypeSubalgebraOver_commonUpper
    {A B C : Subalgebra ℤ R} (_ : Algebra.FiniteType ℤ A)
    (_ : Algebra.FiniteType ℤ B) (_ : Algebra.FiniteType ℤ C)
    (hAB : A ≤ B) (hAC : A ≤ C) :
    ∃ D : Subalgebra ℤ R, Algebra.FiniteType ℤ D ∧ A ≤ D ∧ B ≤ D ∧ C ≤ D := by
  -- The lattice supremum contains both stages, and finite generation is stable under supremum.
  refine ⟨B ⊔ C, ?_, ?_, ?_, ?_⟩
  · exact (Subalgebra.fg_iff_finiteType (B ⊔ C)).mp
      ((Subalgebra.fg_iff_finiteType B).mpr inferInstance |>.sup
        ((Subalgebra.fg_iff_finiteType C).mpr inferInstance))
  · intro x hx
    -- Record both containment hypotheses, then use the left inclusion for the actual membership.
    have _ : x ∈ C := hAC hx
    exact (le_trans hAB le_sup_left) hx
  · exact le_sup_left
  · exact le_sup_right

/-- Helper for Chap10 Lemma 10 136 11: relative global complete intersection is invariant under
algebra equivalence of the target algebra. -/
private theorem isRelativeGlobalCompleteIntersection_of_algEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hA : Algebra.IsRelativeGlobalCompleteIntersection R A) (e : A ≃ₐ[R] B) :
    Algebra.IsRelativeGlobalCompleteIntersection R B := by
  rcases hA.exists_presentation with ⟨n, c, P, hP⟩
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P.ofAlgEquiv e) ?_
  intro p hp
  let ep : p.asIdeal.Fiber B ≃ₐ[R] p.asIdeal.Fiber A :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[R] p.asIdeal.ResidueField)
      e.symm
  have hpA : Nonempty (PrimeSpectrum (p.asIdeal.Fiber A)) := by
    -- A prime in one fiber transports across the induced tensor-product equivalence.
    have hp_nontrivial : Nontrivial (p.asIdeal.Fiber B) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    let _ : Nontrivial (p.asIdeal.Fiber B) := hp_nontrivial
    have hpA_nontrivial : Nontrivial (p.asIdeal.Fiber A) :=
      RingHom.domain_nontrivial ep.symm.toRingHom
    exact PrimeSpectrum.nonempty_iff_nontrivial.mpr hpA_nontrivial
  -- Compare fiber dimensions through the equivalence and reuse the source presentation witness.
  calc
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim (p.asIdeal.Fiber A) := by
      simpa [ep] using (ringKrullDim_eq_of_ringEquiv ep.toRingEquiv)
    _ = P.dimension := hP p hpA
    _ = (P.ofAlgEquiv e).dimension := by
      exact_mod_cast P.dimension_ofAlgEquiv e

/-- Helper for Chap10 Lemma 10 136 11: a quotient by finitely many polynomial relations commutes
with base change when the displayed relations map to the target displayed relations. -/
private theorem quotientBaseChangeEquiv_of_relationLifts
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n c : ℕ} (fA : Fin c → MvPolynomial (Fin n) A)
    (fB : Fin c → MvPolynomial (Fin n) B)
    (hf : ∀ i, MvPolynomial.map (algebraMap A B) (fA i) = fB i) :
    Nonempty (B ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)) ≃ₐ[B]
      (MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range fB))) := by
  classical
  let ePoly : B ⊗[A] MvPolynomial (Fin n) A ≃ₐ[B] MvPolynomial (Fin n) B :=
    MvPolynomial.algebraTensorAlgEquiv A B
  have hgen : ∀ i,
      ePoly (Algebra.TensorProduct.includeRight (fA i)) = fB i := by
    intro i
    -- The polynomial tensor equivalence sends the right-included source relation to its image.
    rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul,
      one_smul]
    exact hf i
  -- First commute quotient with tensor product, then identify the tensor polynomial ring with the
  -- target polynomial ring and compare the generated ideals relation-by-relation.
  refine Nonempty.intro ((Algebra.TensorProduct.tensorQuotientEquiv (R := A) B
    (MvPolynomial (Fin n) A) B (Ideal.span (Set.range fA))).trans ?_)
  refine Ideal.quotientEquivAlg _ _ ePoly ?_
  rw [Ideal.map_span, Ideal.map_span, Set.image_image]
  apply congrArg Ideal.span
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨fA i, ⟨i, rfl⟩, hgen i⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hgen i).symm⟩

/-- Helper for Chap10 Lemma 10 136 11: a quotient of a polynomial algebra by a finite displayed
family of relations is finitely presented over the coefficient ring. -/
private theorem finitePresentation_displayedQuotient
    {A : Type u} [CommRing A] {n c : ℕ}
    (fA : Fin c → MvPolynomial (Fin n) A) :
    Algebra.FinitePresentation A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)) := by
  -- The relation ideal is generated by a finite range, and quotienting a finitely presented
  -- polynomial algebra by a finitely generated ideal preserves finite presentation.
  letI : Algebra A (MvPolynomial (Fin n) A) := inferInstance
  letI : Module A (MvPolynomial (Fin n) A) := Algebra.toModule
  letI : Algebra.FinitePresentation A (MvPolynomial (Fin n) A) := inferInstance
  letI : Module (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A) := Semiring.toModule
  have hrelationsFG : (Ideal.span (Set.range fA)).FG := by
    exact Submodule.fg_span (Set.finite_range fA)
  exact Algebra.FinitePresentation.quotient
    (R := A) (A := MvPolynomial (Fin n) A) (I := Ideal.span (Set.range fA)) hrelationsFG

/-- Helper for Chap10 Lemma 10 136 11: the pointwise relative dimension is bounded by the
Krull dimension of the whole fiber over the contracted base prime. -/
private lemma relativeDimensionAt_le_fiberKrullDim_of_comap
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (q : PrimeSpectrum S) :
    relativeDimensionAt A S q ≤
      ringKrullDim ((PrimeSpectrum.comap (algebraMap A S) q).asIdeal.Fiber S) := by
  -- The local relative dimension is the Krull dimension of a localization of the whole fiber.
	  calc
	    relativeDimensionAt A S q = ringKrullDim (fiberLocalRingAt A S q) := rfl
	    _ = ((fiberPrimeAt A S q).asIdeal.height : WithBot ℕ∞) := by
	      rw [IsLocalization.AtPrime.ringKrullDim_eq_height
	        (fiberPrimeAt A S q).asIdeal (fiberLocalRingAt A S q)]
	    _ ≤ ringKrullDim ((PrimeSpectrum.comap (algebraMap A S) q).asIdeal.Fiber S) := by
	      -- A prime height is bounded by the Krull dimension of its ambient fiber ring.
	      exact Ideal.height_le_ringKrullDim_of_ne_top (I := (fiberPrimeAt A S q).asIdeal)
	        (fiberPrimeAt A S q).isPrime.ne_top

/-- Helper for Chap10 Lemma 10 136 11: a point of the bounded relative-dimension locus has a
basic open neighbourhood contained in that locus. -/
private theorem exists_basicOpen_subset_relativeDimensionAtLELocus_of_mem
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.FiniteType A S] {n : ℕ} (q : PrimeSpectrum S)
    (hq : q ∈ relativeDimensionAtLELocus A S n) :
    ∃ g : S, q ∈ PrimeSpectrum.basicOpen g ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
        relativeDimensionAtLELocus A S n := by
  -- First use Lemma 10.125.6 to obtain some open neighbourhood inside the bounded locus.
  obtain ⟨U, hU⟩ := exists_openNhdsOf_mem_relativeDimensionAtLELocus n q hq
  -- Then refine that open neighbourhood to a Zariski basic open around the same point.
  obtain ⟨_, ⟨g, rfl⟩, hqg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.1.2 q U.2
  refine ⟨g, hqg, ?_⟩
  intro q' hq'
  exact hU q' (hgU hq')

/-- Helper for Chap10 Lemma 10 136 11: relative-GCI for a mapped displayed quotient transports
back to the tensor base change of the original displayed quotient. -/
private theorem isRelativeGlobalCompleteIntersection_baseChangeQuotient_of_relationLifts
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n c : ℕ} (fA : Fin c → MvPolynomial (Fin n) A)
    (fB : Fin c → MvPolynomial (Fin n) B)
    (hf : ∀ i, MvPolynomial.map (algebraMap A B) (fA i) = fB i)
    (hB : IsRelativeGlobalCompleteIntersection B
      (MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range fB))) :
    IsRelativeGlobalCompleteIntersection B
      (B ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))) := by
  -- Identify the tensor quotient with the displayed quotient and transport the owner predicate
  -- in the reverse direction along that algebra equivalence.
  rcases quotientBaseChangeEquiv_of_relationLifts fA fB hf with ⟨e⟩
  exact isRelativeGlobalCompleteIntersection_of_algEquiv hB e.symm

/-- Helper for Chap10 Lemma 10 136 11: relative-GCI for the tensor base change of a displayed
quotient transports to the displayed quotient with mapped relations. -/
private theorem isRelativeGlobalCompleteIntersection_quotient_of_baseChangeQuotient_relationLifts
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n c : ℕ} (fA : Fin c → MvPolynomial (Fin n) A)
    (fB : Fin c → MvPolynomial (Fin n) B)
    (hf : ∀ i, MvPolynomial.map (algebraMap A B) (fA i) = fB i)
    (hbase : IsRelativeGlobalCompleteIntersection B
      (B ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)))) :
    IsRelativeGlobalCompleteIntersection B
      (MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range fB)) := by
  -- Use the same quotient/base-change equivalence, now transporting in the forward direction.
  rcases quotientBaseChangeEquiv_of_relationLifts fA fB hf with ⟨e⟩
  exact isRelativeGlobalCompleteIntersection_of_algEquiv hbase e

/-- Helper for Chap10 Lemma 10 136 11: a presentation-level relative-GCI witness remains a
relative-GCI witness after arbitrary base change. -/
private theorem presentationRelativeGCI_baseChange
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S]
    {n c : ℕ} {P : Algebra.Presentation A S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    (P.baseChange B).IsRelativeGlobalCompleteIntersection := by
  intro p' hp'
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) p'
  let Pp : Algebra.Presentation p.asIdeal.ResidueField (p.asIdeal.Fiber S) (Fin n) (Fin c) :=
    P.baseChange p.asIdeal.ResidueField
  let e : p'.asIdeal.Fiber (B ⊗[A] S) ≃ₐ[p'.asIdeal.ResidueField]
      p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    -- Transport a prime of the new fiber to the scalar-extended old fiber, then contract it.
    rcases hp' with ⟨q'⟩
    let j :
        p.asIdeal.Fiber S →ₐ[p.asIdeal.ResidueField]
          p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.includeRight
    let qTensor :
        PrimeSpectrum
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S)) :=
      (PrimeSpectrum.comapEquiv e.toRingEquiv) q'
    exact ⟨PrimeSpectrum.comap j.toRingHom qTensor⟩
  haveI : Algebra.FinitePresentation p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    simpa [Pp] using Pp.finitePresentation_of_isFinite
  haveI : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  -- Compare the new fiber with the old one after extending scalars between residue fields.
  calc
    ringKrullDim (p'.asIdeal.Fiber (B ⊗[A] S))
        = ringKrullDim
            (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S)) := by
          simpa using (ringKrullDim_eq_of_ringEquiv (e := e.toRingEquiv))
    _ = ringKrullDim (p.asIdeal.Fiber S) := by
          symm
          exact ringKrullDim_tensorProduct_eq_of_fieldExtension
    _ = P.dimension := hP p hp_nonempty
    _ = (P.baseChange B).dimension := by
          simp [Algebra.Presentation.dimension]

/-- Helper for Chap10 Lemma 10 136 11: intrinsic relative-GCI is stable under arbitrary base
change. -/
private theorem isRelativeGlobalCompleteIntersection_baseChange
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S]
    (hS : IsRelativeGlobalCompleteIntersection A S) :
    IsRelativeGlobalCompleteIntersection B (B ⊗[A] S) := by
  -- Unpack the intrinsic owner, base-change its concrete presentation, and repack the result.
  rcases hS.exists_presentation with ⟨n, c, P, hP⟩
  exact Algebra.Presentation.toIsRelativeGlobalCompleteIntersection
    (presentationRelativeGCI_baseChange (B := B) hP)

/-- Helper for Chap10 Lemma 10 136 11: relative-GCI for a displayed quotient base-changes to the
displayed quotient cut out by the mapped relations. -/
private theorem isRelativeGlobalCompleteIntersection_mappedQuotient_of_relationLifts
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {n c : ℕ} (fA : Fin c → MvPolynomial (Fin n) A)
    (fB : Fin c → MvPolynomial (Fin n) B)
    (hf : ∀ i, MvPolynomial.map (algebraMap A B) (fA i) = fB i)
    (hA : IsRelativeGlobalCompleteIntersection A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))) :
    IsRelativeGlobalCompleteIntersection B
      (MvPolynomial (Fin n) B ⧸ Ideal.span (Set.range fB)) := by
  -- First base-change the owner predicate, then rewrite the tensor quotient to the displayed
  -- quotient in the target coefficients.
  have hbase : IsRelativeGlobalCompleteIntersection B
      (B ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))) :=
    isRelativeGlobalCompleteIntersection_baseChange (B := B) hA
  rcases quotientBaseChangeEquiv_of_relationLifts fA fB hf with ⟨e⟩
  exact isRelativeGlobalCompleteIntersection_of_algEquiv hbase e

/-- Helper for Chap10 Lemma 10 136 11: the bad base-prime locus of a presentation is the set of
nonempty fibers whose Krull dimension is not the presentation dimension. -/
private def presentationBadBaseLocus
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {m d : ℕ}
    (P : Algebra.Presentation A S (Fin m) (Fin d)) : Set (PrimeSpectrum A) :=
  fun p ↦ Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) ∧
    ringKrullDim (p.asIdeal.Fiber S) ≠ P.dimension

/-- Helper for Chap10 Lemma 10 136 11: an empty bad base-prime locus upgrades a presentation to
the intrinsic relative global complete intersection owner. -/
private theorem isRelativeGlobalCompleteIntersection_of_empty_presentationBadBaseLocus
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {m d : ℕ}
    {P : Algebra.Presentation A S (Fin m) (Fin d)}
    (hempty : presentationBadBaseLocus P = ∅) :
    Algebra.IsRelativeGlobalCompleteIntersection A S := by
  classical
  -- The presentation-level owner asks for exactly the negation of membership in the bad locus.
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P) ?_
  intro p hp
  by_contra hdim
  have hbad : p ∈ presentationBadBaseLocus P := And.intro hp hdim
  rw [hempty] at hbad
  exact hbad.elim

/-- Helper for Chap10 Lemma 10 136 11: a presentation-level relative-GCI witness has no bad
base primes for the associated fiber-dimension locus. -/
private theorem presentationBadBaseLocus_eq_empty_of_isRelativeGlobalCompleteIntersection
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {m d : ℕ}
    {P : Algebra.Presentation A S (Fin m) (Fin d)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    presentationBadBaseLocus P = ∅ := by
  -- The bad locus records exactly the primes where the presentation-level dimension formula
  -- fails, so the presentation witness rules out every point of the locus.
  ext p
  constructor
  · intro hp
    exact (hp.2 (hP p hp.1)).elim
  · intro hp
    exact hp.elim

/-- Helper for Chap10 Lemma 10 136 11: the intrinsic relative-GCI owner supplies a presentation
whose associated bad base-prime locus is empty. -/
private theorem exists_presentation_with_empty_bad_locus_of_relativeGCI
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (hS : Algebra.IsRelativeGlobalCompleteIntersection A S) :
    ∃ (m d : ℕ) (P : Algebra.Presentation A S (Fin m) (Fin d)),
      P.IsRelativeGlobalCompleteIntersection ∧ presentationBadBaseLocus P = ∅ := by
  -- Unpack the owner presentation, then translate its fiber-dimension formula into the
  -- bad-locus normal form needed for the finite-stage descent step.
  rcases hS.exists_presentation with ⟨m, d, P, hP⟩
  exact ⟨m, d, P, hP,
    presentationBadBaseLocus_eq_empty_of_isRelativeGlobalCompleteIntersection hP⟩

/-- Helper for Chap10 Lemma 10 136 11: radical containment of the distinguished element in the
ideal generated by the vanishing generators makes a basic constructible piece empty. -/
private theorem basicConstructibleSetData_eq_empty_of_mem_radical
    {A : Type u} [CommRing A] (C : PrimeSpectrum.BasicConstructibleSetData A)
    (hC : C.f ∈ (Ideal.span (Set.range C.g)).radical) :
    C.toSet = ∅ := by
  -- A point of `V(g) \ V(f)` would be a prime containing all `gᵢ` but not `f`; the radical
  -- containment forces that same prime to contain `f`, giving the contradiction.
  ext p
  constructor
  · intro hp
    rw [PrimeSpectrum.BasicConstructibleSetData.toSet] at hp
    have hspan_le : Ideal.span (Set.range C.g) ≤ p.asIdeal := by
      rw [Ideal.span_le]
      intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hp.1 ⟨i, rfl⟩
    have hfmem : C.f ∈ p.asIdeal :=
      (p.isPrime.radical_le_iff.mpr hspan_le) hC
    have hfzero : p ∈ PrimeSpectrum.zeroLocus ({C.f} : Set A) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact hfmem
    exact hp.2 hfzero
  · intro hp
    exact hp.elim

/-- Helper for Chap10 Lemma 10 136 11: if the image of a basic constructible piece under a ring
map is empty, then the image of its distinguished element lies in the radical of the ideal
generated by the mapped vanishing generators. -/
private theorem basicConstructibleSetData_mem_radical_of_map_empty
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (C : PrimeSpectrum.BasicConstructibleSetData A)
    (hC : (C.map φ).toSet = ∅) :
    φ C.f ∈ (Ideal.span (Set.range (φ ∘ C.g))).radical := by
  -- Empty difference is first rewritten as the subset `V(φg) ⊆ V(φf)`, then the standard
  -- prime-spectrum Galois connection turns that subset into radical membership.
  have hsubset :
      PrimeSpectrum.zeroLocus (Set.range (C.map φ).g) ⊆
        PrimeSpectrum.zeroLocus ({(C.map φ).f} : Set B) := by
    intro p hp
    by_contra hf
    have hpC : p ∈ (C.map φ).toSet := by
      rw [PrimeSpectrum.BasicConstructibleSetData.toSet]
      exact ⟨hp, hf⟩
    rw [hC] at hpC
    exact hpC.elim
  have hsubsetIdeal :
      PrimeSpectrum.zeroLocus (Ideal.span (Set.range (C.map φ).g) : Set B) ⊆
        PrimeSpectrum.zeroLocus (Ideal.span ({(C.map φ).f} : Set B) : Set B) := by
    simpa [PrimeSpectrum.zeroLocus_span] using hsubset
  have hle : Ideal.span ({(C.map φ).f} : Set B) ≤
      (Ideal.span (Set.range (C.map φ).g)).radical :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
      (Ideal.span (Set.range (C.map φ).g))
      (Ideal.span ({(C.map φ).f} : Set B))).mp hsubsetIdeal
  have hfmem : (C.map φ).f ∈ (Ideal.span (Set.range (C.map φ).g)).radical :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  simpa [PrimeSpectrum.BasicConstructibleSetData.map, Function.comp_def] using hfmem

/-- Helper for Chap10 Lemma 10 136 11: relations lifted from `A` to a larger coefficient
subalgebra still map to the prescribed ambient relations in `R`. -/
private theorem mappedRelations_inclusion_to_ambient
    {n c : ℕ} {A B : Subalgebra ℤ R} (hAB : A ≤ B)
    (fA : Fin c → MvPolynomial (Fin n) A)
    (f : Fin c → MvPolynomial (Fin n) R)
    (hfA : ∀ i, MvPolynomial.map A.val (fA i) = f i) :
    ∀ i, MvPolynomial.map B.val
        (MvPolynomial.map (Subalgebra.inclusion hAB).toRingHom (fA i)) = f i := by
  intro i
  -- Compose the coefficient maps through the larger subalgebra, then use the original ambient
  -- lift equality.
  exact (map_relationLift_inclusion hAB (fA i)).trans (hfA i)

/-- Helper for Chap10 Lemma 10 136 11: if the displayed quotient over a coefficient stage becomes
relative-GCI after base change to the ambient ring, then it spreads to a larger finite type
`ℤ`-subalgebra. -/
private theorem existsRelativeGCIQuotientFiniteStage_of_baseChange
    {n c : ℕ} {A : Subalgebra ℤ R} [Algebra A R]
    (hA : Algebra.FiniteType ℤ A)
    (fA : Fin c → MvPolynomial (Fin n) A)
    [hModule : Module A (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))]
    [hTensorComm : CommRing (R ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)))]
    [hTensorAlgebra : Algebra R
      (R ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)))]
    (f : Fin c → MvPolynomial (Fin n) R)
    (hfA : ∀ i, MvPolynomial.map A.val (fA i) = f i)
    (hGCIBase : IsRelativeGlobalCompleteIntersection R
      (R ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)))) :
    ∃ (R₀ : Subalgebra ℤ R) (_ : Algebra.FiniteType ℤ R₀)
      (f₀ : Fin c → MvPolynomial (Fin n) R₀),
        (∀ i, MvPolynomial.map R₀.val (f₀ i) = f i) ∧
          IsRelativeGlobalCompleteIntersection R₀
            (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)) := by
  -- Route correction: the generic owner-level descent lemma used in prior attempts returned a
  -- tensor product with existential ring/module spellings, which blocks transport to the
  -- displayed quotient. The remaining source step should descend the displayed quotient itself:
  -- choose a finite bounded-locus cover after ambient base change, descend the unit-ideal
  -- relation to a larger coefficient subalgebra, and assemble the relative-GCI witness directly
  -- for the mapped relations.
  -- TODO: prove the finite-stage descent certificate in displayed-quotient normal form; the
  -- verified base-change and quotient-transport adapters above reduce the remaining gap to
  -- descending the finite unit cover and bounded relative-dimension locus.
  sorry

/-- Helper for Chap10 Lemma 10 136 11: relative global complete intersection of a displayed
quotient spreads from the ambient ring to some finite type `ℤ`-subalgebra containing a fixed
finite coefficient stage. -/
private theorem relativeGCIQuotient_spreads_from_coeffSubalgebra
    {n c : ℕ} {A : Subalgebra ℤ R} (hA : Algebra.FiniteType ℤ A)
    (fA : Fin c → MvPolynomial (Fin n) A)
    (f : Fin c → MvPolynomial (Fin n) R)
    (hfA : ∀ i, MvPolynomial.map A.val (fA i) = f i)
    (hfgci :
      IsRelativeGlobalCompleteIntersection R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    ∃ (R₀ : Subalgebra ℤ R) (_ : Algebra.FiniteType ℤ R₀)
      (f₀ : Fin c → MvPolynomial (Fin n) R₀),
        (∀ i, MvPolynomial.map R₀.val (f₀ i) = f i) ∧
          IsRelativeGlobalCompleteIntersection R₀
            (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)) := by
  -- Route correction: the previous owner-level descent placeholder has been removed. We now keep
  -- only the verified setup: the coefficient-stage quotient base-changes to the ambient quotient.
  let S_A := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)
  letI : Algebra A (MvPolynomial (Fin n) A) := inferInstance
  letI : Module A (MvPolynomial (Fin n) A) := Algebra.toModule
  letI : Algebra.FinitePresentation A (MvPolynomial (Fin n) A) := inferInstance
  letI : Module (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A) := Semiring.toModule
  letI : CommRing S_A := inferInstance
  letI : Algebra A S_A := inferInstance
  letI : Module A S_A := Algebra.toModule
  letI : Algebra.FinitePresentation A S_A := finitePresentation_displayedQuotient fA
  letI : Algebra A R := A.val.toRingHom.toAlgebra
  letI : Module A R := Algebra.toModule
  have hGCIBase : IsRelativeGlobalCompleteIntersection R (R ⊗[A] S_A) := by
    -- The ambient displayed quotient is the mapped-relation quotient of the coefficient stage, so
    -- the named adapter transports its RGCI structure to the tensor base change.
    refine isRelativeGlobalCompleteIntersection_baseChangeQuotient_of_relationLifts
      (A := A) (B := R) fA f ?_ hfgci
    intro i
    simpa using hfA i
  -- The remaining finite-stage work is the source spreading step for this fixed displayed
  -- quotient: enlarge the coefficient stage until the base-changed RGCI structure descends.
  let hModule : Module A (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)) :=
    Algebra.toModule
  let hTensorComm : CommRing (R ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))) :=
    inferInstance
  let hTensorAlgebra :
      Algebra R (R ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))) :=
    inferInstance
  letI : Module A (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA)) := hModule
  letI : CommRing (R ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))) :=
    hTensorComm
  letI : Algebra R (R ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fA))) :=
    hTensorAlgebra
  exact existsRelativeGCIQuotientFiniteStage_of_baseChange
      (hModule := hModule) (hTensorComm := hTensorComm) (hTensorAlgebra := hTensorAlgebra)
      hA fA f hfA hGCIBase

/- Domain-style sampling:
- primary domain: relative global complete intersections presented as explicit polynomial
  quotients, together with descent of coefficients to finite type `ℤ`-subalgebras;
- sampled owner declarations of the same kind:
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.exists_presentation`,
  `Algebra.instFinitePresentationOfIsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.localizationAway`;
- best owner abstraction:
  the property being descended is the canonical chapter owner
  `Algebra.IsRelativeGlobalCompleteIntersection`; this lemma remains `source-facing` because the
  Stacks item also keeps track of explicit descended relations `f₀`, but those relations should
  serve only to describe the descended quotient ring, not to replace the owner-level predicate by
  one unpacked field of it;
- primitive vs. derived:
  the primitive source-facing data are the descended coefficient subalgebra and the lifted
  relations `f₀`; the fact that the descended quotient is a relative global complete intersection
  is the main owner-level conclusion, while any particular fiber-dimension formula for that
  displayed presentation is derived API.

Source/core/bridge triage:
- `source-facing`: descend the explicit quotient presentation by finitely many relations to a
  finite type `ℤ`-subalgebra;
- `core/canonical`: `Algebra.IsRelativeGlobalCompleteIntersection`;
- `bridge/view`: the explicit quotient description
  `MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)` of that descended model.
-/

-- Proof sketch: let `R₀` be the `ℤ`-subalgebra of `R` generated by the finitely many coefficients
-- of the `f i`. Choose lifts `f₀ i` of the relations to `MvPolynomial (Fin n) R₀`. For each
-- prime of the descended quotient, reduce to the owner-level relative-global-complete-
-- intersection condition on a finite type stage and enlarge `R₀` until the descended quotient
-- itself carries that owner predicate.
/-- Lemma 10.136.11: if the displayed quotient
`R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete intersection over `R`, then the
finitely many relations `fᵢ` descend to a finite type `ℤ`-subalgebra `R₀ ⊆ R` such that the
descended quotient over `R₀` is again a relative global complete intersection. -/
@[stacks 00SU]
theorem exists_finiteType_zSubalgebra_of_relativeGCIQuotient
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (hfgci :
      IsRelativeGlobalCompleteIntersection R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) :
    ∃ (R₀ : Subalgebra ℤ R) (_ : Algebra.FiniteType ℤ R₀)
      (f₀ : Fin c → MvPolynomial (Fin n) R₀),
        (∀ i, MvPolynomial.map R₀.val (f₀ i) = f i) ∧
          IsRelativeGlobalCompleteIntersection R₀
            (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range f₀)) := by
  -- First descend only the finitely many displayed coefficients; this is the elementary part of
  -- the spreading argument and fixes the initial finite type stage.
  obtain ⟨Rcoeff, hRcoeff, fcoeff, hfcoeff⟩ :=
    exists_coeffSubalgebra_lifts_relations (R := R) f
  -- The remaining source-facing spreading helper may enlarge this coefficient stage and then
  -- provides exactly the descended quotient required by the statement.
  exact relativeGCIQuotient_spreads_from_coeffSubalgebra hRcoeff fcoeff f hfcoeff hfgci

end Algebra

end
