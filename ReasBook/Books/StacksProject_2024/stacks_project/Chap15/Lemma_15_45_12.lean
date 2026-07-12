import StacksProject_2024.Chap15.Lemma_15_105_14
import StacksProject_2024.Chap10.Lemma_10_143_5
import StacksProject_2024.Chap15.Lemma_15_18_2
import StacksProject_2024.Chap15.Lemma_15_105_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

namespace PrimeSpectrum

/- Domain triage:
* primary domain: fibers `κ(p) ⊗[A] B`, primes of `B` lying over `p`, and their residue fields;
* source-facing items in this file: finiteness of the fiber over `p`, the resulting product
  decomposition of the fiber ring, and separable algebraicity of the residue-field extensions;
* sampled owners for the refinement:
  `RingHom.IsFilteredColimitOfEtale`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `Ideal.primesOver`,
  `Ideal.Fiber`,
  `IsArtinianRing.equivPi`;
* bridge/view data removed by this refinement: arbitrary indexing types, bijections for the
  product decomposition, and the existence-only wrapper around the decomposition map. The
  canonical owner data are `Ideal.Fiber p B` and `p.primesOver B`; the primitive bridge data are
  the coordinate maps from the fiber ring to each residue field over `p`, and part `(2)` derives
  the product map from those owners instead of treating the whole product packaging as primitive.

Primitive data are `A`, `B`, the filtered-colimit-of-étale hypothesis on `algebraMap A B`, and the
chosen prime `p : PrimeSpectrum A`. The product decomposition in part `(2)` is therefore stated
directly over the owner set `p.asIdeal.primesOver B`, rather than via an auxiliary `ι` and a
reindexing bijection, with the canonical product map exposed as data and bijectivity as the
source-facing theorem. -/

/-- Helper for Lemma 15.45.12: in an absolutely flat ring, the factorization
`x = x^2 * y` lowers the nilpotence exponent by one. -/
lemma pow_succ_eq_zero_of_square_factor
    {R : Type*} [CommRing R] {x y : R} (hy : x = x ^ 2 * y) {n : ℕ}
    (hn : x ^ (n + 2) = 0) :
    x ^ (n + 1) = 0 := by
  -- Rewrite one copy of `x` using the square factorization and regroup powers.
  calc
    x ^ (n + 1) = x ^ n * x := by
      rw [pow_add]
      simp
    _ = x ^ n * (x ^ 2 * y) := by rw [← hy]
    _ = x ^ (n + 2) * y := by
      rw [pow_two]
      ring
    _ = 0 := by simp [hn]

/-- Helper for Lemma 15.45.12: quotients of absolutely flat rings are absolutely flat. -/
lemma quotient_isAbsolutelyFlatRing_of_isAbsolutelyFlatRing
    {R : Type*} [CommRing R] [IsAbsolutelyFlatRing R] (I : Ideal R) :
    IsAbsolutelyFlatRing (R ⧸ I) := by
  refine ⟨fun x ↦ ?_⟩
  -- Lift the quotient element to `R`, factor it there, and descend the factorization.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, hs⟩ := IsAbsolutelyFlatRing.exists_factor (A := R) r
  refine ⟨Ideal.Quotient.mk I s, ?_⟩
  simpa using congrArg (Ideal.Quotient.mk I) hs

/-- Helper for Lemma 15.45.12: an absolutely flat domain is a field. -/
lemma isField_of_isDomain_of_isAbsolutelyFlatRing
    {R : Type*} [CommRing R] [IsDomain R] [IsAbsolutelyFlatRing R] :
    IsField R := by
  refine IsField.mk ?_ (fun x y ↦ mul_comm x y) ?_
  · exact ⟨0, 1, zero_ne_one⟩
  · intro a ha
    obtain ⟨b, hb⟩ := IsAbsolutelyFlatRing.exists_factor (A := R) a
    refine ⟨b, ?_⟩
    have hab : a * b = 1 := by
      apply mul_left_cancel₀ ha
      calc
        a * (a * b) = a ^ 2 * b := by ring
        _ = a := by simpa [pow_two] using hb.symm
        _ = a * 1 := by simp
    simpa [mul_comm] using hab

/-- Helper for Lemma 15.45.12: absolutely flat commutative rings are zero-dimensional. -/
lemma krullDimLEZero_of_isAbsolutelyFlatRing_local
    {R : Type*} [CommRing R] [IsAbsolutelyFlatRing R] :
    Ring.KrullDimLE 0 R := by
  refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
  letI : I.IsPrime := hI
  letI : IsAbsolutelyFlatRing (R ⧸ I) :=
    quotient_isAbsolutelyFlatRing_of_isAbsolutelyFlatRing I
  let hfield : IsField (R ⧸ I) := isField_of_isDomain_of_isAbsolutelyFlatRing (R := R ⧸ I)
  letI : Field (R ⧸ I) := IsField.toField hfield
  -- The quotient map has maximal kernel because its codomain is a field.
  have hker : (RingHom.ker (Ideal.Quotient.mk I)).IsMaximal := by
    exact RingHom.ker_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  simpa using hker

/-- Helper for Lemma 15.45.12: absolutely flat commutative rings are reduced. -/
lemma isReduced_of_isAbsolutelyFlatRing_local
    {R : Type*} [CommRing R] [IsAbsolutelyFlatRing R] :
    IsReduced R := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := IsAbsolutelyFlatRing.exists_factor (A := R) x
  let hnil :
      ∀ m : ℕ, x ^ (m + 1) = 0 → x = 0 := by
    intro m
    induction m with
    | zero =>
        intro hm
        simpa using hm
    | succ m ih =>
        intro hm
        exact ih (pow_succ_eq_zero_of_square_factor hy hm)
  rcases hx with ⟨n, hn⟩
  cases n with
  | zero =>
      have h1 : (1 : R) = 0 := by simpa using hn
      have hsub : Subsingleton R := by
        simpa [subsingleton_iff_zero_eq_one] using h1.symm
      letI : Subsingleton R := hsub
      exact Subsingleton.elim _ _
  | succ n =>
      exact hnil n hn

/-- Helper for Lemma 15.45.12: a weakly étale algebra over a field is absolutely flat because
every singleton-generated subalgebra is étale, hence a finite product of fields. -/
lemma isAbsolutelyFlatRing_of_isWeaklyEtale_over_field
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [Algebra.IsWeaklyEtale K S] :
    IsAbsolutelyFlatRing S := by
  refine ⟨fun x ↦ ?_⟩
  let A : Subalgebra K S := Algebra.adjoin K ({x} : Set S)
  have hAfg : A.FG := by
    -- The singleton-generated subalgebra is finite type, hence finitely generated.
    rw [Subalgebra.fg_iff_finiteType A]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  have hAet : Algebra.Etale K A := etale_of_fg_subalgebra_of_isWeaklyEtale A hAfg
  obtain ⟨ι, hι, T, hField, hAlg, e, _hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp hAet
  let y : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  letI : ∀ i, IsAbsolutelyFlatRing (T i) := fun i ↦ inferInstance
  letI : IsAbsolutelyFlatRing (∀ i, T i) := inferInstance
  obtain ⟨z, hz⟩ := IsAbsolutelyFlatRing.exists_factor (A := ∀ i, T i) (e y)
  refine ⟨((e.symm z : A) : S), ?_⟩
  -- Transport the product-side factorization back through the algebra equivalence and forget to `S`.
  have hy' : y = y ^ 2 * e.symm z := by
    simpa using congrArg e.symm hz
  exact congrArg (fun t : A ↦ (t : S)) hy'

/-- Helper for Lemma 15.45.12: the fiber over `p` is Artinian because the weakly étale fiber is
absolutely flat, hence zero-dimensional, and the hypothesis already makes it Noetherian. -/
lemma fiber_isReduced_of_isFilteredColimitOfEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) :
    IsReduced (p.asIdeal.Fiber B) := by
  -- Route correction: avoid the broken `15_105_8` import chain and re-run the source proof
  -- locally on the fiber over `κ(p)`.
  let hweak : Algebra.IsWeaklyEtale A B :=
    isWeaklyEtale_of_isFilteredColimitOfEtale hcolim
  let _ : Algebra.IsWeaklyEtale p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
    hweak.baseChange
  let _ : IsAbsolutelyFlatRing (p.asIdeal.Fiber B) :=
    isAbsolutelyFlatRing_of_isWeaklyEtale_over_field
      (K := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber B)
  -- Reducedness is the nilpotent-free consequence of the absolute-flat factorization criterion.
  exact isReduced_of_isAbsolutelyFlatRing_local (R := p.asIdeal.Fiber B)

/-- Helper for Lemma 15.45.12: the fiber over `p` is Artinian because the weakly étale fiber is
absolutely flat, hence zero-dimensional, and the hypothesis already makes it Noetherian. -/
lemma fiber_isArtinian_of_isFilteredColimitOfEtale_of_isNoetherianFiber
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)] :
    IsArtinianRing (p.asIdeal.Fiber B) := by
  -- Route correction: the same field-fiber argument gives absolute flatness locally, so the
  -- Noetherian fiber is Artinian once we convert absolute flatness to dimension `≤ 0`.
  let hweak : Algebra.IsWeaklyEtale A B :=
    isWeaklyEtale_of_isFilteredColimitOfEtale hcolim
  let _ : Algebra.IsWeaklyEtale p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
    hweak.baseChange
  let _ : IsAbsolutelyFlatRing (p.asIdeal.Fiber B) :=
    isAbsolutelyFlatRing_of_isWeaklyEtale_over_field
      (K := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber B)
  -- Zero-dimensionality now comes from the absolute-flat quotient/domain argument.
  exact
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2
      ⟨inferInstance, krullDimLEZero_of_isAbsolutelyFlatRing_local (R := p.asIdeal.Fiber B)⟩

/-- Helper for Lemma 15.45.12: maximal ideals of the Artinian fiber are in bijection with the
primes of `B` lying over `p`. -/
noncomputable def fiber_maximalSpectrum_equiv_primesOver
    (_hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)] :
    MaximalSpectrum (p.asIdeal.Fiber B) ≃ p.asIdeal.primesOver B :=
  (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := p.asIdeal.Fiber B)).symm.trans
    (PrimeSpectrum.primesOverOrderIsoFiber A B p.asIdeal).symm.toEquiv

/-- Helper for Lemma 15.45.12: the prime of `B` attached to a maximal ideal of the fiber has the
expected comap along `κ(p) ⊗[A] B ← B`. -/
lemma fiber_primesOver_comap_eq
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)]
    (I : MaximalSpectrum (p.asIdeal.Fiber B)) :
    let q : p.asIdeal.primesOver B := fiber_maximalSpectrum_equiv_primesOver hcolim p I
    q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := by
  -- The maximal ideal `I` is first viewed as a prime of the fiber; the canonical fiber/primes-over
  -- order isomorphism records the corresponding prime of `B` by comap along `includeRight`.
  rfl

/-- Helper for Lemma 15.45.12: each Artinian fiber factor `F ⧸ I` identifies with the residue
field of the corresponding prime of `B` over `p`. -/
noncomputable def fiber_component_quotientEquiv_residueField
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)]
    (I : MaximalSpectrum (p.asIdeal.Fiber B)) :
    (p.asIdeal.Fiber B ⧸ I.asIdeal) ≃+*
      (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1.ResidueField := by
  let q : p.asIdeal.primesOver B := fiber_maximalSpectrum_equiv_primesOver hcolim p I
  have hq' :
      q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := by
    simpa [q] using fiber_primesOver_comap_eq hcolim p I
  let eQuot :
      (p.asIdeal.Fiber B ⧸ I.asIdeal) ≃+* I.asIdeal.ResidueField :=
    RingEquiv.ofBijective (algebraMap _ I.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField I.asIdeal)
  let eResidue :
      q.1.ResidueField ≃+* I.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map q.1 I.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hq')
      ((p.asIdeal.surjectiveOnStalks_residueField.baseChange').residueFieldMap_bijective
        q.1 I.asIdeal hq')
  -- We first pass from the quotient to the fiber-prime residue field, then back to `κ(q)`.
  exact eQuot.trans eResidue.symm

/-- Helper for Lemma 15.45.12: equal prime ideals in the same ring have canonically equivalent
residue fields. -/
noncomputable def residueFieldCongrOfEq
    {R : Type*} [CommRing R] {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I = J) :
    I.ResidueField ≃+* J.ResidueField := by
  cases h
  exact RingEquiv.refl _

/-- Helper for Lemma 15.45.12: residue-field maps commute with the canonical transport induced by
equality of source prime ideals. -/
lemma residueField_map_apply_congrOfEq
    {R S : Type*} [CommRing R] [CommRing S]
    {I J : Ideal R} [I.IsPrime] [J.IsPrime] {K : Ideal S} [K.IsPrime]
    (f : R →+* S) (hIJ : I = J) (hIK : I = Ideal.comap f K) (hJK : J = Ideal.comap f K)
    (x : I.ResidueField) :
    Ideal.ResidueField.map J K f hJK (residueFieldCongrOfEq hIJ x) =
      Ideal.ResidueField.map I K f hIK x := by
  cases hIJ
  simp [residueFieldCongrOfEq]

/-- Helper for Lemma 15.45.12: two equality proofs between the same prime ideals induce the same
transport on residue-field elements. -/
lemma residueFieldCongrOfEq_apply_eq
    {R : Type*} [CommRing R] {I J : Ideal R} [I.IsPrime] [J.IsPrime]
    (h₁ h₂ : I = J) (x : I.ResidueField) :
    residueFieldCongrOfEq h₁ x = residueFieldCongrOfEq h₂ x := by
  cases h₁
  cases h₂
  rfl

/-- Helper for Lemma 15.45.12: after reindexing the Artinian fiber factors by the canonical
bijection with primes over `p`, the `q`-factor identifies with `κ(q)`. -/
noncomputable def fiber_reindexedComponent_quotientEquiv_residueField
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)]
    (q : p.asIdeal.primesOver B) :
    (p.asIdeal.Fiber B ⧸ ((fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q).asIdeal) ≃+*
      q.1.ResidueField := by
  let I : MaximalSpectrum (p.asIdeal.Fiber B) :=
    (fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q
  let eComp :
      (p.asIdeal.Fiber B ⧸ ((fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q).asIdeal) ≃+*
        (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1.ResidueField := by
    change (p.asIdeal.Fiber B ⧸ I.asIdeal) ≃+*
      (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1.ResidueField
    exact fiber_component_quotientEquiv_residueField hcolim p I
  have hq :
      (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1 = q.1 := by
    exact congrArg Subtype.val
      ((fiber_maximalSpectrum_equiv_primesOver hcolim p).apply_symm_apply q)
  -- After fixing `I = e.symm q`, only the codomain needs a residue-field transport.
  exact eComp.trans (residueFieldCongrOfEq hq)

/- Lemma 15.45.12 (1): if `B` is a filtered colimit of étale `A`-algebras and the fiber ring
`p.asIdeal.Fiber B` is Noetherian, then only finitely many primes of `B` lie over `p`.

 Proof sketch: base change the filtered-colimit-of-étale presentation of `B` along
 `A → κ(p)` to see that the fiber ring `p.asIdeal.Fiber B` is a filtered colimit of étale
 `κ(p)`-algebras. Each stage is a finite product of finite separable field extensions, hence has
 discrete spectrum. The Noetherian fiber ring therefore has finitely many primes, and
 `PrimeSpectrum.primesOverOrderIsoFiber` identifies those primes with the primes of `B` over `p`. -/
theorem primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)] :
    Finite (p.asIdeal.primesOver B) := by
  -- The spectrum of the Artinian fiber is finite, and the canonical order isomorphism
  -- transports this finiteness back to the primes of `B` over `p`.
  letI : IsArtinianRing (p.asIdeal.Fiber B) :=
    fiber_isArtinian_of_isFilteredColimitOfEtale_of_isNoetherianFiber hcolim p
  letI : Finite (PrimeSpectrum (p.asIdeal.Fiber B)) := inferInstance
  exact
    Finite.of_equiv (PrimeSpectrum (p.asIdeal.Fiber B))
      (PrimeSpectrum.primesOverOrderIsoFiber A B p.asIdeal).symm.toEquiv

end PrimeSpectrum

/-- Helper for Lemma 15.45.12: the residue field of the zero ideal in a field is canonically the
field itself. -/
noncomputable theorem field_botResidueFieldAlgEquiv_local (K : Type u) [Field K] :
    K ≃ₐ[K] ((⊥ : Ideal K).ResidueField) := by
  -- Realize `κ((0))` as a fraction ring of `K`, then compare the two fraction-ring models.
  letI : IsFractionRing K ((⊥ : Ideal K).ResidueField) := by
    let e : K ≃ₐ[K] K ⧸ (⊥ : Ideal K) := (AlgEquiv.quotientBot K K).symm
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap K ((⊥ : Ideal K).ResidueField) x =
      algebraMap (K ⧸ (⊥ : Ideal K)) ((⊥ : Ideal K).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    rfl
  let eFracK : FractionRing K ≃ₐ[K] K := FractionRing.algEquiv K K
  let eFracResidue : FractionRing K ≃ₐ[K] ((⊥ : Ideal K).ResidueField) :=
    FractionRing.algEquiv K ((⊥ : Ideal K).ResidueField)
  exact eFracK.symm.trans eFracResidue

/-- Helper for Lemma 15.45.12: a prime of an étale algebra over a field has separable residue
field over the base field. -/
lemma prime_residueField_isSeparable_of_etale_over_field_local
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
    [Algebra.Etale K S] (r : Ideal S) [r.IsPrime] :
    Algebra.IsSeparable K r.ResidueField := by
  have hsepBot : Algebra.IsSeparable ((⊥ : Ideal K).ResidueField) r.ResidueField := by
    -- Apply the étale-away residue-field theorem with the witness `g = 1`.
    exact
      (residueField_finite_and_separable_of_exists_etale_away
        (R := K) (S := S) r
        ⟨1, by
            simpa [Ideal.ne_top_iff_one] using
              (Ideal.IsPrime.ne_top (I := r) inferInstance),
          inferInstance⟩).2
  -- Transport separability back along the canonical identification `K ≃ κ((0))`.
  rw [Algebra.isSeparable_iff] at hsepBot ⊢
  intro x
  exact IsSeparable.of_algHom
    (f := (field_botResidueFieldAlgEquiv_local K).toAlgHom) (hsepBot x)

/-- Helper for Lemma 15.45.12: a prime of a weakly étale algebra over a field has separable
residue field over the base field. -/
lemma residueField_isSeparable_of_isWeaklyEtale_over_field_local
    {K : Type u} {F : Type v} [Field K] [CommRing F] [Algebra K F]
    [Algebra.IsWeaklyEtale K F] (Q : Ideal F) [Q.IsPrime] :
    Algebra.IsSeparable K Q.ResidueField := by
  rw [Algebra.isSeparable_iff]
  intro x
  -- Capture the residue-field element by one ambient element and shrink to the singleton stage.
  obtain ⟨a, rfl⟩ := Q.algebraMap_residueField_surjective x
  let A₀ : Subalgebra K F := Algebra.adjoin K ({a} : Set F)
  let r : Ideal A₀ := Ideal.comap (A₀.val : A₀ →+* F) Q
  letI : r.IsPrime := by
    dsimp [r]
    infer_instance
  let a₀ : A₀ := ⟨a, Algebra.subset_adjoin (by simp)⟩
  have hA₀fg : A₀.FG := by
    -- The singleton-generated subalgebra is finite type, hence finitely generated.
    rw [Subalgebra.fg_iff_finiteType A₀]
    exact Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton a)
  have hA₀et : Algebra.Etale K A₀ := by
    -- Weak étaleness over a field makes every finitely generated stage étale.
    exact etale_of_fg_subalgebra_of_isWeaklyEtale A₀ hA₀fg
  have hsepStage : Algebra.IsSeparable K r.ResidueField := by
    let _ : Algebra.Etale K A₀ := hA₀et
    -- Apply the field-case étale result to the stage prime `r`.
    exact
      prime_residueField_isSeparable_of_etale_over_field_local
        (K := K) (S := A₀) r
  have hmap :
      (Ideal.ResidueField.mapₐ r Q A₀.val rfl) (algebraMap A₀ r.ResidueField a₀) =
        algebraMap F Q.ResidueField a := by
    -- The chosen representative `a` maps compatibly from the stage quotient to the ambient one.
    exact Ideal.ResidueField.map_algebraMap r Q A₀.val rfl a₀
  -- Transport separability of the stage residue class across the canonical residue-field map.
  exact
    IsSeparable.of_algHom
      (f := Ideal.ResidueField.mapₐ r Q A₀.val rfl)
      (by
        simpa [hmap] using
          ((Algebra.isSeparable_iff.mp hsepStage) (algebraMap A₀ r.ResidueField a₀)))

/-- Helper for Lemma 15.45.12: the residue field of a prime over `p` is canonically equivalent to
the residue field of the corresponding prime of the fiber over `p`. -/
noncomputable theorem residueField_algEquiv_of_baseChange_fiber_prime_local
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) (qbar : PrimeSpectrum (p.Fiber B))
    (hqbar :
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qbar.asIdeal = q.1) :
    q.1.ResidueField ≃ₐ[p.ResidueField] qbar.asIdeal.ResidueField := by
  let e : q.1.ResidueField ≃+* qbar.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map q.1 qbar.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hqbar.symm)
      ((p.surjectiveOnStalks_residueField.baseChange').residueFieldMap_bijective
        q.1 qbar.asIdeal hqbar.symm)
  refine AlgEquiv.ofRingEquiv (f := e) ?_
  intro x
  -- Reduce scalar compatibility to elements coming from `A` and compare the two tensor factors.
  obtain ⟨a, rfl⟩ := p.algebraMap_residueField_surjective x
  change
    e (Ideal.ResidueField.map p q.1 (algebraMap A B) (q.1.over_def p)
      (algebraMap A p.ResidueField a)) =
      algebraMap p.ResidueField qbar.asIdeal.ResidueField (algebraMap A p.ResidueField a)
  rw [show e =
      Ideal.ResidueField.map q.1 qbar.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hqbar.symm from rfl]
  rw [Ideal.ResidueField.map_algebraMap q.1 qbar.asIdeal
    Algebra.TensorProduct.includeRight.toRingHom hqbar.symm ((algebraMap A B) a)]
  have hbase :
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) ((algebraMap A B) a) =
        (Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B)
          ((algebraMap A p.ResidueField) a) := by
    -- The two tensor-factor maps agree on the common base ring `A`.
    simpa using congrArg (fun f : A →+* p.Fiber B => f a)
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
        ((Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B).toRingHom.comp
            (algebraMap A p.ResidueField)) =
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B).toRingHom.comp
            (algebraMap A B))).symm
  calc
    algebraMap (p.Fiber B) qbar.asIdeal.ResidueField
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) ((algebraMap A B) a)) =
      algebraMap (p.Fiber B) qbar.asIdeal.ResidueField
        ((Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B)
          ((algebraMap A p.ResidueField) a)) := by
        exact congrArg (algebraMap (p.Fiber B) qbar.asIdeal.ResidueField) hbase
    _ =
      algebraMap p.ResidueField qbar.asIdeal.ResidueField (algebraMap A p.ResidueField a) := by
        rfl

namespace Ideal

/-- The canonical ring homomorphism from the fiber ring `p.Fiber B = κ(p) ⊗[A] B` to the product
of the residue fields of the primes of `B` lying over `p`, indexed by the canonical owner set
`p.primesOver B`. -/
noncomputable def fiberToPiResidueField (p : Ideal A) [p.IsPrime]
    (B : Type v) [CommRing B] [Algebra A B] :
    p.Fiber B →+* ∀ q : p.primesOver B, q.1.ResidueField :=
  let φ : ∀ q : p.primesOver B, p.Fiber B →+* q.1.ResidueField :=
    fun q ↦
      (Algebra.TensorProduct.lift
        (Ideal.ResidueField.mapₐ p q.1 (Algebra.ofId _ _) (q.1.over_def p))
        (IsScalarTower.toAlgHom _ _ _)
        (fun _ _ ↦ Commute.all _ _)).toRingHom
  Pi.ringHom φ

set_option maxHeartbeats 5000000 in
/-- Helper for Lemma 15.45.12: after fixing the fiber maximal ideal `I` corresponding to `q`, the
postcomposed `q`-coordinate agrees with the fiber algebra map on the `includeLeft` tensor
generator. -/
lemma fiberToPiResidueField_postcompose_comp_includeLeft
    (p : Ideal A) [p.IsPrime] (B : Type v) [CommRing B] [Algebra A B]
    (q : p.primesOver B) (I : MaximalSpectrum (p.Fiber B))
    (hq' : q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    (((Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq').comp
        ((Pi.evalRingHom (fun q : p.primesOver B => q.1.ResidueField) q).comp
          (p.fiberToPiResidueField B))).comp
        (Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B).toRingHom) =
      (algebraMap (p.Fiber B) I.asIdeal.ResidueField).comp
        (Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B).toRingHom := by
  -- The left branch of `TensorProduct.lift` is the scalar map from `κ(p)`, so the postcomposition
  -- is exactly the ambient `κ(p) → κ(I)` algebra map.
  ext x
  simp [Ideal.fiberToPiResidueField, RingHom.comp_assoc]
  have hx :
      (algebraMap A q.1.ResidueField) x =
        (algebraMap B q.1.ResidueField) ((algebraMap A B) x) := by
    exact (IsScalarTower.algebraMap_apply A B q.1.ResidueField x).symm
  rw [hx]
  have hmap :
      (Ideal.ResidueField.map q.1 I.asIdeal
          Algebra.TensorProduct.includeRight.toRingHom hq')
        ((algebraMap B q.1.ResidueField) ((algebraMap A B) x)) =
      (algebraMap (p.Fiber B) I.asIdeal.ResidueField)
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) ((algebraMap A B) x)) := by
    simpa using
      (Ideal.ResidueField.map_algebraMap q.1 I.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hq' ((algebraMap A B) x))
  have hbase :
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) ((algebraMap A B) x) =
        (Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B)
          ((algebraMap A p.ResidueField) x) := by
    -- The two tensor-factor maps agree on the image of the common base ring `A`.
    simpa using congrArg (fun f : A →+* p.Fiber B => f x)
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
        ((Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B).toRingHom.comp
            (algebraMap A p.ResidueField)) =
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B).toRingHom.comp
            (algebraMap A B))).symm
  calc
    (Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq')
        ((algebraMap B q.1.ResidueField) ((algebraMap A B) x)) =
      (algebraMap (p.Fiber B) I.asIdeal.ResidueField)
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) ((algebraMap A B) x)) := hmap
    _ =
      (algebraMap (p.Fiber B) I.asIdeal.ResidueField)
        ((algebraMap A p.ResidueField) x ⊗ₜ[A] 1) := by
        simpa [Algebra.TensorProduct.includeLeft_apply] using
          congrArg (algebraMap (p.Fiber B) I.asIdeal.ResidueField) hbase

/-- Helper for Lemma 15.45.12: after fixing the fiber maximal ideal `I` corresponding to `q`, the
postcomposed `q`-coordinate agrees with the fiber algebra map on the `includeRight` tensor
generator. -/
lemma fiberToPiResidueField_postcompose_comp_includeRight
    (p : Ideal A) [p.IsPrime] (B : Type v) [CommRing B] [Algebra A B]
    (q : p.primesOver B) (I : MaximalSpectrum (p.Fiber B))
    (hq' : q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    (((Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq').comp
        ((Pi.evalRingHom (fun q : p.primesOver B => q.1.ResidueField) q).comp
          (p.fiberToPiResidueField B))).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B).toRingHom) =
      (algebraMap (p.Fiber B) I.asIdeal.ResidueField).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B).toRingHom := by
  apply RingHom.ext
  intro b
  -- On the right tensor generator, the coordinate map is just the structural map to `κ(q)`.
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
  simp [Ideal.fiberToPiResidueField, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]

/-- Helper for Lemma 15.45.12: after fixing the fiber maximal ideal `I` corresponding to `q`,
postcomposing the canonical `q`-coordinate with the forward residue-field map is exactly the
algebra map from the fiber ring to `I`'s residue field. -/
lemma fiberToPiResidueField_postcompose_eq_algebraMap
    (p : Ideal A) [p.IsPrime] (B : Type v) [CommRing B] [Algebra A B]
    (q : p.primesOver B) (I : MaximalSpectrum (p.Fiber B))
    (hq' : q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    ((Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq').comp
        ((Pi.evalRingHom (fun q : p.primesOver B => q.1.ResidueField) q).comp
          (p.fiberToPiResidueField B))) =
      algebraMap (p.Fiber B) I.asIdeal.ResidueField :=
by
  let forwardMap : q.1.ResidueField →ₐ[A] I.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ q.1 I.asIdeal
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) hq'
  let sourceCoordinate : p.Fiber B →ₐ[A] q.1.ResidueField :=
    Algebra.TensorProduct.lift
      (Ideal.ResidueField.mapₐ p q.1 (Algebra.ofId A B) (q.1.over_def p))
      (IsScalarTower.toAlgHom A B q.1.ResidueField)
      (fun _ _ ↦ Commute.all _ _)
  let F : p.Fiber B →ₐ[A] I.asIdeal.ResidueField :=
    forwardMap.comp sourceCoordinate
  let G : p.Fiber B →ₐ[A] I.asIdeal.ResidueField :=
    AlgHom.restrictScalars A (Algebra.ofId (p.Fiber B) I.asIdeal.ResidueField)
  have hleft :
      F.comp (Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B) =
        G.comp (Algebra.TensorProduct.includeLeft : p.ResidueField →ₐ[A] p.Fiber B) := by
    -- The left generator is controlled by the base-ring compatibility of the two tensor factors.
    apply DFunLike.ext
    intro x
    simpa [F, G, forwardMap, sourceCoordinate, Ideal.fiberToPiResidueField, Pi.evalRingHom,
      RingHom.comp_assoc] using
      congrArg (fun f : p.ResidueField →+* I.asIdeal.ResidueField => f x)
        (fiberToPiResidueField_postcompose_comp_includeLeft
          (p := p) (B := B) q I hq')
  have hright :
      (AlgHom.restrictScalars A F).comp (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) =
        (AlgHom.restrictScalars A G).comp
          (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) := by
    -- The right generator follows directly from the defining formula of `TensorProduct.lift`.
    apply DFunLike.ext
    intro b
    simpa [F, G, forwardMap, sourceCoordinate, Ideal.fiberToPiResidueField, Pi.evalRingHom,
      RingHom.comp_assoc] using
      congrArg (fun f : B →+* I.asIdeal.ResidueField => f b)
        (fiberToPiResidueField_postcompose_comp_includeRight
          (p := p) (B := B) q I hq')
  -- Compare the two algebra maps on the tensor generators and conclude by the universal property.
  simpa [F, G, forwardMap, sourceCoordinate, Ideal.fiberToPiResidueField, RingHom.comp_assoc] using
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.ext hleft hright)

end Ideal

namespace PrimeSpectrum

/-- Helper for Lemma 15.45.12: reindex the Artinian product decomposition of the fiber along the
canonical bijection between maximal ideals of the fiber and primes of `B` over `p`. -/
noncomputable def fiber_piQuotientEquiv_piResidueField
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)] :
    (∀ I : MaximalSpectrum (p.asIdeal.Fiber B), p.asIdeal.Fiber B ⧸ I.asIdeal) ≃+*
      ∀ q : p.asIdeal.primesOver B, q.1.ResidueField := by
  let e : MaximalSpectrum (p.asIdeal.Fiber B) ≃ p.asIdeal.primesOver B :=
    fiber_maximalSpectrum_equiv_primesOver hcolim p
  let eReindex :
      (∀ I : MaximalSpectrum (p.asIdeal.Fiber B), p.asIdeal.Fiber B ⧸ I.asIdeal) ≃+*
        (∀ q : p.asIdeal.primesOver B, p.asIdeal.Fiber B ⧸ (e.symm q).asIdeal) :=
    -- Route correction: reindex the quotient family first so the later residue-field comparison
    -- sees a stable `q`-coordinate and no hidden dependent transport.
    (RingEquiv.piCongrLeft
      (fun I : MaximalSpectrum (p.asIdeal.Fiber B) ↦ p.asIdeal.Fiber B ⧸ I.asIdeal) e.symm).symm
  let eResidue :
      (∀ q : p.asIdeal.primesOver B, p.asIdeal.Fiber B ⧸ (e.symm q).asIdeal) ≃+*
        (∀ q : p.asIdeal.primesOver B, q.1.ResidueField) :=
    RingEquiv.piCongrRight fun q ↦
      fiber_reindexedComponent_quotientEquiv_residueField hcolim p q
  -- After the reindexing step, the residue-field comparison is coordinatewise and transport-free.
  exact eReindex.trans eResidue

/-- Helper for Lemma 15.45.12: the refactored product equivalence evaluates coordinatewise via the
component quotient-to-residue-field equivalence. -/
lemma fiber_piQuotientEquiv_piResidueField_apply
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)]
    (f : ∀ I : MaximalSpectrum (p.asIdeal.Fiber B), p.asIdeal.Fiber B ⧸ I.asIdeal)
    (q : p.asIdeal.primesOver B) :
    fiber_piQuotientEquiv_piResidueField hcolim p f q =
      fiber_reindexedComponent_quotientEquiv_residueField hcolim p q
        (f ((fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q)) := by
  -- The new definition first reindexes by `fiber_maximalSpectrum_equiv_primesOver`, then applies
  -- the coordinate residue-field equivalence at that reindexed maximal ideal.
  rfl

/-- Helper for Lemma 15.45.12: the `I`-coordinate of the Artinian product decomposition is the
quotient map to `R ⧸ I`. -/
lemma artinian_equivPi_apply_eq_quotient_mk
    (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]
    (I : MaximalSpectrum R) (x : R) :
    IsArtinianRing.equivPi R x I = Ideal.Quotient.mk I.asIdeal x := by
  -- The reduced Artinian decomposition is the nilradical quotient followed by the Chinese
  -- remainder map, so evaluating the `R`-algebra equivalence at `I` recovers the quotient class.
  have hcomm :
      IsArtinianRing.equivPi R x =
        algebraMap R ((J : MaximalSpectrum R) → R ⧸ J.asIdeal) x := by
    simpa using (IsArtinianRing.equivPi R).commutes x
  simpa using congrArg (fun f : (J : MaximalSpectrum R) → R ⧸ J.asIdeal ↦ f I) hcomm

set_option maxHeartbeats 20000000 in
/-- Helper for Lemma 15.45.12: after postcomposing with the forward residue-field map, the
transported `q`-coordinate becomes the canonical quotient-to-residue-field map. -/
-- TODO: Reprove this by specializing `I = (fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q`,
-- rewriting the transported coordinate with `fiber_piQuotientEquiv_piResidueField_apply`, and then
-- cancelling the forward residue-field map against `fiber_component_quotientEquiv_residueField`.
lemma fiber_transported_coordinate_after_forward_residue_map
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)] [IsReduced (p.asIdeal.Fiber B)]
    (x : p.asIdeal.Fiber B) (q : p.asIdeal.primesOver B)
    (I : MaximalSpectrum (p.asIdeal.Fiber B))
    (hI : I = (fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q)
    (hq' : q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq'
        (((fiber_piQuotientEquiv_piResidueField hcolim p).toRingHom.comp
          (IsArtinianRing.equivPi (p.asIdeal.Fiber B)).toRingHom) x q) =
      algebraMap (p.asIdeal.Fiber B) I.asIdeal.ResidueField x :=
by
  -- Route correction: specialize to the canonical maximal ideal attached to `q` before unfolding
  -- the reindexed product equivalence, so the only remaining transport is the explicit
  -- residue-field equality between the source prime and `q.1`.
  subst hI
  let I : MaximalSpectrum (p.asIdeal.Fiber B) :=
    (fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q
  have hcoord :
      (((fiber_piQuotientEquiv_piResidueField hcolim p).toRingHom.comp
          (IsArtinianRing.equivPi (p.asIdeal.Fiber B)).toRingHom) x q) =
        fiber_reindexedComponent_quotientEquiv_residueField hcolim p q
          (Ideal.Quotient.mk I.asIdeal x) := by
    -- Evaluate the transported Artinian product decomposition at the reindexed `q`-coordinate.
    change
      fiber_piQuotientEquiv_piResidueField hcolim p
          ((IsArtinianRing.equivPi (p.asIdeal.Fiber B)).toRingHom x) q =
        fiber_reindexedComponent_quotientEquiv_residueField hcolim p q
          (Ideal.Quotient.mk I.asIdeal x)
    rw [fiber_piQuotientEquiv_piResidueField_apply]
    simpa [I] using
      artinian_equivPi_apply_eq_quotient_mk
        (R := p.asIdeal.Fiber B) ((fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q) x
  have hsource :
      (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1 = q.1 := by
    exact congrArg Subtype.val
      ((fiber_maximalSpectrum_equiv_primesOver hcolim p).apply_symm_apply q)
  have hsource_comap :
      (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1 =
        I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := by
    simpa [I] using fiber_primesOver_comap_eq hcolim p I
  let eQuot :
      (p.asIdeal.Fiber B ⧸ I.asIdeal) ≃+* I.asIdeal.ResidueField :=
    RingEquiv.ofBijective (algebraMap _ I.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField I.asIdeal)
  let eResidue :
      (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1.ResidueField ≃+*
        I.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map
        (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1 I.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hsource_comap)
      ((p.asIdeal.surjectiveOnStalks_residueField.baseChange').residueFieldMap_bijective
        (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1 I.asIdeal hsource_comap)
  -- Rewrite the `q`-coordinate through the reindexed component equivalence and then use the
  -- canonical residue-field transport to change the source prime from `e I` to `q`.
  rw [hcoord]
  calc
    Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq'
        (fiber_reindexedComponent_quotientEquiv_residueField hcolim p q
          (Ideal.Quotient.mk I.asIdeal x)) =
      Ideal.ResidueField.map
          (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1 I.asIdeal
          Algebra.TensorProduct.includeRight.toRingHom hsource_comap
          (fiber_component_quotientEquiv_residueField hcolim p I
            (Ideal.Quotient.mk I.asIdeal x)) := by
        -- This is the only remaining transport: `fiber_reindexedComponent_quotientEquiv_residueField`
        -- is `fiber_component_quotientEquiv_residueField` followed by the residue-field congruence.
        simpa [fiber_reindexedComponent_quotientEquiv_residueField, I] using
          (residueField_map_apply_congrOfEq
            (f := Algebra.TensorProduct.includeRight.toRingHom)
            (I := (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1)
            (J := q.1) (K := I.asIdeal)
            hsource hsource_comap hq'
            (fiber_component_quotientEquiv_residueField hcolim p I
              (Ideal.Quotient.mk I.asIdeal x)))
    _ = Ideal.ResidueField.map
          (fiber_maximalSpectrum_equiv_primesOver hcolim p I).1 I.asIdeal
          Algebra.TensorProduct.includeRight.toRingHom hsource_comap
          (eResidue.symm (eQuot (Ideal.Quotient.mk I.asIdeal x))) := by
        rfl
    _ = eQuot (Ideal.Quotient.mk I.asIdeal x) := by
        change eResidue (eResidue.symm (eQuot (Ideal.Quotient.mk I.asIdeal x))) =
          eQuot (Ideal.Quotient.mk I.asIdeal x)
        exact eResidue.apply_symm_apply (eQuot (Ideal.Quotient.mk I.asIdeal x))
    _ = algebraMap (p.asIdeal.Fiber B) I.asIdeal.ResidueField x := by
        rfl

/-- Helper for Lemma 15.45.12: after postcomposing with the forward residue-field map, the
canonical `q`-coordinate of `fiberToPiResidueField` is the quotient-to-residue-field map. -/
lemma fiber_canonical_coordinate_after_forward_residue_map
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)]
    (x : p.asIdeal.Fiber B) (q : p.asIdeal.primesOver B)
    (I : MaximalSpectrum (p.asIdeal.Fiber B))
    (hq' : q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq'
        ((p.asIdeal.fiberToPiResidueField B x) q) =
      algebraMap (p.asIdeal.Fiber B) I.asIdeal.ResidueField x := by
  -- Evaluate the owner-level ring-hom identity from `Ideal` at `x`.
  suffices
      Ideal.ResidueField.map q.1 I.asIdeal Algebra.TensorProduct.includeRight.toRingHom hq'
          ((p.asIdeal.fiberToPiResidueField B x) q) =
        algebraMap (p.asIdeal.Fiber B) I.asIdeal.ResidueField x by
    simpa [hq'] using this
  simpa [RingHom.comp_apply] using
    congrArg (fun f : p.asIdeal.Fiber B →+* I.asIdeal.ResidueField => f x)
      (Ideal.fiberToPiResidueField_postcompose_eq_algebraMap
        (p := p.asIdeal) (B := B) q I hq')

lemma fiberToPiResidueField_eq_equivPi_transport
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)] [IsReduced (p.asIdeal.Fiber B)] :
    (fiber_piQuotientEquiv_piResidueField hcolim p).toRingHom.comp
        (IsArtinianRing.equivPi (p.asIdeal.Fiber B)).toRingHom =
      p.asIdeal.fiberToPiResidueField B := by
  -- Evaluate both sides at `x` and `q`, compare after postcomposing to a fixed residue field,
  -- and cancel by injectivity of that forward residue-field map.
  apply RingHom.ext
  intro x
  ext q
  let I : MaximalSpectrum (p.asIdeal.Fiber B) :=
    (fiber_maximalSpectrum_equiv_primesOver hcolim p).symm q
  have hq' : q.1 = I.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := by
    simpa [I] using fiber_primesOver_comap_eq hcolim p I
  let hbij :=
    (p.asIdeal.surjectiveOnStalks_residueField.baseChange').residueFieldMap_bijective
      q.1 I.asIdeal hq'
  apply hbij.injective
  exact
    (fiber_transported_coordinate_after_forward_residue_map
      (hcolim := hcolim) (p := p) x q I rfl hq').trans
      (fiber_canonical_coordinate_after_forward_residue_map
        (p := p) x q I hq').symm

-- Proof sketch: the fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` is both Noetherian and a
-- filtered colimit of étale `κ(p)`-algebras, so it is reduced with finitely many prime ideals, all
-- of which are maximal. Hence it is canonically a finite product of fields. Transport the index
-- set of those factors back to the canonical owner set `p.asIdeal.primesOver B` using
-- `PrimeSpectrum.primesOverOrderIsoFiber`, and then identify the canonical coordinate map
-- `Ideal.fiberToPiResidueField` with the reduced Artinian-ring product decomposition
-- `IsArtinianRing.equivPi`.
/-- Lemma 15.45.12 (2): if `B` is a filtered colimit of étale `A`-algebras and the fiber ring
`p.asIdeal.Fiber B` is Noetherian, then the canonical map from `p.asIdeal.Fiber B` to the finite
product of the residue fields of the primes of `B` lying over `p` is bijective. -/
theorem fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)] :
    Function.Bijective (p.asIdeal.fiberToPiResidueField B) := by
  letI : IsArtinianRing (p.asIdeal.Fiber B) :=
    fiber_isArtinian_of_isFilteredColimitOfEtale_of_isNoetherianFiber hcolim p
  letI : IsReduced (p.asIdeal.Fiber B) :=
    fiber_isReduced_of_isFilteredColimitOfEtale hcolim p
  -- Once the canonical coordinate map is identified with the transported Artinian decomposition,
  -- bijectivity is the composition of the two ring-equivalence factors.
  rw [← fiberToPiResidueField_eq_equivPi_transport hcolim p]
  exact
    (fiber_piQuotientEquiv_piResidueField hcolim p).bijective.comp
      (IsArtinianRing.equivPi (p.asIdeal.Fiber B)).bijective

-- Proof sketch: a filtered colimit of étale `A`-algebras is weakly étale, so the source-facing
-- statement is a direct bridge to the chapter owner
-- `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`. The Noetherian hypothesis used in
-- parts `(1)` and `(2)` is not part of the mathematical content of this residue-field claim.
/-- Lemma 15.45.12 (3): if `B` is a filtered colimit of étale `A`-algebras, then for every prime
`p` of `A` and every prime `q` of `B` lying over `p`, the residue field extension `κ(q) / κ(p)`
is separable algebraic. -/
theorem residueField_isAlgebraic_and_separable_of_isFilteredColimitOfEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) (q : p.asIdeal.primesOver B) :
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := by
  let qSpec : PrimeSpectrum B := ⟨q.1, inferInstance⟩
  have hqSpec : PrimeSpectrum.comap (algebraMap A B) qSpec = p := by
    -- Upgrade the lies-over equality from ideals to prime-spectrum points.
    apply PrimeSpectrum.ext
    simpa [Ideal.under, qSpec] using (q.1.over_def p.asIdeal).symm
  let qbar : PrimeSpectrum (p.asIdeal.Fiber B) :=
    PrimeSpectrum.preimageEquivFiber A B p ⟨qSpec, hqSpec⟩
  have hqbar :
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qbar.asIdeal = q.1 := by
    -- The distinguished fiber prime contracts back to the original branch `q`.
    simpa [qSpec, qbar] using
      PrimeSpectrum.preimageEquivFiber_asIdeal_comap (R := A) (S := B) p qSpec hqSpec
  have hsepFiber : Algebra.IsSeparable p.asIdeal.ResidueField qbar.asIdeal.ResidueField := by
    let hweak : Algebra.IsWeaklyEtale A B :=
      isWeaklyEtale_of_isFilteredColimitOfEtale hcolim
    let _ : Algebra.IsWeaklyEtale p.asIdeal.ResidueField (p.asIdeal.Fiber B) :=
      hweak.baseChange
    -- Work over the fiber field `κ(p)` and apply the local field-case residue-field lemma.
    exact
      residueField_isSeparable_of_isWeaklyEtale_over_field_local
        (K := p.asIdeal.ResidueField) (F := p.asIdeal.Fiber B) qbar.asIdeal
  let e : q.1.ResidueField ≃ₐ[p.asIdeal.ResidueField] qbar.asIdeal.ResidueField :=
    residueField_algEquiv_of_baseChange_fiber_prime_local
      (A := A) (B := B) p.asIdeal q qbar hqbar
  have hsep : Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := by
    -- Pull separability back across the residue-field equivalence.
    simpa using (AlgEquiv.Algebra.isSeparable_iff e).1 hsepFiber
  exact ⟨hsep.isAlgebraic, hsep⟩

end PrimeSpectrum

end
