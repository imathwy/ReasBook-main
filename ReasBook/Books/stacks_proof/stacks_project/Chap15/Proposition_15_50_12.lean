import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_166_6
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap15.Definition_15_50_1
import stacks_proof.stacks_project.Chap15.Lemma_15_41_6
import stacks_proof.stacks_project.Chap15.Lemma_15_41_7
import stacks_proof.stacks_project.Chap15.Lemma_15_43_5
import stacks_proof.stacks_project.Chap15.Lemma_15_43_9
import stacks_proof.stacks_project.Chap15.Lemma_15_50_2
import stacks_proof.stacks_project.Chap15.Proposition_15_50_10
import stacks_proof.stacks_project.Chap15.Proposition_15_50_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct

/- Domain-style sampling:
- primary domain: commutative algebra of `G`-rings and their permanence properties;
- sampled owner declarations of the same kind:
  `IsGRing`,
  `CompletedLocalizationAtPrime`,
  `isGRing_of_essFiniteType`,
  the complete-local `IsGRing` instance from Proposition `15.50.6`;
- best owner abstraction: the chapter owner class `IsGRing`;
- primitive vs. derived:
  the primitive public data are the ambient ring/algebra hypotheses in each source clause;
  the field and complete-local examples are direct owner recall, the Dedekind-domain clause is a
  source-facing owner instance, and the finite-type clause is only a thin source-facing
  specialization of the canonical essentially-finite-type transfer theorem.

Source/core/bridge triage:
- `source-facing`: the Dedekind-domain and finite-type clauses recorded in this proposition;
- `core/canonical`: `IsGRing` and `isGRing_of_essFiniteType`;
- `bridge/view`: the finite-type specialization and the `ℤ` specialization of the
  Dedekind-domain characteristic-zero instance.
-/

section

variable (K : Type u) [Field K]

/- Proposition 15.50.12: fields are `G`-rings. This is the canonical field instance from
Definition `15.50.1`. -/
#check (inferInstance : IsGRing K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Proposition 15.50.12: a Noetherian complete local ring is a `G`-ring. This is the
canonical instance supplied by Proposition `15.50.6`. -/
#check (inferInstance : IsGRing R)

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Helper for Proposition 15.50.12: in a Dedekind domain, a prime below `p` is either the zero
prime or equal to `p`. -/
lemma prime_pair_eq_bot_or_eq_of_dedekind
    (p q : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal) :
    q.asIdeal = ⊥ ∨ q = p := by
  by_cases hqbot : q.asIdeal = ⊥
  · -- Proof comment: the zero-prime branch is one of the two source cases.
    exact Or.inl hqbot
  · -- Proof comment: every nonzero prime in a Dedekind domain is maximal, so the inclusion
    -- `q ⊆ p` forces equality.
    have hqmax : q.asIdeal.IsMaximal :=
      Ideal.IsPrime.isMaximal (R := R) (p := q.asIdeal) q.isPrime hqbot
    have hpq : p.asIdeal ≤ q.asIdeal := hqmax.1 hqp
    right
    exact PrimeSpectrum.ext <| le_antisymm hqp hpq

/-- Helper for Proposition 15.50.12: the residue field at the zero prime of a domain is its
fraction field. -/
noncomputable lemma zero_prime_residueField_algEquiv_fractionRing_of_domain
    (A : Type u) [CommRing A] [IsDomain A] :
    FractionRing A ≃ₐ[A] ((⊥ : Ideal A).ResidueField) := by
  let e : A ≃ₐ[A] A ⧸ (⊥ : Ideal A) := (AlgEquiv.quotientBot A A).symm
  letI : IsFractionRing A ((⊥ : Ideal A).ResidueField) := by
    -- Proof comment: transport the fraction-ring structure across the quotient-by-zero model.
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap A ((⊥ : Ideal A).ResidueField) x =
      algebraMap (A ⧸ (⊥ : Ideal A)) ((⊥ : Ideal A).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    rfl
  -- Proof comment: once both codomains are recognized as fraction-ring models of `A`, the
  -- canonical fraction-ring equivalence identifies them.
  exact FractionRing.algEquiv A ((⊥ : Ideal A).ResidueField)

/-- Helper for Proposition 15.50.12: the residue field at the zero prime of `R` is its
fraction field. -/
noncomputable lemma zero_prime_residueField_algEquiv_fractionRing :
    FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) := by
  -- Proof comment: this is the domain-general zero-prime/fraction-field comparison specialized
  -- to the ambient Dedekind domain `R`.
  exact zero_prime_residueField_algEquiv_fractionRing_of_domain R

/-- Helper for Proposition 15.50.12: a separable field extension is geometrically regular. -/
lemma field_isGeometricallyRegular_of_isSeparableOver
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K] :
    Algebra.IsGeometricallyRegular k K := by
  -- Proof comment: transport geometric regularity from the field over itself across the
  -- separable base-field extension.
  exact
    (Algebra.isGeometricallyRegular_iff_of_isSeparable :
      Algebra.IsGeometricallyRegular k K ↔ Algebra.IsGeometricallyRegular K K).2
      inferInstance

/-- Helper for Proposition 15.50.12: the maximal-ideal residue-field model agrees with the usual
residue field of a local ring. -/
noncomputable lemma maximalIdeal_residueField_ringEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Proposition 15.50.12: quotienting a local ring by its maximal ideal identifies the
ideal-quotient model with the local-ring residue field. -/
noncomputable lemma maximalIdeal_quotient_residueField_ringEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    A ⧸ maximalIdeal A ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).trans
      (maximalIdeal_residueField_ringEquiv A)

/-- Helper for Proposition 15.50.12: the quotient-to-residue-field comparison sends the class of
`a : A` to its usual residue class. -/
lemma maximalIdeal_quotient_residueField_ringEquiv_apply_algebraMap
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdeal_quotient_residueField_ringEquiv A
        (algebraMap A (A ⧸ maximalIdeal A) a) =
      algebraMap A (ResidueField A) a := by
  -- Proof comment: both maps factor through the canonical residue-field quotient, so they agree
  -- on classes coming from `A`.
  change
    maximalIdeal_residueField_ringEquiv A
        (algebraMap A (maximalIdeal A).ResidueField a) =
      algebraMap A (ResidueField A) a
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField
        (algebraMap A (ResidueField A) a) by rfl]
  change
    maximalIdeal_residueField_ringEquiv A
        ((maximalIdeal_residueField_ringEquiv A).symm (algebraMap A (ResidueField A) a)) =
      algebraMap A (ResidueField A) a
  exact
    (maximalIdeal_residueField_ringEquiv A).apply_symm_apply
      (algebraMap A (ResidueField A) a)

/-- Helper for Proposition 15.50.12: localizing a ring at a prime ideal does not change the
corresponding residue field. -/
noncomputable lemma prime_localization_residueField_ringEquiv (p : PrimeSpectrum R) :
    ResidueField (Localization.AtPrime p.asIdeal) ≃+* p.asIdeal.ResidueField :=
  (maximalIdeal_residueField_ringEquiv (Localization.AtPrime p.asIdeal)).symm.trans <| by
    -- Proof comment: the ideal-residue-field model for the maximal ideal of `R_p` is
    -- definitionally the residue field at `p`.
    change
      (maximalIdeal (Localization.AtPrime p.asIdeal)).ResidueField ≃+*
        p.asIdeal.ResidueField
    exact RingEquiv.refl _

/-- Helper for Proposition 15.50.12: for a nonzero prime of a Dedekind domain, the localization
at that prime is a DVR and its maximal-ideal completion is again a DVR. -/
lemma completed_localizationAtPrime_isDiscreteValuationRing_of_nonzero_prime
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    let A := Localization.AtPrime p.asIdeal
    IsDiscreteValuationRing A ∧
      ∃ (_ : IsDomain (AdicCompletion (maximalIdeal A) A)),
        IsDiscreteValuationRing (AdicCompletion (maximalIdeal A) A) := by
  let A := Localization.AtPrime p.asIdeal
  have hA : IsDiscreteValuationRing A := by
    -- Proof comment: a nonzero prime localization of a Dedekind domain is exactly a DVR.
    exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (A := R) (p := p.asIdeal) hp
  have hA' : ∃ (_ : IsDomain A), IsDiscreteValuationRing A := ⟨inferInstance, hA⟩
  have hCompletion :
      ∃ (_ : IsDomain (AdicCompletion (maximalIdeal A) A)),
        IsDiscreteValuationRing (AdicCompletion (maximalIdeal A) A) :=
    (isDiscreteValuationRing_iff_isDiscreteValuationRing_maximalIdeal_adicCompletion A).mp hA'
  -- Proof comment: package both the source DVR and the completion DVR once so the main proof
  -- does not have to reassemble these instances in each branch.
  exact ⟨hA, hCompletion⟩

/-- Helper for Proposition 15.50.12: for a nonzero prime of a Dedekind domain, the fiber of the
localization map `R -> R_p` at that prime is the residue field of `R_p`. -/
noncomputable lemma localizationAtPrime_fiber_ringEquiv_residueField
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    p.asIdeal.Fiber (Localization.AtPrime p.asIdeal) ≃+*
      ResidueField (Localization.AtPrime p.asIdeal) := by
  let A := Localization.AtPrime p.asIdeal
  let eQuot :
      p.asIdeal.Fiber A ≃+*
        A ⧸ Ideal.map (algebraMap R A) p.asIdeal :=
    (closedFiberQuotAlgEquiv :
      p.asIdeal.Fiber A ≃ₐ[R] A ⧸ Ideal.map (algebraMap R A) p.asIdeal).toRingEquiv
  have hmap : Ideal.map (algebraMap R A) p.asIdeal = maximalIdeal A := by
    -- Proof comment: localization at `p` turns the extended prime into the closed point of `R_p`.
    simpa [A] using IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal A
  -- Proof comment: first replace the fiber by the quotient by the extended prime, then identify
  -- that quotient with the residue field of the local ring `R_p`.
  exact eQuot.trans <|
    (Ideal.quotEquivOfEq hmap).trans
      (maximalIdeal_quotient_residueField_ringEquiv A)

/-- Helper for Proposition 15.50.12: the closed-fiber comparison for `R -> R_p` fixes the base
residue field `κ(p)`. -/
lemma localizationAtPrime_fiber_ringEquiv_residueField_commutes
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) (x : p.asIdeal.ResidueField) :
    localizationAtPrime_fiber_ringEquiv_residueField (R := R) p hp
        (algebraMap p.asIdeal.ResidueField
          (p.asIdeal.Fiber (Localization.AtPrime p.asIdeal)) x) =
      algebraMap p.asIdeal.ResidueField
        (ResidueField (Localization.AtPrime p.asIdeal)) x := by
  let A := Localization.AtPrime p.asIdeal
  have hcomap : Ideal.comap (algebraMap R A) (maximalIdeal A) = p.asIdeal := by
    -- Proof comment: the maximal ideal of the localized ring contracts back to `p`.
    simpa [A] using
      (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p.asIdeal))
  -- Proof comment: reduce the scalar check to a residue class lifted from `R`, then unfold the
  -- closed-fiber quotient model and compare both sides through the same class in `A / m_A`.
  obtain ⟨a, rfl⟩ := p.asIdeal.algebraMap_residueField_surjective x
  change
    localizationAtPrime_fiber_ringEquiv_residueField (R := R) p hp
        (algebraMap R (p.asIdeal.Fiber A) a) =
      algebraMap p.asIdeal.ResidueField (ResidueField A)
        (algebraMap R p.asIdeal.ResidueField a)
  rw [Ideal.ResidueField.map_algebraMap p.asIdeal (maximalIdeal A) (algebraMap R A) hcomap a]
  simp [localizationAtPrime_fiber_ringEquiv_residueField,
    maximalIdeal_quotient_residueField_ringEquiv_apply_algebraMap]

/-- Helper for Proposition 15.50.12: the closed fiber of `R -> R_p` is canonically the residue
field of the local ring `R_p` as a `κ(p)`-algebra. -/
noncomputable lemma localizationAtPrime_fiber_algEquiv_residueField
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    p.asIdeal.Fiber (Localization.AtPrime p.asIdeal) ≃ₐ[p.asIdeal.ResidueField]
      ResidueField (Localization.AtPrime p.asIdeal) := by
  -- Proof comment: the existing ring equivalence is already compatible with the `κ(p)`-scalar
  -- structure by the elementwise commutation lemma above.
  refine AlgEquiv.ofRingEquiv
    (f := localizationAtPrime_fiber_ringEquiv_residueField (R := R) p hp) ?_
  intro x
  exact localizationAtPrime_fiber_ringEquiv_residueField_commutes (R := R) p hp x

/-- Helper for Proposition 15.50.12: the closed fiber of `R -> R_p` is canonically the residue
field of `R_p` as an algebra over the localized ring itself. -/
noncomputable lemma localizationAtPrime_closedFiber_algEquiv_residueField_over_localization
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    let A := Localization.AtPrime p.asIdeal
    p.asIdeal.Fiber A ≃ₐ[A] ResidueField A := by
  let A := Localization.AtPrime p.asIdeal
  -- Proof comment: package the quotient-model comparison as an `A`-algebra equivalence by
  -- checking only that it sends the right tensor-factor algebra map to the usual residue map.
  refine AlgEquiv.ofRingEquiv
    (f := localizationAtPrime_fiber_ringEquiv_residueField (R := R) p hp) ?_
  intro a
  simp [localizationAtPrime_fiber_ringEquiv_residueField,
    maximalIdeal_quotient_residueField_ringEquiv_apply_algebraMap]

/-- Helper for Proposition 15.50.12: localizing `R_p` away from the image of the nonzero elements
of `R` already gives the fraction field of `R_p`. -/
noncomputable lemma localizationAtPrime_sourceLocalization_isFractionRing
    (p : PrimeSpectrum R) :
    let A := Localization.AtPrime p.asIdeal
    let T := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
    IsFractionRing A (Localization T) := by
  let A := Localization.AtPrime p.asIdeal
  let T := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  have hField : IsField (Localization T) := by
    refine
      { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
        mul_comm := mul_comm
        mul_inv_cancel := ?_ }
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
    have hx : x ≠ 0 := by
      intro hx0
      apply hz
      simpa [hx0] using (show IsLocalization.mk' (Localization T) x s = 0 by simp [hx0])
    have hPrimeToT :
        p.asIdeal.primeCompl ≤ Submonoid.comap (algebraMap R A) T := by
      intro r hr
      change algebraMap R A r ∈ T
      have hr0 : r ≠ 0 := by
        intro hr0
        exact hr (hr0 ▸ p.asIdeal.zero_mem)
      exact
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨r, mem_nonZeroDivisors_of_ne_zero hr0⟩
    obtain ⟨a, t, hxt⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
    have ha : a ≠ 0 := by
      intro ha0
      apply hx
      rw [hxt, ha0]
      simp
    have haT : algebraMap R A a ∈ T := by
      exact
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩
    have htT : algebraMap R A t ∈ T := by
      have ht0 : (t : R) ≠ 0 := by
        intro ht0
        exact t.2 (ht0 ▸ p.asIdeal.zero_mem)
      exact
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨(t : R), mem_nonZeroDivisors_of_ne_zero ht0⟩
    have hxUnit : IsUnit (algebraMap A (Localization T) x) := by
      -- Proof comment: write `x` as `a / t` with `a,t ∈ R`; both images land in the chosen
      -- localization submonoid, so the image of `x` is a quotient of units.
      rw [hxt]
      rw [IsLocalization.map_mk' (Q := Localization T) hPrimeToT]
      have hnumUnit :
          IsUnit (algebraMap A (Localization T) (algebraMap R A a)) :=
        IsLocalization.map_units (Localization T) ⟨algebraMap R A a, haT⟩
      have hdenUnit :
          IsUnit (algebraMap A (Localization T) (algebraMap R A t)) :=
        IsLocalization.map_units (Localization T) ⟨algebraMap R A t, htT⟩
      simpa [IsLocalization.mk'_spec'] using hnumUnit.div hdenUnit
    have hsUnit : IsUnit (algebraMap A (Localization T) s) :=
      IsLocalization.map_units (Localization T) s
    refine ⟨(IsUnit.unitOfMulIsUnitLeft hsUnit ?_).unit⁻¹, ?_⟩
    · simpa [IsLocalization.mk'_spec'] using hxUnit
    · simp
  letI : Field (Localization T) := hField.toField
  have hT : T ≤ nonZeroDivisors A := by
    -- Proof comment: `R_p` is still a domain, so images of source nonzerodivisors stay
    -- nonzerodivisors in the localization.
    exact
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul A
        (show nonZeroDivisors R ≤ nonZeroDivisors R by
          intro x hx
          exact hx)
  letI : FaithfulSMul A (Localization T) :=
    (faithfulSMul_iff_algebraMap_injective A (Localization T)).mpr <|
      IsLocalization.injective (Localization T) hT
  -- Proof comment: once the source-side localization is a field, the ordinary localization normal
  -- form upgrades it to the fraction-ring owner on `R_p`.
  refine IsFractionRing.of_field (R := A) (K := Localization T) ?_
  intro z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
  refine ⟨x, s, ?_⟩
  apply (eq_div_iff ?_).2
  · exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors (Localization T) hT s.2
  · simpa [div_eq_mul_inv] using (IsLocalization.mk'_spec' (Localization T) x s)

/-- Helper for Proposition 15.50.12: the generic fiber of `R -> R_p` is canonically the fraction
field of `R_p` as an algebra over the localized ring itself. -/
noncomputable lemma localizationAtPrime_genericFiber_algEquiv_fractionRing
    (p : PrimeSpectrum R) :
    let A := Localization.AtPrime p.asIdeal
    ((⊥ : Ideal R).Fiber A) ≃ₐ[A] FractionRing A := by
  let A := Localization.AtPrime p.asIdeal
  let T := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  let eZero : ((⊥ : Ideal R).ResidueField) ≃ₐ[R] Localization (nonZeroDivisors R) :=
    (zero_prime_residueField_algEquiv_fractionRing (R := R)).symm.trans
      (FractionRing.algEquiv R (Localization (nonZeroDivisors R)))
  let eTensor :
      ((⊥ : Ideal R).Fiber A) ≃+* Localization T :=
    (Algebra.TensorProduct.congr eZero (AlgEquiv.refl : A ≃ₐ[R] A)).toRingEquiv.trans
      (Localization.tensorRightAlgEquiv (nonZeroDivisors R) A).toRingEquiv
  letI : IsFractionRing A (Localization T) :=
    localizationAtPrime_sourceLocalization_isFractionRing (R := R) p
  let eFrac : Localization T ≃ₐ[A] FractionRing A :=
    (FractionRing.algEquiv A (Localization T)).symm
  -- Proof comment: first normalize the raw tensor-defined generic fiber to the source-side
  -- localization model, then identify that localization with the fraction field of `R_p`.
  refine (AlgEquiv.ofRingEquiv (f := eTensor) ?_).trans eFrac
  intro a
  simp [eTensor, eZero]

/-- Helper for Proposition 15.50.12: the closed fiber of a maximal-ideal completion is the
quotient by the completed maximal ideal. -/
noncomputable lemma closed_completion_fiber_ringEquiv_quotient
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Ideal.Fiber (maximalIdeal A) (AdicCompletion (maximalIdeal A) A) ≃+*
      AdicCompletion (maximalIdeal A) A ⧸
        maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let eQuot :
      Ideal.Fiber (maximalIdeal A) ACompletion ≃+*
        ACompletion ⧸ Ideal.map (algebraMap A ACompletion) (maximalIdeal A) :=
    (closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal A) ACompletion ≃ₐ[A]
        ACompletion ⧸ Ideal.map (algebraMap A ACompletion) (maximalIdeal A)).toRingEquiv
  have hmap :
      Ideal.map (algebraMap A ACompletion) (maximalIdeal A) =
        maximalIdeal ACompletion := by
    -- Proof comment: the completion map preserves the closed point of the local ring.
    simpa [ACompletion] using completion_map_maximalIdeal_eq_maximalIdeal A
  -- Proof comment: the canonical closed-fiber quotient model from `closedFiberQuotAlgEquiv`
  -- becomes the desired quotient after replacing the extended ideal by the completed maximal
  -- ideal.
  exact eQuot.trans <| Ideal.quotEquivOfEq hmap

/-- Helper for Proposition 15.50.12: the closed fiber of a maximal-ideal completion is
ring-equivalent to the residue field of the completion. -/
noncomputable lemma closed_completion_fiber_ringEquiv_residueField
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Ideal.Fiber (maximalIdeal A) (AdicCompletion (maximalIdeal A) A) ≃+*
      ResidueField (AdicCompletion (maximalIdeal A) A) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  -- Proof comment: factor the closed fiber through the completed maximal-ideal quotient, then use
  -- the standard quotient/residue-field identification for the local ring `A^∧`.
  exact
    (closed_completion_fiber_ringEquiv_quotient A).trans
      (maximalIdeal_quotient_residueField_ringEquiv ACompletion)

/-- Helper for Proposition 15.50.12: the completion of a Noetherian local ring induces an
algebra equivalence on residue fields over the source residue field. -/
noncomputable lemma completion_residueField_algEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ResidueField A ≃ₐ[ResidueField A]
      ResidueField (AdicCompletion (maximalIdeal A) A) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let _ : Algebra (ResidueField A) (ResidueField ACompletion) :=
    (ResidueField.map (algebraMap A ACompletion)).toAlgebra
  let ψ : ResidueField A →ₐ[ResidueField A] ResidueField ACompletion :=
    IsScalarTower.toAlgHom (ResidueField A) (ResidueField A) (ResidueField ACompletion)
  -- Proof comment: the completion map is already known to be bijective on residue fields, so we
  -- only package that bijection in the algebra-equiv form needed by the formal-fiber transport.
  refine AlgEquiv.ofBijective ψ ?_
  simpa [ψ, RingHom.algebraMap_toAlgebra] using
    (maximalIdealCompletion_residueField_bijective A)

/-- Helper for Proposition 15.50.12: the closed-fiber comparison for the maximal-ideal
completion fixes the source residue field. -/
lemma closed_completion_fiber_ringEquiv_residueField_commutes
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (x : ResidueField A) :
    closed_completion_fiber_ringEquiv_residueField A
        (algebraMap (ResidueField A)
          (Ideal.Fiber (maximalIdeal A) (AdicCompletion (maximalIdeal A) A)) x) =
      completion_residueField_algEquiv A x := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  -- Proof comment: as in the strict-henselization model, lift a residue-field element back to
  -- `A` and compare both sides on the corresponding closed-fiber class.
  obtain ⟨a, rfl⟩ := (maximalIdeal A).algebraMap_residueField_surjective x
  change
    closed_completion_fiber_ringEquiv_residueField A
        (algebraMap A (Ideal.Fiber (maximalIdeal A) ACompletion) a) =
      algebraMap A (ResidueField ACompletion) a
  simp [closed_completion_fiber_ringEquiv_residueField,
    closed_completion_fiber_ringEquiv_quotient, completion_residueField_algEquiv,
    maximalIdeal_quotient_residueField_ringEquiv_apply_algebraMap]

/-- Helper for Proposition 15.50.12: the closed fiber of the completion of a Noetherian local
ring is canonically the residue field of the completion as a `ResidueField A`-algebra. -/
noncomputable lemma closed_completion_fiber_algEquiv_residueField
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Ideal.Fiber (maximalIdeal A) (AdicCompletion (maximalIdeal A) A) ≃ₐ[ResidueField A]
      ResidueField (AdicCompletion (maximalIdeal A) A) := by
  -- Proof comment: package the residue-field compatibility from the previous lemma into the
  -- desired algebra equivalence.
  refine AlgEquiv.ofRingEquiv
    (f := closed_completion_fiber_ringEquiv_residueField A) ?_
  intro x
  exact closed_completion_fiber_ringEquiv_residueField_commutes A x

/-- Helper for Proposition 15.50.12: after base change to the completion of a Noetherian local
ring, the closed fiber is exactly the residue field of the completion. -/
noncomputable lemma closed_completion_baseChange_algEquiv_residueField
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    let ACompletion := AdicCompletion (maximalIdeal A) A
    ResidueField A ⊗[A] ACompletion ≃ₐ[ResidueField A]
      ResidueField ACompletion := by
  -- Proof comment: for a local ring the `maximalIdeal`-fiber is definitionally the displayed
  -- tensor product, so the existing closed-fiber comparison is already the desired adapter.
  simpa [Ideal.Fiber] using closed_completion_fiber_algEquiv_residueField A

/-- Helper for Proposition 15.50.12: replacing the zero-prime residue field of a domain by its
fraction field identifies the generic completion fiber with the corresponding localization model. -/
noncomputable lemma generic_completion_zeroFiber_algEquiv_localization
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] :
    let ACompletion := AdicCompletion (maximalIdeal A) A
    ((⊥ : Ideal A).Fiber ACompletion) ≃+*
      Localization (Algebra.algebraMapSubmonoid ACompletion (nonZeroDivisors A)) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let eZero : FractionRing A ≃ₐ[A] ((⊥ : Ideal A).ResidueField) :=
    zero_prime_residueField_algEquiv_fractionRing_of_domain A
  let eFrac : Localization (nonZeroDivisors A) ≃ₐ[A] FractionRing A :=
    IsLocalization.algEquiv (nonZeroDivisors A) (Localization (nonZeroDivisors A)) (FractionRing A)
  -- Proof comment: first replace the zero-prime residue field by the fraction field, then rewrite
  -- the tensor product as the standard localization of the completion away from the source
  -- nonzerodivisors.
  exact
    ((Algebra.TensorProduct.congr eZero.symm
        (AlgEquiv.refl : ACompletion ≃ₐ[A] ACompletion)).toRingEquiv.trans <|
      ((Algebra.TensorProduct.congr eFrac.symm
        (AlgEquiv.refl : ACompletion ≃ₐ[A] ACompletion)).toRingEquiv.trans <|
        (Localization.tensorRightAlgEquiv (nonZeroDivisors A) ACompletion).toRingEquiv))

/-- Helper for Proposition 15.50.12: a uniformizer of a DVR stays a uniformizer after maximal-ideal
completion. -/
lemma completion_uniformizer_image_irreducible
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A]
    {ϖ : A} (hϖ : Irreducible ϖ) :
    let ACompletion := AdicCompletion (maximalIdeal A) A
    Irreducible (algebraMap A ACompletion ϖ) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  -- Proof comment: the completion map sends the maximal ideal generated by `ϖ` to the maximal
  -- ideal of the completion, so the image of `ϖ` is again a uniformizer.
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  rw [← completion_map_maximalIdeal_eq_maximalIdeal A]
  rw [hϖ.maximalIdeal_eq]
  ext x
  simp [Ideal.mem_map_iff_of_surjective, Submodule.span_singleton_eq_range]

/-- Helper for Proposition 15.50.12: every nonzero element of the completion of a DVR differs from
the image of a source power of a uniformizer by a unit. -/
lemma completion_nonzero_eq_unit_mul_source_pow
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A]
    {x : AdicCompletion (maximalIdeal A) A} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Units (AdicCompletion (maximalIdeal A) A)),
      x = u * algebraMap A (AdicCompletion (maximalIdeal A) A)
        ((Classical.choose (IsDiscreteValuationRing.exists_irreducible A)) ^ n) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let ϖ : A := Classical.choose (IsDiscreteValuationRing.exists_irreducible A)
  have hϖ : Irreducible ϖ := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)
  have hImage :
      Irreducible (algebraMap A ACompletion ϖ) :=
    completion_uniformizer_image_irreducible (A := A) hϖ
  -- Proof comment: in the completed DVR every nonzero element is associated to a power of the
  -- completed uniformizer, and powers commute with the completion map.
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (R := ACompletion) hx hImage
  refine ⟨n, u, ?_⟩
  simpa [ϖ, map_pow] using hu

/-- Helper for Proposition 15.50.12: localizing the completion of a DVR away from the image of the
source nonzerodivisors produces a field. -/
noncomputable lemma completion_localization_isField_of_dvr
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A] :
    let ACompletion := AdicCompletion (maximalIdeal A) A
    let T := Algebra.algebraMapSubmonoid ACompletion (nonZeroDivisors A)
    IsField (Localization T) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let T := Algebra.algebraMapSubmonoid ACompletion (nonZeroDivisors A)
  have hT :
      T ≤ nonZeroDivisors ACompletion := by
    -- Proof comment: the completion remains a domain, so source nonzerodivisors stay
    -- nonzerodivisors after applying the algebra map.
    exact
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul ACompletion
        (show nonZeroDivisors A ≤ nonZeroDivisors A by intro x hx; exact hx)
  letI : FaithfulSMul ACompletion (Localization T) :=
    (faithfulSMul_iff_algebraMap_injective ACompletion (Localization T)).mpr <|
      IsLocalization.injective (Localization T) hT
  refine
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := mul_comm
      mul_inv_cancel := ?_ }
  intro z hz
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
  have hx : x ≠ 0 := by
    intro hx0
    apply hz
    simpa [hx0] using (show IsLocalization.mk' (Localization T) x s = 0 by simp [hx0])
  obtain ⟨n, u, hu⟩ := completion_nonzero_eq_unit_mul_source_pow (A := A) hx
  have hpowMem : (Classical.choose (IsDiscreteValuationRing.exists_irreducible A) ^ n) ∈
      nonZeroDivisors A := by
    exact mem_nonZeroDivisors_of_ne_zero <| pow_ne_zero _ <|
      Irreducible.ne_zero
        (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A))
  have hxUnit : IsUnit (algebraMap ACompletion (Localization T) x) := by
    rw [hu]
    refine IsUnit.mul ?_ ?_
    · exact IsUnit.map (algebraMap ACompletion (Localization T)) u.isUnit
    · simpa [T, map_pow] using
        IsLocalization.map_units (Localization T)
          ⟨algebraMap A ACompletion
              ((Classical.choose (IsDiscreteValuationRing.exists_irreducible A)) ^ n),
            Algebra.mem_algebraMapSubmonoid_of_mem ⟨_, hpowMem⟩⟩
  have hsUnit : IsUnit (algebraMap ACompletion (Localization T) s) :=
    IsLocalization.map_units (Localization T) s
  refine ⟨(IsUnit.unitOfMulIsUnitLeft hsUnit ?_).unit⁻¹, ?_⟩
  · simpa [IsLocalization.mk'_spec'] using hxUnit
  · simp

/-- Helper for Proposition 15.50.12: the completion-side localization away from the image of the
source nonzerodivisors is a fraction-ring model of the completed DVR. -/
noncomputable lemma completion_localization_isFractionRing_of_dvr
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A] :
    let ACompletion := AdicCompletion (maximalIdeal A) A
    let T := Algebra.algebraMapSubmonoid ACompletion (nonZeroDivisors A)
    IsFractionRing ACompletion (Localization T) := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let T := Algebra.algebraMapSubmonoid ACompletion (nonZeroDivisors A)
  let hField : IsField (Localization T) := completion_localization_isField_of_dvr (A := A)
  letI : Field (Localization T) := hField.toField
  have hT :
      T ≤ nonZeroDivisors ACompletion := by
    exact
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul ACompletion
        (show nonZeroDivisors A ≤ nonZeroDivisors A by intro x hx; exact hx)
  letI : FaithfulSMul ACompletion (Localization T) :=
    (faithfulSMul_iff_algebraMap_injective ACompletion (Localization T)).mpr <|
      IsLocalization.injective (Localization T) hT
  -- Proof comment: once the localization is known to be a field, the ordinary localization normal
  -- form provides the fraction-ring structure directly.
  refine IsFractionRing.of_field (R := ACompletion) (K := Localization T) ?_
  intro z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
  refine ⟨x, s, ?_⟩
  apply (eq_div_iff ?_).2
  · exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors (Localization T) hT s.2
  · simpa [div_eq_mul_inv] using (IsLocalization.mk'_spec' (Localization T) x s)

/-- Helper for Proposition 15.50.12: the explicit completion-side localization agrees with the
fraction field of the completed DVR. -/
noncomputable lemma completion_localization_algEquiv_fractionRing_of_dvr
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsDiscreteValuationRing A] :
    let ACompletion := AdicCompletion (maximalIdeal A) A
    let T := Algebra.algebraMapSubmonoid ACompletion (nonZeroDivisors A)
    Localization T ≃ₐ[ACompletion] FractionRing ACompletion := by
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let T := Algebra.algebraMapSubmonoid ACompletion (nonZeroDivisors A)
  letI : IsFractionRing ACompletion (Localization T) :=
    completion_localization_isFractionRing_of_dvr (A := A)
  -- Proof comment: both rings are now recognized as fraction-ring models of the completed DVR.
  exact FractionRing.algEquiv ACompletion (Localization T)

/-- Helper for Proposition 15.50.12: at the zero prime, the completed localization is already the
fraction field. -/
noncomputable lemma zero_prime_completedLocalization_algEquiv_fractionField
    (p : PrimeSpectrum R) (hp : p.asIdeal = ⊥) :
    let A := Localization.AtPrime (⊥ : Ideal R)
    R̂_[p] ≃ₐ[A] A := by
  subst hp
  let A := Localization.AtPrime (⊥ : Ideal R)
  let ACompletion := AdicCompletion (maximalIdeal A) A
  letI : IsFractionRing R A := by
    -- Proof comment: localizing a domain at the zero prime is the ordinary fraction field model.
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization ((⊥ : Ideal R).primeCompl) A)
  letI : Field A := IsFractionRing.toField R A
  have hmaxA : maximalIdeal A = ⊥ := by
    -- Proof comment: the generic localization is a field, so its maximal ideal vanishes.
    exact IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField A)
  have hmaxCompletion : maximalIdeal ACompletion = ⊥ := by
    -- Proof comment: the completion map preserves maximal ideals, hence the completed local ring
    -- is also a field in the zero-prime case.
    calc
      maximalIdeal ACompletion =
          Ideal.map (algebraMap A ACompletion) (maximalIdeal A) := by
            symm
            simpa [ACompletion] using completion_map_maximalIdeal_eq_maximalIdeal A
      _ = ⊥ := by simpa [hmaxA]
  let eAtoResidue : A ≃ₐ[A] ResidueField A :=
    (by
      -- Proof comment: identify the residue field of the field `A` with `A` itself.
      let eQuot : A ≃ₐ[A] A ⧸ maximalIdeal A := by
        simpa [hmaxA] using (AlgEquiv.quotientBot A A)
      let eRes : A ⧸ maximalIdeal A ≃ₐ[A] ResidueField A := by
        refine AlgEquiv.ofRingEquiv
          (f := maximalIdeal_quotient_residueField_ringEquiv A) ?_
        intro a
        exact maximalIdeal_quotient_residueField_ringEquiv_apply_algebraMap A a
      exact eQuot.trans eRes)
  let eCompletionToResidue : ACompletion ≃ₐ[A] ResidueField ACompletion :=
    (by
      -- Proof comment: the completion residue field is likewise the whole completed ring.
      let eQuot : ACompletion ≃ₐ[A] ACompletion ⧸ maximalIdeal ACompletion := by
        let eQuotCompletion : ACompletion ≃ₐ[ACompletion]
            ACompletion ⧸ maximalIdeal ACompletion := by
          simpa [hmaxCompletion] using (AlgEquiv.quotientBot ACompletion ACompletion)
        exact eQuotCompletion.restrictScalars A
      let eRes : ACompletion ⧸ maximalIdeal ACompletion ≃ₐ[A] ResidueField ACompletion := by
        refine AlgEquiv.ofRingEquiv
          (f := maximalIdeal_quotient_residueField_ringEquiv ACompletion) ?_
        intro a
        simpa using
          maximalIdeal_quotient_residueField_ringEquiv_apply_algebraMap ACompletion
            (algebraMap A ACompletion a)
      exact eQuot.trans eRes)
  let eResidue : ResidueField A ≃ₐ[A] ResidueField ACompletion :=
    (completion_residueField_algEquiv A).restrictScalars A
  -- Proof comment: compare both rings with their residue fields and use the completion-induced
  -- residue-field equivalence.
  exact eCompletionToResidue.trans (eResidue.symm.trans eAtoResidue.symm)

/-- Helper for Proposition 15.50.12: at the zero prime, the generic formal fiber of the completed
localization is the zero-prime localization itself. -/
noncomputable lemma zero_prime_formalFiber_algEquiv_localizationAtBot
    (p : PrimeSpectrum R) (hp : p.asIdeal = ⊥) :
    let A := Localization.AtPrime (⊥ : Ideal R)
    ((⊥ : Ideal R).Fiber (R̂_[p])) ≃ₐ[((⊥ : Ideal R).ResidueField)] A := by
  let A := Localization.AtPrime (⊥ : Ideal R)
  let eZero : FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) :=
    zero_prime_residueField_algEquiv_fractionRing (R := R)
  let eFrac : FractionRing R ≃ₐ[R] A := by
    letI : IsFractionRing R A := by
      -- Proof comment: localizing a domain at the zero prime is the usual fraction-field model.
      delta IsFractionRing
      simpa [Ideal.primeCompl_bot] using
        (inferInstance : IsLocalization ((⊥ : Ideal R).primeCompl) A)
    exact FractionRing.algEquiv R A
  let eBase : ((⊥ : Ideal R).ResidueField) ≃ₐ[R] A := eZero.symm.trans eFrac
  let _ : Algebra ((⊥ : Ideal R).ResidueField) A := eBase.toRingHom.toAlgebra
  let _ : IsScalarTower R ((⊥ : Ideal R).ResidueField) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Proof comment: the transported `κ(0)`-algebra on `A` is chosen so that it extends the
      -- original `R`-algebra structure.
      simpa [RingHom.algebraMap_toAlgebra] using eBase.commutes x
  let eTensor :
      ((⊥ : Ideal R).Fiber (R̂_[p])) ≃ₐ[((⊥ : Ideal R).ResidueField)]
        ((⊥ : Ideal R).Fiber A) := by
    let eRhat : R̂_[p] ≃ₐ[R] A :=
      (zero_prime_completedLocalization_algEquiv_fractionField (R := R) p hp).restrictScalars R
    let eRing :
        ((⊥ : Ideal R).Fiber (R̂_[p])) ≃+* ((⊥ : Ideal R).Fiber A) :=
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : ((⊥ : Ideal R).ResidueField) ≃ₐ[R] ((⊥ : Ideal R).ResidueField))
        eRhat).toRingEquiv
    -- Proof comment: tensoring the completed-localization comparison with `κ(0)` preserves the
    -- left-factor scalar map, so the result is already `κ(0)`-linear.
    refine AlgEquiv.ofRingEquiv (f := eRing) ?_
    intro x
    simp [eRing]
  let eFiber :
      ((⊥ : Ideal R).Fiber A) ≃ₐ[((⊥ : Ideal R).ResidueField)] A := by
    -- Proof comment: once `A` is viewed as a `κ(0)`-algebra through the zero-prime fraction-field
    -- equivalence, the generic fiber over `R` is the left tensor unit.
    simpa [Ideal.Fiber] using
      (Algebra.TensorProduct.lidOfCompatibleSMul
        R ((⊥ : Ideal R).ResidueField) A)
  exact eTensor.trans eFiber

/-- Helper for Proposition 15.50.12: for a nonzero prime, the generic formal fiber of the
completed localization is the fraction field of the completed DVR. -/
noncomputable lemma generic_nonzero_formalFiber_algEquiv_fractionRing_of_completion
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    let A := Localization.AtPrime p.asIdeal
    let ACompletion := AdicCompletion (maximalIdeal A) A
    ((⊥ : Ideal R).Fiber (R̂_[p])) ≃ₐ[((⊥ : Ideal R).ResidueField)] FractionRing ACompletion := by
  let A := Localization.AtPrime p.asIdeal
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let _ := completed_localizationAtPrime_isDiscreteValuationRing_of_nonzero_prime
    (R := R) p hp
  -- Proof comment: the remaining work is to package the already-proved generic normalization
  -- steps into a single `κ(0)`-linear algebra equivalence.
  -- TODO: compose `fiber_baseChange_algEquiv` with
  -- `localizationAtPrime_genericFiber_algEquiv_fractionRing`,
  -- `generic_completion_zeroFiber_algEquiv_localization`, and
  -- `completion_localization_algEquiv_fractionRing_of_dvr`, while verifying the final
  -- `κ(0)`-scalar compatibility at each transition.
  sorry

/-- Helper for Proposition 15.50.12: for a nonzero prime, the closed formal fiber of the
completed localization is the residue field of the completed DVR. -/
noncomputable lemma closed_nonzero_formalFiber_algEquiv_completion_residueField
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    let A := Localization.AtPrime p.asIdeal
    let ACompletion := AdicCompletion (maximalIdeal A) A
    p.asIdeal.Fiber (R̂_[p]) ≃ₐ[p.asIdeal.ResidueField] ResidueField ACompletion := by
  let A := Localization.AtPrime p.asIdeal
  let ACompletion := AdicCompletion (maximalIdeal A) A
  -- Proof comment: the missing step is again only packaging: rewrite the base-changed closed
  -- fiber through the `R_p` residue field and then collapse the completion closed fiber.
  -- TODO: combine `fiber_baseChange_algEquiv`,
  -- `localizationAtPrime_closedFiber_algEquiv_residueField_over_localization`, and
  -- `closed_completion_baseChange_algEquiv_residueField` into one direct `κ(p)`-linear
  -- equivalence.
  sorry

/-- Helper for Proposition 15.50.12: the residue field of the completed localization at `p` is
geometrically regular over the original residue field `κ(p)`. -/
lemma completion_residueField_isGeometricallyRegular_over_primeResidueField
    (p : PrimeSpectrum R) :
    let A := Localization.AtPrime p.asIdeal
    let ACompletion := AdicCompletion (maximalIdeal A) A
    IsGeometricallyRegular p.asIdeal.ResidueField (ResidueField ACompletion) := by
  let A := Localization.AtPrime p.asIdeal
  let ACompletion := AdicCompletion (maximalIdeal A) A
  let eLocRes : p.asIdeal.ResidueField ≃+* ResidueField A :=
    (prime_localization_residueField_ringEquiv (R := R) p).symm
  let _ : Algebra p.asIdeal.ResidueField (ResidueField A) := eLocRes.toRingHom.toAlgebra
  let _ : Algebra p.asIdeal.ResidueField (ResidueField ACompletion) :=
    ((algebraMap (ResidueField A) (ResidueField ACompletion)).comp
      (algebraMap p.asIdeal.ResidueField (ResidueField A))).toAlgebra
  let _ : IsScalarTower p.asIdeal.ResidueField (ResidueField A) (ResidueField ACompletion) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hbij :
      Function.Bijective
        (IsScalarTower.toAlgHom
          p.asIdeal.ResidueField p.asIdeal.ResidueField (ResidueField A)) := by
    simpa [RingHom.algebraMap_toAlgebra] using eLocRes.bijective
  let eBase :
      p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] ResidueField A :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom
        p.asIdeal.ResidueField p.asIdeal.ResidueField (ResidueField A))
      hbij
  have hGeomA : IsGeometricallyRegular p.asIdeal.ResidueField (ResidueField A) := by
    let _ : IsGeometricallyRegular
        p.asIdeal.ResidueField p.asIdeal.ResidueField := inferInstance
    -- Proof comment: after transporting scalars from `κ(p)` to `ResidueField A`, the source
    -- residue field is a field over itself.
    exact Algebra.isGeometricallyRegular_of_algEquiv eBase.symm
  let eCompletion :
      ResidueField A ≃ₐ[p.asIdeal.ResidueField] ResidueField ACompletion :=
    (completion_residueField_algEquiv A).restrictScalars p.asIdeal.ResidueField
  let _ : IsGeometricallyRegular p.asIdeal.ResidueField (ResidueField A) := hGeomA
  -- Proof comment: the completion comparison on residue fields is an algebra equivalence over
  -- `κ(p)` once the localization residue field is installed as the intermediate base.
  exact Algebra.isGeometricallyRegular_of_algEquiv eCompletion.symm

/-- Helper for Proposition 15.50.12: the generic formal fiber over a prime of a Dedekind domain
is geometrically regular once the tensor-defined generic fiber is identified with the fraction
field of the completed DVR. -/
lemma generic_formalFiber_isGeometricallyRegular_of_dedekind_prime
    (p : PrimeSpectrum R) :
    IsGeometricallyRegular ((⊥ : Ideal R).ResidueField)
      ((⊥ : Ideal R).Fiber (R̂_[p])) := by
  by_cases hp : p.asIdeal = ⊥
  · -- Proof comment: in the zero-prime case the completed localization is the completion of the
    -- fraction field at its zero maximal ideal, so the fiber is the source field in disguise.
    let A := Localization.AtPrime (⊥ : Ideal R)
    let eZero : FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) :=
      zero_prime_residueField_algEquiv_fractionRing (R := R)
    let eFrac : FractionRing R ≃ₐ[R] A := by
      letI : IsFractionRing R A := by
        -- Proof comment: localizing a domain at the zero prime recovers the ordinary fraction
        -- field model.
        delta IsFractionRing
        simpa [Ideal.primeCompl_bot] using
          (inferInstance : IsLocalization ((⊥ : Ideal R).primeCompl) A)
      exact FractionRing.algEquiv R A
    let eBase : ((⊥ : Ideal R).ResidueField) ≃ₐ[R] A := eZero.symm.trans eFrac
    let _ : Algebra ((⊥ : Ideal R).ResidueField) A := eBase.toRingHom.toAlgebra
    let _ : IsScalarTower R ((⊥ : Ideal R).ResidueField) A :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        simpa [RingHom.algebraMap_toAlgebra] using eBase.commutes x
    have hbij :
        Function.Bijective
          (IsScalarTower.toAlgHom
            ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal R).ResidueField) A) := by
      simpa [RingHom.algebraMap_toAlgebra] using eBase.bijective
    let eBaseκ :
        ((⊥ : Ideal R).ResidueField) ≃ₐ[((⊥ : Ideal R).ResidueField)] A :=
      AlgEquiv.ofBijective
        (IsScalarTower.toAlgHom
          ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal R).ResidueField) A)
        hbij
    have hGeomA :
        IsGeometricallyRegular ((⊥ : Ideal R).ResidueField) A := by
      let _ : IsGeometricallyRegular
          ((⊥ : Ideal R).ResidueField) ((⊥ : Ideal R).ResidueField) := inferInstance
      exact Algebra.isGeometricallyRegular_of_algEquiv eBaseκ.symm
    let _ : IsGeometricallyRegular ((⊥ : Ideal R).ResidueField) A := hGeomA
    exact
      Algebra.isGeometricallyRegular_of_algEquiv
        (zero_prime_formalFiber_algEquiv_localizationAtBot (R := R) p hp)
  · have hDvr :=
      completed_localizationAtPrime_isDiscreteValuationRing_of_nonzero_prime
        (R := R) p hp
    let A := Localization.AtPrime p.asIdeal
    let ACompletion := AdicCompletion (maximalIdeal A) A
    let eZero : FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) :=
      zero_prime_residueField_algEquiv_fractionRing (R := R)
    let _ : CharZero ((⊥ : Ideal R).ResidueField) := by
      exact eZero.symm.toRingEquiv.charZero
    let _ : PerfectField ((⊥ : Ideal R).ResidueField) := PerfectField.ofCharZero
    let _ :
        Algebra.IsSeparableOver ((⊥ : Ideal R).ResidueField) (FractionRing ACompletion) :=
      Algebra.IsSeparableOver.of_perfectField
    have hGeomFrac :
        IsGeometricallyRegular ((⊥ : Ideal R).ResidueField) (FractionRing ACompletion) :=
      field_isGeometricallyRegular_of_isSeparableOver
    let _ : IsGeometricallyRegular
        ((⊥ : Ideal R).ResidueField) (FractionRing ACompletion) := hGeomFrac
    -- Route correction: after the zero-prime branch is closed directly, the nonzero generic case
    -- is reduced to one packaged `κ(0)`-linear identification of the formal fiber with the
    -- fraction field of the completed DVR.
    let _ := hDvr
    exact
      Algebra.isGeometricallyRegular_of_algEquiv
        (generic_nonzero_formalFiber_algEquiv_fractionRing_of_completion
          (R := R) p hp)

/-- Helper for Proposition 15.50.12: the closed formal fiber over a nonzero prime of a Dedekind
domain is geometrically regular. -/
lemma closed_formalFiber_isGeometricallyRegular_of_dedekind_nonzero_prime
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    IsGeometricallyRegular p.asIdeal.ResidueField
      (p.asIdeal.Fiber (R̂_[p])) := by
  let A := Localization.AtPrime p.asIdeal
  let _ := completed_localizationAtPrime_isDiscreteValuationRing_of_nonzero_prime
    (R := R) p hp
  -- Route correction: the only remaining closed-branch work is the direct `κ(p)`-linear
  -- comparison from the formal fiber to the completion residue field. Once that adapter is in
  -- place, the target is a field obtained from `ResidueField A` by the completion residue-field
  -- equivalence.
  have hGeomRes :
      IsGeometricallyRegular p.asIdeal.ResidueField (ResidueField (AdicCompletion
        (maximalIdeal A) A)) :=
    completion_residueField_isGeometricallyRegular_over_primeResidueField (R := R) p
  let _ : IsGeometricallyRegular p.asIdeal.ResidueField (ResidueField ACompletion) := hGeomRes
  exact
    Algebra.isGeometricallyRegular_of_algEquiv
      (closed_nonzero_formalFiber_algEquiv_completion_residueField
        (R := R) p hp)

-- Proof sketch: a Dedekind domain is Noetherian and has Krull dimension at most `1`. Localizing
-- at a nonzero prime gives a discrete valuation ring, whose completion is again a discrete
-- valuation ring, so the defining formal fibres are geometrically regular; the zero prime gives
-- the fraction field case.
/-- Proposition 15.50.12: a Dedekind domain whose fraction field has characteristic zero is a
`G`-ring. -/
@[stacks 07PX]
instance isGRing_of_isDedekindDomain_of_fractionRing_charZero : IsGRing R := by
  -- Proof comment: use the prime-pair criterion and split the source-faithful Dedekind-domain
  -- geometry into the generic branch `q = 0` and the closed branch `q = p ≠ 0`.
  refine (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular (R := R)).2 ?_
  intro p q hqp
  rcases prime_pair_eq_bot_or_eq_of_dedekind (R := R) p q hqp with hqbot | rfl
  · -- Proof comment: this is the generic-fiber branch. The remaining missing bridge is an
    -- explicit identification of `κ(0) ⊗[R] R̂_[p]` with the fraction field of the completed
    -- DVR when `p ≠ 0`, together with the trivial field case when `p = 0`.
    simpa [hqbot] using
      generic_formalFiber_isGeometricallyRegular_of_dedekind_prime (R := R) p
  · -- Proof comment: this is the closed-fiber branch at a nonzero prime. The missing bridge is
    -- an explicit algebra equivalence between the fiber over `p` and the residue field of the
    -- completed DVR, after which geometric regularity follows from the residue-field bijection.
    exact
      closed_formalFiber_isGeometricallyRegular_of_dedekind_nonzero_prime
        (R := R) p <| by
          intro hp
          exact p.asIdeal.ne_top <| hp.symm ▸ Ideal.bot_eq_top

end

section

/- Proposition 15.50.12: the ring of integers `ℤ` is a `G`-ring, by the
Dedekind-domain characteristic-zero instance above. -/
#check (inferInstance : IsGRing ℤ)

end

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: finite type algebras are essentially finite type, so this is the finite-type
-- specialization of Proposition `15.50.10`.
/-- Proposition 15.50.12: a finite type algebra over a `G`-ring is again a `G`-ring. -/
@[stacks 07PX]
theorem isGRing_of_finiteType [IsGRing R] [Algebra.FiniteType R S] : IsGRing S := by
  -- Proof comment: finite type is a special case of essential finite type, so the canonical
  -- transfer theorem applies directly.
  exact isGRing_of_essFiniteType R

end
