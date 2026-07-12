import Mathlib
import StacksProject_2024.Chap10.Lemma_10_120_18
import StacksProject_2024.Chap10.Lemma_10_121_8
import StacksProject_2024.Chap10.Lemma_10_160_2
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Proposition_10_162_16
import StacksProject_2024.Chap15.Definition_15_47_1
import StacksProject_2024.Chap15.Lemma_15_10_5
import StacksProject_2024.Chap15.Lemma_15_47_3
import StacksProject_2024.Chap15.Lemma_15_47_6
import StacksProject_2024.Chap15.Lemma_15_48_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling:
- primary domain: commutative algebra of the chapter owner `IsJ2Ring`, together with the standard
  complete-local, one-dimensional local, Nagata, Dedekind, and finite-type stability sources for
  the `J-2` property;
- sampled owner declarations of the same kind:
  `IsJ2Ring`,
  `isJ2Ring_iff_forall_finiteType_isJ1`,
  `NagataRing`,
  `IsCompleteLocalRing`;
- best owner abstraction: the public surface should stay on the canonical owner `IsJ2Ring`; pure
  specialization clauses such as the field and integer cases should use direct recall or instance
  inference rather than parallel local wrapper declarations;
- primitive vs. derived: the primitive public data are the ambient ring hypotheses for each source
  clause. The `J-1` conclusions for finite type algebras are derived from `IsJ2Ring`, so this file
  should not introduce any auxiliary data packaging around them.

Source/core/bridge triage:
- `source-facing`: the six proposition clauses listing concrete sources of `IsJ2Ring`;
- `core/canonical`: the chapter owner `IsJ2Ring`;
- `bridge/view`: the Dedekind/Nagata/complete-local specializations and the finite-type stability
  theorem.
-/

section

variable (K : Type u) [Field K]

/- Proposition 15.48.7 (1): fields are `J-2`. -/
#check (inferInstance : IsJ2Ring K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Helper for Proposition 15.48.7: complete-local structure transports across a ring
equivalence. -/
theorem isCompleteLocalRing_of_ringEquiv
    {S : Type*} [CommRing S] {T : Type*} [CommRing T] (e : S ≃+* T)
    [IsCompleteLocalRing T] :
    IsCompleteLocalRing S := by
  -- Transport locality and maximal-ideal adic completeness across the ring equivalence.
  letI : IsLocalRing S := e.toRingEquiv.isLocalRing
  letI : IsAdicComplete (maximalIdeal S) S := by
    rw [← IsAdicComplete.congr_ringEquiv (maximalIdeal S) e.toRingEquiv]
    simpa [IsLocalRing.map_ringEquiv_maximalIdeal] using
      (inferInstance : IsAdicComplete (maximalIdeal T) T)
  infer_instance

/-- Helper for Proposition 15.48.7: a finite product of complete local rings is complete local as
soon as the total product is a domain. -/
theorem isCompleteLocalRing_pi_of_isDomain
    {ι : Type*} [Fintype ι] (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, IsCompleteLocalRing (S i)] [IsDomain ((i : ι) → S i)] :
    IsCompleteLocalRing ((i : ι) → S i) := by
  classical
  -- A domain-valued product must have at least one nontrivial factor.
  have h_exists_nontrivial : ∃ i, Nontrivial (S i) := by
    by_contra hnone
    have hsub : Subsingleton ((i : ι) → S i) := by
      refine ⟨?_⟩
      intro x y
      funext i
      have hsub_i : Subsingleton (S i) := by
        exact not_nontrivial_iff_subsingleton.mp (by
          intro hi
          exact hnone ⟨i, hi⟩)
      exact Subsingleton.elim _ _
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  obtain ⟨i0, hi0⟩ := h_exists_nontrivial
  let _ : Nontrivial (S i0) := hi0
  -- Any second nontrivial factor would create zero divisors via coordinate idempotents.
  have hsub_factor : ∀ j : ι, j ≠ i0 → Subsingleton (S j) := by
    intro j hj
    have hnot_nontrivial : ¬ Nontrivial (S j) := by
      intro hj_nontrivial
      let _ : Nontrivial (S j) := hj_nontrivial
      have hmul :
          (Pi.single i0 (1 : S i0) : (i : ι) → S i) * Pi.single j (1 : S j) = 0 := by
        ext k
        by_cases hki : k = i0
        · subst hki
          simp [hj]
        · by_cases hkj : k = j
          · subst hkj
            simp [hki]
          · simp [hki, hkj]
      rcases mul_eq_zero.mp hmul with hleft | hright
      · have h10 : (1 : S i0) = 0 := by
          simpa [Pi.single_apply] using congrArg (fun f ↦ f i0) hleft
        exact one_ne_zero h10
      · have h10 : (1 : S j) = 0 := by
          simpa [Pi.single_apply, hj] using congrArg (fun f ↦ f j) hright
        exact one_ne_zero h10
    exact not_nontrivial_iff_subsingleton.mp hnot_nontrivial
  let e : ((i : ι) → S i) ≃+* S i0 :=
    { toFun := fun f ↦ f i0
      invFun := fun x j ↦ if h : j = i0 then by
          subst h
          exact x
        else
          0
      left_inv := by
        intro f
        funext j
        by_cases hj : j = i0
        · subst hj
          simp
        · let _ : Subsingleton (S j) := hsub_factor j hj
          exact Subsingleton.elim _ _
      right_inv := by
        intro x
        simp
      map_mul' := by
        intro x y
        simp
      map_add' := by
        intro x y
        simp
      map_zero' := rfl
      map_one' := rfl }
  -- The product is ring-equivalent to its unique nontrivial factor, hence complete local.
  exact isCompleteLocalRing_of_ringEquiv e

/-- Helper for Proposition 15.48.7: a finite domain over a Noetherian complete local ring is
`J-0`. -/
theorem isJ0Ring_of_finite_domain_over_noetherian_completeLocalRing
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A] [IsDomain A] :
    IsJ0Ring A :=
by
  -- Collapse the completed-local product decomposition to a single complete-local factor.
  let e := finiteProductOfNoetherianCompleteLocalRings_of_finite (R := R) (S := A)
  letI :
      IsCompleteLocalRing
        (∀ q : (maximalIdeal R).primesOver A,
          AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
            (Localization.AtPrime q.1)) :=
    isCompleteLocalRing_pi_of_isDomain
      (S := fun q : (maximalIdeal R).primesOver A ↦
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
          (Localization.AtPrime q.1))
  letI : IsCompleteLocalRing A := isCompleteLocalRing_of_ringEquiv e
  -- Lemma `15.48.6` closes the domain case once the complete-local owner is in place.
  exact isJ0Ring_of_noetherian_completeLocalDomain (A := A)

/-- Proposition 15.48.7 (1): a Noetherian complete local ring is `J-2`. -/
-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra is a finite
-- product of Noetherian complete local rings, so by Lemma `15.47.3` it suffices to handle the
-- domain case. That domain case is Lemma `15.48.6`.
instance isJ2Ring_of_noetherian_completeLocalRing : IsJ2Ring R := by
  let htfae :=
    isJ2Ring_tfae_finiteType_domain_isJ0_finite_algebra_isJ1_purelyInseparable_residueField_extension
      (R := R)
  -- Route correction: execute clause `(3) -> (1)` exactly as in the source and reduce finite
  -- algebras to prime quotients that are finite domain algebras over `R`.
  refine (htfae.out 2 0) ?_
  intro A _ _ _
  -- Each prime quotient is again a finite domain over `R`, so the helper supplies the `J-0`
  -- input required by Lemma `15.47.3`.
  exact
    _root_.isJ1Ring_of_isJ0Ring_quotient_by_prime (R := A) fun p ↦ by
      letI : Algebra R (A ⧸ p.asIdeal) := inferInstance
      letI : Module.Finite R (A ⧸ p.asIdeal) := inferInstance
      letI : IsDomain (A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
      exact isJ0Ring_of_finite_domain_over_noetherian_completeLocalRing (R := R)

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Helper for Proposition 15.48.7: the generic localization of a domain is a regular local ring,
because it identifies with the fraction field. -/
theorem isRegularLocalRing_localizationAtPrime_bot_of_isDomain
    {A : Type v} [CommRing A] [IsDomain A] :
    IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A)) := by
  -- Identify the localization at the generic point with the fraction field of the domain.
  letI : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization ((⊥ : Ideal A).primeCompl)
        (Localization.AtPrime (⊥ : Ideal A)))
  letI : IsRegularLocalRing (FractionRing A) := by infer_instance
  let e : FractionRing A ≃ₐ[A] Localization.AtPrime (⊥ : Ideal A) :=
    FractionRing.algEquiv A (Localization.AtPrime (⊥ : Ideal A))
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- Helper for Proposition 15.48.7: a finite algebra over a local ring has only finitely many
maximal ideals, since every maximal ideal lies over the unique maximal ideal of the base. -/
theorem finite_maximalSpectrum_of_moduleFinite_local
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A] :
    Finite (MaximalSpectrum A) := by
  classical
  letI : Finite ((maximalIdeal R).primesOver A) :=
    Algebra.QuasiFinite.finite_primesOver (R := R) (S := A) (maximalIdeal R)
  let f : MaximalSpectrum A → (maximalIdeal R).primesOver A := fun m ↦ by
    letI : m.asIdeal.LiesOver (maximalIdeal R) := by
      exact
        ⟨(IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m.asIdeal)).symm⟩
    exact Ideal.primesOver.mk (maximalIdeal R) m.asIdeal
  exact Finite.of_injective f fun m n hmn ↦ by
    apply Subtype.ext
    simpa using congrArg Subtype.val hmn

/-- Helper for Proposition 15.48.7: a finite family of closed points in a prime spectrum is a
closed subset. -/
theorem isClosed_of_finite_subset_closedPoints
    {A : Type v} [CommRing A] {X : Set (PrimeSpectrum A)}
    (hXfinite : X.Finite) (hXclosed : X ⊆ closedPoints (PrimeSpectrum A)) :
    IsClosed X := by
  classical
  let s := hXfinite.toFinset
  have hXeq :
      X = ⋃ x ∈ s, ({x} : Set (PrimeSpectrum A)) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.2 ?_
      refine ⟨x, Set.mem_iUnion.2 ?_⟩
      refine ⟨by simpa [s] using hXfinite.mem_toFinset hx, ?_⟩
      simp
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨x', hx'⟩
      rcases Set.mem_iUnion.1 hx' with ⟨hx'fin, hx'x⟩
      simpa using hx'x
  rw [hXeq]
  refine isClosed_biUnion_finset fun x hx ↦ ?_
  have hxclosed : x ∈ closedPoints (PrimeSpectrum A) := hXclosed (by simpa [s] using hx)
  simpa [closedPoints] using hxclosed

/-- Helper for Proposition 15.48.7: a finite domain over a one-dimensional Noetherian local ring
is `J-0`. -/
theorem isJ0Ring_of_finite_domain_over_noetherian_local_ring_dimension_one
    (hdim : ringKrullDim R = 1) {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    [IsDomain A] :
    IsJ0Ring A :=
by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  letI : Finite (MaximalSpectrum A) :=
    finite_maximalSpectrum_of_moduleFinite_local (R := R) (A := A)
  have hdim_le : ringKrullDim R ≤ 1 := by
    simpa [hdim]
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim_le
  -- Route correction: the remaining source-faithful step is to show that every nonregular prime
  -- is maximal, so the singular locus is a finite union of closed points.
  -- TODO: pass to the quotient domain `R / ker(R → A)`, localize at a maximal ideal above a
  -- nonmaximal nonzero prime, and contradict `Ring.KrullDimLE 1` via
  -- `two_le_ringKrullDim_of_zero_lt_lt_maximalIdeal`; then close `J-1` using the finite closed
  -- singular locus and conclude `J-0` by `isJ0Ring_of_isJ1Ring_domain`.
  sorry

-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra has finite
-- spectrum; because the regular locus is stable under generalization, it is open, so every finite
-- `R`-algebra is `J-1`.
/-- Proposition 15.48.7 (3): a Noetherian local ring of Krull dimension `1` is `J-2`. -/
@[stacks 07PJ]
theorem isJ2Ring_of_noetherian_local_ring_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := by
  let htfae :=
    isJ2Ring_tfae_finiteType_domain_isJ0_finite_algebra_isJ1_purelyInseparable_residueField_extension
      (R := R)
  -- Route correction: again use clause `(3) -> (1)`, but now the one-dimensional local helper
  -- packages the source argument for finite domain algebras.
  refine (htfae.out 2 0) ?_
  intro A _ _ _
  -- Prime quotients of finite algebras stay finite over the same base, so the helper applies
  -- uniformly after passing to `A ⧸ p`.
  exact
    _root_.isJ1Ring_of_isJ0Ring_quotient_by_prime (R := A) fun p ↦ by
      letI : Algebra R (A ⧸ p.asIdeal) := inferInstance
      letI : Module.Finite R (A ⧸ p.asIdeal) := inferInstance
      letI : IsDomain (A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
      exact
        isJ0Ring_of_finite_domain_over_noetherian_local_ring_dimension_one
          (R := R) hdim

end

section

variable (R : Type u) [CommRing R] [NagataRing R]

/-- Helper for Proposition 15.48.7: a one-dimensional Nagata ring supplies the clause `(4)`
`J-0` model for every finite purely inseparable residue-field extension. -/
theorem exists_j0_model_of_purelyInseparable_extension_for_nagataRing_dimension_one
    (hdim : ringKrullDim R = 1)
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L] :
    let _ : Algebra R L :=
      RingHom.toAlgebra
        ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
    let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower R A L)
      (_ : IsFractionRing A L),
      IsJ0Ring A :=
by
  let _ : Algebra R L :=
    RingHom.toAlgebra
      ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
  let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  by_cases hpmax : p.IsMaximal
  · -- In the maximal branch, the field extension itself is the required finite `J-0` model.
    letI : Module.Finite R p.ResidueField := inferInstance
    letI : Module.Finite R L := Module.Finite.trans p.ResidueField L
    letI : Algebra L L := inferInstance
    letI : IsScalarTower R L L := by infer_instance
    letI : IsFractionRing L L := IsFractionRing.idem L L
    letI : IsJ0Ring L := isJ0Ring_of_isRegularRing L
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance⟩
  · -- TODO: in the nonmaximal branch, first show that `p` is minimal in dimension one, then pass
    -- to `R / p`, use Nagata finiteness of the normalization in `L`, identify the normalization as
    -- a one-dimensional normal domain, and conclude regularity and hence `J-0`.
    let _ := hdim
    let _ := hpmax
    sorry

-- Proof sketch: use condition `(4)` of Lemma `15.47.6`. For a prime `p` and a finite purely
-- inseparable extension of its residue field, if `p` is maximal then the extension ring is finite
-- over a field and hence regular; if `p` is minimal, the Nagata property makes the integral
-- closure finite, and in dimension `1` that normal domain is regular.
/-- Proposition 15.48.7 (4): a Nagata ring of Krull dimension `1` is `J-2`. -/
@[stacks 07PJ]
theorem isJ2Ring_of_nagataRing_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := by
  let htfae :=
    isJ2Ring_tfae_finiteType_domain_isJ0_finite_algebra_isJ1_purelyInseparable_residueField_extension
      (R := R)
  -- Execute clause `(4) -> (1)` exactly: the helper is stated with the same owner-facing clause
  -- as the TFAE theorem, so the final step is a direct application.
  exact
    (htfae.out 3 0)
      (exists_j0_model_of_purelyInseparable_extension_for_nagataRing_dimension_one
        (R := R) hdim)

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Helper for Proposition 15.48.7: a nonfield Dedekind domain has Krull dimension `1`. -/
theorem ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField
    (hR : ¬ IsField R) :
    ringKrullDim R = 1 :=
by
  -- Repackage the Krull dimension as a natural number using the standard non-bottom/non-top API.
  have hdim_eq :
      ringKrullDim R =
        ((((ringKrullDim R).unbotD 0).toNat : ℕ∞) : WithBot ℕ∞) := by
    have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
    cases hs : ringKrullDim R with
    | bot =>
        exact (hbot hs).elim
    | coe d =>
        have hd_ne_top : d ≠ ⊤ := by
          intro hd_top
          exact htop <| by simp [hs, hd_top]
        simpa [hs] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hd_ne_top).symm
  have hdimle1_inst : Ring.KrullDimLE 1 R := by
    infer_instance
  have hdimle1 : ringKrullDim R ≤ 1 := Ring.krullDimLE_iff.mp hdimle1_inst
  have hnat_ne_zero : ((ringKrullDim R).unbotD 0).toNat ≠ 0 := by
    intro hzero
    have hdim0 : ringKrullDim R = 0 := by
      simpa [hzero] using hdim_eq
    let _ : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
    exact hR (Ring.KrullDimLE.isField_of_isDomain (R := R))
  obtain ⟨d, hd⟩ :
      ∃ d : ℕ, ((ringKrullDim R).unbotD 0).toNat = d.succ :=
    Nat.exists_eq_succ_of_ne_zero hnat_ne_zero
  have hdim_succ : ringKrullDim R = d.succ := by
    simpa [hd] using hdim_eq
  have hd_le : d.succ ≤ 1 := by
    exact_mod_cast (by simpa [hdim_succ] using hdimle1)
  have hd_zero : d = 0 := by
    omega
  -- The only nonzero dimension compatible with the Dedekind-domain bound is `1`.
  simpa [hd_zero] using hdim_succ

/-- Proposition 15.48.7 (5): a Dedekind domain whose fraction field has characteristic zero is
`J-2`. -/
-- Proof sketch: such a ring is Nagata by Proposition `10.162.16`, and a Dedekind domain has
-- Krull dimension `1`; apply the one-dimensional Nagata case.
instance isJ2Ring_of_isDedekindDomain_of_fractionRing_charZero : IsJ2Ring R := by
  by_cases hfield : IsField R
  · -- In the field branch, reuse the canonical field instance directly.
    letI : Field R := hfield.toField
    refine ⟨?_⟩
    intro A _ _ _
    -- Over a field, the existing finite-type `J-1` owner applies directly.
    infer_instance
  · -- Otherwise the source reduces the Dedekind case to the one-dimensional Nagata case.
    letI : NagataRing R := nagataRing_of_isDedekindDomain_of_fractionRing_charZero (R := R)
    exact
      isJ2Ring_of_nagataRing_dimension_one (R := R)
        (ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField (R := R) hfield)

end

section

/- Proposition 15.48.7 (2): the ring of integers `ℤ` is `J-2`, by the Dedekind-domain
characteristic-zero instance above. -/
#check (inferInstance : IsJ2Ring ℤ)

end

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Proposition 15.48.7 (6): finite type ring extensions of `J-2` rings are `J-2`. -/
-- Proof sketch: if `T` is a finite type `S`-algebra, then by transitivity it is a finite type
-- `R`-algebra. Since `R` is `J-2`, the ring `T` is `J-1`, so `S` satisfies the defining `J-2`
-- condition.
theorem isJ2Ring_of_finiteType [IsJ2Ring R] [Algebra.FiniteType R S] :
    IsJ2Ring S := by
  -- Unpack the definition and test the target ring against an arbitrary finite type `S`-algebra.
  refine ⟨?_⟩
  intro A _ _ _
  -- Compose the finite type structures along `R → S → A`, then invoke the ambient `J-2`
  -- property of `R` on the resulting finite type `R`-algebra.
  letI : Algebra R A := ((algebraMap S A).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FiniteType R A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R S) (inferInstance : Algebra.FiniteType S A)
  infer_instance

end
