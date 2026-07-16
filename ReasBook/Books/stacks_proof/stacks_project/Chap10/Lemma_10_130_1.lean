import stacks_proof.stacks_project.Chap10.Definition_10_103_1
import stacks_proof.stacks_project.Chap10.Definition_10_125_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_9
import stacks_proof.stacks_project.Chap10.Lemma_10_112_6
import stacks_proof.stacks_project.Chap10.Lemma_10_122_4
import stacks_proof.stacks_project.Chap10.Lemma_10_125_4
import stacks_proof.stacks_project.Chap10.Lemma_10_113_1.DimensionEquality
import stacks_proof.stacks_project.Chap10.Lemma_10_114_7
import stacks_proof.stacks_project.Chap10.Lemma_10_128_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {k : Type u} [Field k]
variable {d : ℕ}
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "P" => MvPolynomial (Fin d) k

/-- Helper for Chap10 Lemma 10 130 1: localizing the self-module of a ring at a prime agrees
with the localized ring itself. -/
private noncomputable abbrev localizedSelfLinearEquivAtPrime
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p R ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl R).trans
    (Algebra.TensorProduct.rid R (Localization.AtPrime p) (Localization.AtPrime p)).toLinearEquiv

/-- Helper for Chap10 Lemma 10 130 1: membership in the flat locus can be rewritten as flatness
of the localized ring over the localized polynomial base at the contracted prime. -/
private lemma mem_flatOverBaseLocus_iff_flat_localizationAtPrime_under
    (π : P →ₐ[k] S) (q : PrimeSpectrum S) :
    let _ : Algebra P S := π.toAlgebra
    let p : Ideal P := q.asIdeal.under P
    q ∈ Module.flatOverBaseLocus P S S ↔
      Module.Flat (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := by
  dsimp
  letI : Algebra P S := π.toAlgebra
  let p : Ideal P := q.asIdeal.under P
  have hflat :
      q ∈ Module.flatOverBaseLocus P S S ↔
        Module.Flat (Localization.AtPrime p) (LocalizedModule.AtPrime q.asIdeal S) := by
    -- Proof comment: rewrite the flat-locus owner through the standard localization criterion for
    -- flatness over the contracted source prime.
    rw [Module.mem_flatOverBaseLocus]
    exact Module.flat_iff_of_isLocalization
      (Localization.AtPrime p) p.primeCompl (M := LocalizedModule.AtPrime q.asIdeal S)
  constructor
  · intro hq
    letI : Module.Flat (Localization.AtPrime p) (LocalizedModule.AtPrime q.asIdeal S) :=
      hflat.mp hq
    -- Proof comment: identify the localized self-module with the localized ring itself.
    exact Module.Flat.of_linearEquiv (localizedSelfLinearEquivAtPrime q.asIdeal)
  · intro hq
    letI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := hq
    have hself :
        Module.Flat (Localization.AtPrime p) (LocalizedModule.AtPrime q.asIdeal S) := by
      -- Proof comment: use the same linear equivalence in the reverse direction.
      exact Module.Flat.of_linearEquiv (localizedSelfLinearEquivAtPrime q.asIdeal).symm
    exact hflat.mpr hself

/-- Helper for Chap10 Lemma 10 130 1: the Krull dimension of a Noetherian local ring comes from
an actual natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] :
    ∃ n : ℕ, ringKrullDim T = n := by
  -- Proof comment: the local Noetherian hypotheses exclude both `⊥` and `⊤`, so the ENat-valued
  -- dimension is represented by its natural-number part.
  have hbot : ringKrullDim T ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim T ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim T).unbot hbot).toNat
  have hneTop : (ringKrullDim T).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim T).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim T = (ringKrullDim T).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim T) hbot).symm
    _ = n := hdim'

/-- Helper for Chap10 Lemma 10 130 1: on an irreducible affine finite-type spectrum, local
topological Krull dimension agrees with the global ring Krull dimension. -/
private theorem topologicalKrullDimAt_eq_ringKrullDim_of_irreducibleSpectrum
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A]
    [Algebra.FiniteType F A] [IsDomain A] (z : PrimeSpectrum A) :
    topologicalKrullDimAt z = ringKrullDim A := by
  -- Proof comment: an irreducible affine spectrum has only the whole space as an irreducible
  -- component through any chosen point.
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := F) (S := A) z]
  letI : Subsingleton
      { Z : irreducibleComponents (PrimeSpectrum A) // z ∈ (Z : Set (PrimeSpectrum A)) } := by
    refine ⟨fun Z W ↦ Subtype.ext ?_⟩
    apply Subtype.ext
    have hZ : (Z.1 : Set (PrimeSpectrum A)) = Set.univ := by
      simpa [irreducibleComponents_eq_singleton] using Z.1.2
    have hW : (W.1 : Set (PrimeSpectrum A)) = Set.univ := by
      simpa [irreducibleComponents_eq_singleton] using W.1.2
    exact hZ.trans hW.symm
  have hmem_univ : Set.univ ∈ irreducibleComponents (PrimeSpectrum A) := by
    rw [irreducibleComponents_eq_singleton]
    simp
  have hz_univ : z ∈ (Set.univ : Set (PrimeSpectrum A)) := Set.mem_univ z
  let Z0 : { Z : irreducibleComponents (PrimeSpectrum A) // z ∈ (Z : Set (PrimeSpectrum A)) } :=
    ⟨⟨Set.univ, hmem_univ⟩, hz_univ⟩
  have huniv :
      topologicalKrullDim (Set.univ : Set (PrimeSpectrum A)) =
        topologicalKrullDim (PrimeSpectrum A) := by
    simpa using IsHomeomorph.topologicalKrullDim_eq
      (Homeomorph.Set.univ (PrimeSpectrum A))
      (Homeomorph.Set.univ (PrimeSpectrum A)).isHomeomorph
  calc
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum A) // z ∈ (Z : Set (PrimeSpectrum A)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum A))) =
        topologicalKrullDim (Z0 : Set (PrimeSpectrum A)) :=
      ciSup_subsingleton Z0 _
    _ = topologicalKrullDim (Set.univ : Set (PrimeSpectrum A)) := by
      simp [Z0]
    _ = topologicalKrullDim (PrimeSpectrum A) := huniv
    _ = ringKrullDim A := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

/-- Helper for Chap10 Lemma 10 130 1: every point of affine `d`-space over a field has local
topological Krull dimension `d`. -/
private theorem topologicalKrullDimAt_mvPolynomial_eq_nat
    {F : Type*} [Field F] (n : ℕ) (y : PrimeSpectrum (MvPolynomial (Fin n) F)) :
    topologicalKrullDimAt y = (n : WithBot ℕ∞) := by
  -- Proof comment: the polynomial ring itself has Krull dimension equal to its number of
  -- variables, and the local dimension collapses to that global value because affine space is
  -- irreducible.
  calc
    topologicalKrullDimAt y = ringKrullDim (MvPolynomial (Fin n) F) :=
      topologicalKrullDimAt_eq_ringKrullDim_of_irreducibleSpectrum (F := F) y
    _ = (n : WithBot ℕ∞) := by
      simp

/- The next helper block isolates the quotient/transcendence/coheight part of the old
`10.116.3` dependency.  This is compile-safe in the current file and reduces the remaining blocker
to the domain height-plus-residue-field formula, rather than the entire local-dimension theorem. -/
/-- Helper for Chap10 Lemma 10 130 1: a finite-type domain over a field has Krull dimension equal
to the transcendence degree of its fraction field over the base field. -/
private theorem ringKrullDim_eq_trdeg_of_finiteType_domain
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = (Cardinal.toNat (Algebra.trdeg k A) : WithBot ℕ∞) := by
  obtain ⟨n, g, hg_injective, hg_finite⟩ := exists_finite_inj_algHom_of_fg k A
  have hdim : ringKrullDim A = n := by
    -- Proof comment: Noether normalization makes `A` integral over a polynomial ring in `n`
    -- variables, so the Krull dimension is exactly `n`.
    let _ : Algebra (MvPolynomial (Fin n) k) A := g.toAlgebra
    have hg_integral : (algebraMap (MvPolynomial (Fin n) k) A).IsIntegral := by
      simpa [RingHom.algebraMap_toAlgebra] using hg_finite.to_isIntegral
    let _ : Algebra.IsIntegral (MvPolynomial (Fin n) k) A :=
      algebraMap_isIntegral_iff.mp hg_integral
    have hdim' :
        ringKrullDim (MvPolynomial (Fin n) k) = ringKrullDim A :=
      ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
        (by simpa [RingHom.algebraMap_toAlgebra] using hg_injective)
    calc
      ringKrullDim A = ringKrullDim (MvPolynomial (Fin n) k) := hdim'.symm
      _ = n := by simp
  have htrdeg : Cardinal.toNat (Algebra.trdeg k A) = n := by
    -- Proof comment: the same normalization makes `A` algebraic over the polynomial subalgebra,
    -- so the tower transcendence degree collapses to the polynomial-ring term.
    let _ : Algebra (MvPolynomial (Fin n) k) A := g.toAlgebra
    let _ : IsScalarTower k (MvPolynomial (Fin n) k) A := by
      refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
      simp [RingHom.algebraMap_toAlgebra]
    let _ : FaithfulSMul (MvPolynomial (Fin n) k) A :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
        simpa [RingHom.algebraMap_toAlgebra] using hg_injective)
    have hIntegral : Algebra.IsIntegral (MvPolynomial (Fin n) k) A :=
      algebraMap_isIntegral_iff.mp (by
        simpa [RingHom.algebraMap_toAlgebra] using hg_finite.to_isIntegral)
    let _ : Algebra.IsIntegral (MvPolynomial (Fin n) k) A := hIntegral
    let _ : Algebra.IsAlgebraic (MvPolynomial (Fin n) k) A :=
      Algebra.IsIntegral.isAlgebraic
    have hzero : Algebra.trdeg (MvPolynomial (Fin n) k) A = 0 :=
      trdeg_eq_zero (R := MvPolynomial (Fin n) k) (A := A)
    have hadd := lift_trdeg_add_eq (R := k) (S := MvPolynomial (Fin n) k) (A := A)
    have hlift :
        Cardinal.lift.{v, u} (Algebra.trdeg k (MvPolynomial (Fin n) k)) =
          Cardinal.lift.{u, v} (Algebra.trdeg k A) := by
      simpa [hzero] using hadd
    have htoNat :
        Cardinal.toNat (Algebra.trdeg k A) =
          Cardinal.toNat (Algebra.trdeg k (MvPolynomial (Fin n) k)) := by
      rw [← Cardinal.toNat_lift.{u, v} (Algebra.trdeg k A),
        ← Cardinal.toNat_lift.{v, u} (Algebra.trdeg k (MvPolynomial (Fin n) k)), hlift]
    rw [htoNat, MvPolynomial.trdeg_of_isDomain, Cardinal.toNat_lift, Cardinal.mk_fin,
      Cardinal.toNat_natCast]
  rw [hdim, htrdeg]

/-- Helper for Chap10 Lemma 10 130 1: for a finite-type domain over a field, replacing both
rings by their fraction fields does not change the natural-number transcendence degree. -/
private theorem fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) =
      Cardinal.toNat (Algebra.trdeg k A) := by
  -- Proof comment: the base-field fraction field is algebraic over `k`, and `Frac(A)` is
  -- algebraic over `A`, so the tower formula collapses both transcendence contributions.
  have hbase_zero : Algebra.trdeg k (FractionRing k) = 0 := by
    exact trdeg_eq_zero (R := k) (A := FractionRing k)
  have hfracA : Algebra.trdeg k (FractionRing A) = Algebra.trdeg k A := by
    have hadd := trdeg_add_eq (R := k) (S := A) (A := FractionRing A)
    have hz : Algebra.trdeg A (FractionRing A) = 0 := by
      have : Algebra.IsAlgebraic A (FractionRing A) :=
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
      exact trdeg_eq_zero (R := A) (A := FractionRing A)
    simpa [hz] using hadd.symm
  letI : FaithfulSMul (FractionRing k) (FractionRing A) :=
    FaithfulSMul.of_field_isFractionRing (FractionRing k) (FractionRing A)
      (FractionRing k) (FractionRing A)
  have hsum := lift_trdeg_add_eq (R := k) (S := FractionRing k) (A := FractionRing A)
  have hlift_eq :
      Cardinal.lift.{u, v} (Algebra.trdeg (FractionRing k) (FractionRing A)) =
        Cardinal.lift.{u, v} (Algebra.trdeg k (FractionRing A)) := by
    simpa [hbase_zero] using hsum
  calc
    Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) =
        Cardinal.toNat (Cardinal.lift.{u, v}
          (Algebra.trdeg (FractionRing k) (FractionRing A))) := by
      exact (Cardinal.toNat_lift.{u, v} _).symm
    _ = Cardinal.toNat (Cardinal.lift.{u, v} (Algebra.trdeg k (FractionRing A))) := by
      rw [hlift_eq]
    _ = Cardinal.toNat (Algebra.trdeg k (FractionRing A)) := by
      exact Cardinal.toNat_lift.{u, v} _
    _ = Cardinal.toNat (Algebra.trdeg k A) := by
      rw [hfracA]

/-- Helper for Chap10 Lemma 10 130 1: the field-base height-plus-residue-field term is bounded
above by the base-field transcendence degree. -/
private theorem fieldBase_primeHeight_add_residueFieldTrdeg_toNat_le_trdeg
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) ≤
      Cardinal.toNat (Algebra.trdeg k A) := by
  -- Proof comment: normalize the imported equality support from fraction fields back to `trdeg k A`.
  have hdim :=
    fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_fractionRing_trdeg
      (k := k) (A := A) p
  have hgeneric := fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain (k := k) (A := A)
  exact le_of_eq (by simpa [hgeneric] using hdim)

/-- Helper for Chap10 Lemma 10 130 1: the base-field transcendence degree is bounded above by the
field-base height-plus-residue-field term. -/
private theorem fieldBase_trdeg_toNat_le_primeHeight_add_residueFieldTrdeg_toNat
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    Cardinal.toNat (Algebra.trdeg k A) ≤
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  -- Proof comment: the same imported equality support also yields the reverse orientation after
  -- rewriting the generic term to `trdeg k A`.
  have hdim :=
    fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_fractionRing_trdeg
      (k := k) (A := A) p
  have hgeneric := fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain (k := k) (A := A)
  exact le_of_eq (by simpa [hgeneric] using hdim.symm)

/-- Helper for Chap10 Lemma 10 130 1: the field-base dimension formula in natural-number form for
a finite-type domain. -/
private theorem fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_trdeg
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k A) := by
  -- Proof comment: combine the two inequality orientations into the equality used by the domain
  -- dimension formula.
  have hle := fieldBase_primeHeight_add_residueFieldTrdeg_toNat_le_trdeg (k := k) (A := A) p
  have hge :=
    fieldBase_trdeg_toNat_le_primeHeight_add_residueFieldTrdeg_toNat (k := k) (A := A) p
  exact le_antisymm hle hge

/-- Helper for Chap10 Lemma 10 130 1: convert the natural-number prime-height formula to the
`WithBot ℕ∞` height formula used by `ringKrullDim`. -/
private theorem primeHeight_toNat_add_coe_eq_height_add
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] (n : ℕ) :
    (((ENat.toNat (Ideal.primeHeight p) + n : ℕ) : ℕ∞) : WithBot ℕ∞) =
      (p.height : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
  -- Proof comment: Noetherianity makes prime height finite, so coercing `toNat` recovers the
  -- original `height`.
  have hfinite : Ideal.primeHeight p ≠ ⊤ := Ideal.primeHeight_ne_top p
  have hheight : p.height = Ideal.primeHeight p := Ideal.height_eq_primeHeight p
  calc
    (((ENat.toNat (Ideal.primeHeight p) + n : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((ENat.toNat (Ideal.primeHeight p) : ℕ∞) + (n : ℕ∞)) : WithBot ℕ∞) := by
      norm_num
    _ = ((Ideal.primeHeight p + (n : ℕ∞)) : WithBot ℕ∞) := by
      rw [ENat.coe_toNat hfinite]
    _ = (p.height : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
      rw [hheight]
      rfl

/-- Helper for Chap10 Lemma 10 130 1: a finite-type domain over a field satisfies the
height-plus-residue-field transcendence dimension formula at every prime. -/
private theorem finiteTypeDomain_ringKrullDim_eq_height_add_trdeg_residueField
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ringKrullDim A =
      (p.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  -- Proof comment: rewrite the domain dimension as `trdeg k A`, then convert the field-base
  -- height term from `primeHeight` back to `height`.
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hnat :=
    fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_trdeg (k := k) (A := A) p
  calc
    ringKrullDim A = (Cardinal.toNat (Algebra.trdeg k A) : WithBot ℕ∞) :=
      ringKrullDim_eq_trdeg_of_finiteType_domain (k := k) (A := A)
    _ = ((ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) : ℕ) : WithBot ℕ∞) := by
      rw [← hnat]
    _ = (p.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) :=
      primeHeight_toNat_add_coe_eq_height_add p.asIdeal
        (Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField))

/-- Helper for Chap10 Lemma 10 130 1: the residue field of a prime and the corresponding prime
quotient have the same transcendence degree over the base field. -/
private theorem trdeg_primeResidueField_eq_trdeg_quotient
    {A : Type v} [CommRing A] [Algebra k A] (I : Ideal A) [I.IsPrime] :
    Algebra.trdeg k I.ResidueField = Algebra.trdeg k (A ⧸ I) := by
  let T := A ⧸ I
  have hcomap : I = Ideal.comap (Ideal.Quotient.mk I : A →+* T) (⊥ : Ideal T) := by
    -- Proof comment: the zero prime of `A ⧸ I` contracts exactly to `I`.
    ext x
    change x ∈ I ↔ Ideal.Quotient.mk I x = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).symm
  let eResidue : I.ResidueField ≃ₐ[k] ((⊥ : Ideal T).ResidueField) :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ I (⊥ : Ideal T) (Ideal.Quotient.mkₐ k I) hcomap)
      (by
        -- Proof comment: surjectivity of the quotient map gives a bijection on the two residue
        -- fields over corresponding primes.
        simpa [T] using
          (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
            (f := (Ideal.Quotient.mk I : A →+* T))
            (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
            I (⊥ : Ideal T) hcomap))
  let eFrac : FractionRing T ≃ₐ[k] ((⊥ : Ideal T).ResidueField) := by
    -- Proof comment: for the quotient domain, the zero-prime residue field is its fraction field.
    let e : T ≃ₐ[T] T ⧸ (⊥ : Ideal T) := (AlgEquiv.quotientBot T T).symm
    letI : IsFractionRing T ((⊥ : Ideal T).ResidueField) := by
      refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
      intro x
      change algebraMap T ((⊥ : Ideal T).ResidueField) x =
        algebraMap (T ⧸ (⊥ : Ideal T)) ((⊥ : Ideal T).ResidueField)
          (Ideal.Quotient.mk _ x)
      symm
      rfl
    exact AlgEquiv.restrictScalars k (FractionRing.algEquiv T ((⊥ : Ideal T).ResidueField))
  have htrdeg_frac : Algebra.trdeg k (FractionRing T) = Algebra.trdeg k T := by
    -- Proof comment: the fraction field is algebraic over the domain `T`, so the tower formula
    -- removes the top transcendence-degree contribution.
    have hadd := trdeg_add_eq (R := k) (S := T) (A := FractionRing T)
    have hz : Algebra.trdeg T (FractionRing T) = 0 := by
      have : Algebra.IsAlgebraic T (FractionRing T) :=
        (IsFractionRing.comap_isAlgebraic_iff (A := T) (K := FractionRing T)
          (C := FractionRing T)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing T) (FractionRing T))
      exact trdeg_eq_zero (R := T) (A := FractionRing T)
    simpa [hz] using hadd.symm
  calc
    Algebra.trdeg k I.ResidueField = Algebra.trdeg k ((⊥ : Ideal T).ResidueField) := by
      simpa using AlgEquiv.trdeg_eq (R := k) eResidue
    _ = Algebra.trdeg k (FractionRing T) := by
      symm
      simpa using AlgEquiv.trdeg_eq (R := k) eFrac
    _ = Algebra.trdeg k T := htrdeg_frac
    _ = Algebra.trdeg k (A ⧸ I) := by
      rfl

/-- Helper for Chap10 Lemma 10 130 1: a prime quotient has Krull dimension equal to the
transcendence degree of that prime's residue field. -/
private theorem ringKrullDim_primeQuotient_eq_trdeg_residueField
    (p : Ideal S) [p.IsPrime] :
    ringKrullDim (S ⧸ p) =
      (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) := by
  -- Proof comment: combine the domain formula for `S ⧸ p` with the residue-field/transcendence
  -- comparison across the quotient map.
  calc
    ringKrullDim (S ⧸ p) =
        (Cardinal.toNat (Algebra.trdeg k (S ⧸ p)) : WithBot ℕ∞) :=
      ringKrullDim_eq_trdeg_of_finiteType_domain (k := k) (A := S ⧸ p)
    _ = (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) := by
      rw [← trdeg_primeResidueField_eq_trdeg_quotient (k := k) (A := S) p]

/-- Helper for Chap10 Lemma 10 130 1: the Krull dimension of a prime quotient is the coheight of
the corresponding point of the ambient spectrum. -/
private theorem ringKrullDim_quotient_eq_coheight
    (p : Ideal S) [p.IsPrime] :
    ringKrullDim (S ⧸ p) =
      (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) : WithBot ℕ∞) := by
  let y : PrimeSpectrum S := ⟨p, inferInstance⟩
  -- Proof comment: rewrite the quotient spectrum as the upper interval above `p`.
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (p : Set S) = Set.Ici y := by
    ext z
    change p ≤ z.asIdeal ↔ y ≤ z
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici y).symm

/-- Helper for Chap10 Lemma 10 130 1: the residue-field transcendence degree of a prime equals
the coheight of that point of the prime spectrum. -/
private theorem residueField_trdeg_toNat_eq_coheight
    (p : Ideal S) [p.IsPrime] :
    (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) =
      (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) : WithBot ℕ∞) := by
  -- Proof comment: compare both sides through the prime quotient `S ⧸ p`.
  calc
    (Cardinal.toNat (Algebra.trdeg k p.ResidueField) : WithBot ℕ∞) =
        ringKrullDim (S ⧸ p) :=
      (ringKrullDim_primeQuotient_eq_trdeg_residueField (k := k) (S := S) p).symm
    _ = (Order.coheight (⟨p, inferInstance⟩ : PrimeSpectrum S) : WithBot ℕ∞) :=
      ringKrullDim_quotient_eq_coheight (S := S) p

-- Route correction: the local-dimension theorem is proved by reindexing irreducible components
-- through `x` by minimal primes below `x.asIdeal`, then applying the finite-type domain formula
-- on each quotient component instead of relying on the broken aggregate `10.116.3` import.
/-- Helper for Chap10 Lemma 10 130 1: components through a point can be reindexed by minimal
primes contained in the point's prime ideal, with each component written as a zero locus. -/
private theorem
    iSup_topologicalKrullDim_irreducibleComponents_through_eq_iSup_zeroLocus_minimalPrimesBelow
    (x : PrimeSpectrum S) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
      ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1.1 : Set S)) := by
  let e :
      { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) } ≃
        { q : minimalPrimes S // q.1 ≤ x.asIdeal } := by
    refine
      { toFun := fun Z => ?_
        invFun := fun q => ?_
        left_inv := ?_
        right_inv := ?_ }
    · refine ⟨⟨PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)), ?_⟩, ?_⟩
      · rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
        rw [(isClosed_of_mem_irreducibleComponents
          (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq]
        exact Z.1.2
      · intro a ha
        exact (PrimeSpectrum.mem_vanishingIdeal
          (Z.1 : Set (PrimeSpectrum S)) a).mp ha x Z.2
    · refine ⟨⟨PrimeSpectrum.zeroLocus (q.1.1 : Set S), ?_⟩, ?_⟩
      · rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents]
        rw [Ideal.IsPrime.radical (Ideal.minimalPrimes_isPrime q.1.2)]
        exact q.1.2
      · exact (PrimeSpectrum.mem_zeroLocus x (q.1.1 : Set S)).mpr q.2
    · intro Z
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      -- Proof comment: the zero locus of the vanishing ideal is the closure, and irreducible
      -- components are already closed.
      calc
        PrimeSpectrum.zeroLocus
            (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S) =
            closure (Z.1 : Set (PrimeSpectrum S)) :=
          PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _
        _ = (Z.1 : Set (PrimeSpectrum S)) :=
          (isClosed_of_mem_irreducibleComponents
            (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq
    · intro q
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      -- Proof comment: a minimal prime is radical, so the vanishing ideal of its zero locus is
      -- the prime itself.
      calc
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (q.1.1 : Set S)) =
            q.1.1.radical :=
          PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical q.1.1
        _ = q.1.1 :=
          Ideal.IsPrime.radical (Ideal.minimalPrimes_isPrime q.1.2)
  refine Equiv.iSup_congr e ?_
  intro Z
  dsimp [e]
  calc
    topologicalKrullDim
        (PrimeSpectrum.zeroLocus
          (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S)) =
        topologicalKrullDim (closure (Z.1 : Set (PrimeSpectrum S))) := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    _ = topologicalKrullDim (Z.1 : Set (PrimeSpectrum S)) := by
      rw [(isClosed_of_mem_irreducibleComponents
        (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq]

/-- Helper for Chap10 Lemma 10 130 1: the component `V(q)` attached to a minimal prime has the
Krull dimension of the quotient ring `S ⧸ q`. -/
private theorem topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient
    (q : minimalPrimes S) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1 : Set S)) =
      ringKrullDim (S ⧸ q.1) := by
  -- Proof comment: `Spec (S ⧸ q)` is homeomorphic to the zero locus `V(q)`.
  have hhomeo :
      topologicalKrullDim (PrimeSpectrum (S ⧸ q.1)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1 : Set S)) := by
    simpa using
      IsHomeomorph.topologicalKrullDim_eq
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.1)
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.1).isHomeomorph
  rw [← hhomeo]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (S ⧸ q.1)

/-- Helper for Chap10 Lemma 10 130 1: the prime of `S ⧸ q` corresponding to `x` when `q` is a
minimal prime below `x.asIdeal`. -/
private noncomputable def quotientPrimeOver
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    PrimeSpectrum (S ⧸ q.1) :=
  (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1).symm ⟨x, hqx⟩

/-- Helper for Chap10 Lemma 10 130 1: the quotient prime over `x` contracts back to
`x.asIdeal`. -/
private theorem quotientPrimeOver_comap_asIdeal
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    Ideal.comap (Ideal.Quotient.mk q.1) (quotientPrimeOver x q hqx).asIdeal = x.asIdeal := by
  have hspec :
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1) (quotientPrimeOver x q hqx) =
        ⟨x, hqx⟩ := by
    exact (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1).apply_symm_apply ⟨x, hqx⟩
  exact congrArg (fun z : PrimeSpectrum.zeroLocus (R := S) (q.1 : Set S) => z.1.asIdeal) hspec

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 1: the residue field of the quotient prime over `x` has the
same transcendence degree over `k` as the residue field of `x`. -/
private theorem quotientPrimeOver_residueField_trdeg_toNat_eq
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    Cardinal.toNat (Algebra.trdeg k (quotientPrimeOver x q hqx).asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  have hcomap :
      x.asIdeal =
        Ideal.comap (Ideal.Quotient.mk q.1) (quotientPrimeOver x q hqx).asIdeal :=
    (quotientPrimeOver_comap_asIdeal (S := S) x q hqx).symm
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ x.asIdeal (quotientPrimeOver x q hqx).asIdeal
          (Ideal.Quotient.mkₐ k q.1) hcomap) := by
    -- Proof comment: surjectivity of the quotient map identifies the two residue fields.
    simpa using
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (f := (Ideal.Quotient.mk q.1 : S →+* S ⧸ q.1))
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        x.asIdeal (quotientPrimeOver x q hqx).asIdeal hcomap)
  let eResidue :
      x.asIdeal.ResidueField ≃ₐ[k] (quotientPrimeOver x q hqx).asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ x.asIdeal (quotientPrimeOver x q hqx).asIdeal
        (Ideal.Quotient.mkₐ k q.1) hcomap)
      hbij
  simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq (R := k) eResidue).symm

/-- Helper for Chap10 Lemma 10 130 1: the quotient-prime height is bounded by the height of the
original prime. -/
private theorem quotientPrimeOver_height_le
    (x : PrimeSpectrum S) (q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }) :
    (quotientPrimeOver x q.1 q.2).asIdeal.height ≤ x.asIdeal.height := by
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1.1
  let f : PrimeSpectrum (S ⧸ q.1.1) → PrimeSpectrum S := fun y => (e y).1
  have hf : StrictMono f := by
    intro a b hab
    simpa [f] using e.strictMono hab
  have hheight :=
    Order.height_le_height_apply_of_strictMono f hf (quotientPrimeOver x q.1 q.2)
  have himage : f (quotientPrimeOver x q.1 q.2) = x := by
    apply PrimeSpectrum.ext
    exact quotientPrimeOver_comap_asIdeal (S := S) x q.1 q.2
  rw [himage] at hheight
  simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight] using hheight

/-- Helper for Chap10 Lemma 10 130 1: each minimal-prime quotient has coheight equal to the
coheight of its corresponding minimal point in `Spec S`. -/
private theorem ringKrullDim_minimalPrimeQuotient_eq_coheight
    (q : minimalPrimes S) :
    ringKrullDim (S ⧸ q.1) =
      (Order.coheight (⟨q.1, Ideal.minimalPrimes_isPrime q.2⟩ : PrimeSpectrum S) :
        WithBot ℕ∞) := by
  letI : q.1.IsPrime := Ideal.minimalPrimes_isPrime q.2
  exact ringKrullDim_quotient_eq_coheight (S := S) q.1

/-- Helper for Chap10 Lemma 10 130 1: every chain ending at `x` lies in a quotient component of a
minimal prime below its head, giving the lower bound for the quotient-height supremum. -/
private theorem ltSeries_length_le_iSup_quotientPrimeOver_height
    (x : PrimeSpectrum S) (l : LTSeries (PrimeSpectrum S)) (hlast : l.last = x) :
    (l.length : ℕ∞) ≤
      ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (quotientPrimeOver x q.1 q.2).asIdeal.height := by
  obtain ⟨p, hp_min, hp_le_head⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := l.head.asIdeal) bot_le
  let qmin : minimalPrimes S := ⟨p, hp_min⟩
  have hq_le_x : qmin.1 ≤ x.asIdeal := by
    exact hp_le_head.trans (by simpa [hlast] using (l.head_le_last : l.head ≤ l.last))
  let qidx : { q : minimalPrimes S // q.1 ≤ x.asIdeal } := ⟨qmin, hq_le_x⟩
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus qmin.1
  have hq_le_i (i : Fin (l.length + 1)) : qmin.1 ≤ (l i).asIdeal := by
    exact hp_le_head.trans (show l.head.asIdeal ≤ (l i).asIdeal from l.head_le i)
  let lq : LTSeries (PrimeSpectrum (S ⧸ qmin.1)) :=
    LTSeries.mk l.length
      (fun i => e.symm ⟨l i, hq_le_i i⟩)
      (fun i j hij => by
        apply e.symm.strictMono
        exact show (⟨l i, hq_le_i i⟩ :
            PrimeSpectrum.zeroLocus (R := S) (qmin.1 : Set S)) <
            ⟨l j, hq_le_i j⟩ from l.strictMono hij)
  have hlast_lq : lq.last = e.symm ⟨x, hq_le_x⟩ := by
    apply e.injective
    simpa [lq, e, RelSeries.last] using hlast
  have hlen : (l.length : ℕ∞) ≤ (e.symm ⟨x, hq_le_x⟩).asIdeal.height := by
    have h := Order.length_le_height_last (p := lq)
    rw [hlast_lq] at h
    simpa only [Ideal.height_eq_primeHeight, Ideal.primeHeight] using h
  exact le_trans hlen (by
    simpa [quotientPrimeOver, qidx, qmin, e] using
      (le_iSup (fun q : { q : minimalPrimes S // q.1 ≤ x.asIdeal } =>
        (quotientPrimeOver x q.1 q.2).asIdeal.height) qidx))

/-- Helper for Chap10 Lemma 10 130 1: quotient primes over all minimal components below `x`
recover exactly the height of `x`. -/
private theorem iSup_quotientPrimeOver_height_eq_height
    (x : PrimeSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (quotientPrimeOver x q.1 q.2).asIdeal.height) = x.asIdeal.height := by
  refine le_antisymm ?_ ?_
  · exact iSup_le fun q => quotientPrimeOver_height_le (S := S) x q
  · rw [Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_eq_iSup_last_eq]
    exact iSup₂_le fun l hlast =>
      ltSeries_length_le_iSup_quotientPrimeOver_height (S := S) x l hlast

/-- Helper for Chap10 Lemma 10 130 1: the quotient prime over `x` has the same coheight as `x`
after identifying their residue fields through the quotient map. -/
private theorem quotientPrimeOver_coheight_eq
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    Order.coheight (quotientPrimeOver x q hqx) = Order.coheight x := by
  apply WithBot.coe_injective
  calc
    (Order.coheight (quotientPrimeOver x q hqx) : WithBot ℕ∞) =
        Cardinal.toNat
          (Algebra.trdeg k (quotientPrimeOver x q hqx).asIdeal.ResidueField) := by
      rw [← residueField_trdeg_toNat_eq_coheight (k := k) (S := S ⧸ q.1)
        (quotientPrimeOver x q hqx).asIdeal]
    _ = Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
      rw [quotientPrimeOver_residueField_trdeg_toNat_eq (k := k) (S := S) x q hqx]
    _ = (Order.coheight x : WithBot ℕ∞) :=
      residueField_trdeg_toNat_eq_coheight (k := k) (S := S) x.asIdeal

/-- Helper for Chap10 Lemma 10 130 1: the coheight of a minimal component through `x` splits as
quotient-prime height plus the coheight of `x`. -/
private theorem minimalPrimeComponent_coheight_eq_quotientPrimeOver_height_add_coheight
    (x : PrimeSpectrum S) (q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }) :
    Order.coheight (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) =
      (quotientPrimeOver x q.1 q.2).asIdeal.height + Order.coheight x := by
  apply WithBot.coe_injective
  letI : q.1.1.IsPrime := Ideal.minimalPrimes_isPrime q.1.2
  calc
    (Order.coheight
        (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
          WithBot ℕ∞) =
        ringKrullDim (S ⧸ q.1.1) :=
      (ringKrullDim_minimalPrimeQuotient_eq_coheight (S := S) q.1).symm
    _ = ((quotientPrimeOver x q.1 q.2).asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat
            (Algebra.trdeg k (quotientPrimeOver x q.1 q.2).asIdeal.ResidueField) :=
      finiteTypeDomain_ringKrullDim_eq_height_add_trdeg_residueField
        (k := k) (A := S ⧸ q.1.1) (quotientPrimeOver x q.1 q.2)
    _ = ((quotientPrimeOver x q.1 q.2).asIdeal.height : WithBot ℕ∞) +
          (Order.coheight (quotientPrimeOver x q.1 q.2) : WithBot ℕ∞) := by
      rw [residueField_trdeg_toNat_eq_coheight (k := k) (S := S ⧸ q.1.1)
        (quotientPrimeOver x q.1 q.2).asIdeal]
    _ = ((quotientPrimeOver x q.1 q.2).asIdeal.height : WithBot ℕ∞) +
          (Order.coheight x : WithBot ℕ∞) := by
      rw [quotientPrimeOver_coheight_eq (k := k) (S := S) x q.1 q.2]

/-- Helper for Chap10 Lemma 10 130 1: a constant can be pulled out of a nonempty supremum of
`ℕ∞` values after coercing to `WithBot ℕ∞`. -/
private theorem iSup_coe_enat_add_const {ι : Type*} [Nonempty ι]
    (f : ι → ℕ∞) (c : ℕ∞) :
    (⨆ i, ((f i + c : ℕ∞) : WithBot ℕ∞)) =
      (((⨆ i, f i) + c : ℕ∞) : WithBot ℕ∞) := by
  -- Proof comment: move the coercion outside once, then use the `ℕ∞` additive supremum rule.
  rw [← WithBot.coe_iSup (OrderTop.bddAbove (Set.range fun i => f i + c)), ENat.iSup_add]

/-- Helper for Chap10 Lemma 10 130 1: the remaining order-theoretic component identity after the
quotient and residue-field transports have been isolated. -/
private theorem iSup_coheight_minimalPrimesBelow_eq_height_add_coheight
    (x : PrimeSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (Order.coheight
          (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
            WithBot ℕ∞)) =
      (x.asIdeal.height : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) := by
  have hnonempty : Nonempty { q : minimalPrimes S // q.1 ≤ x.asIdeal } := by
    obtain ⟨p, hp_min, hp_le_x⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := x.asIdeal) bot_le
    exact ⟨⟨⟨p, hp_min⟩, hp_le_x⟩⟩
  let f : { q : minimalPrimes S // q.1 ≤ x.asIdeal } → ℕ∞ :=
    fun q => (quotientPrimeOver x q.1 q.2).asIdeal.height
  calc
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (Order.coheight
          (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
            WithBot ℕ∞)) =
        ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          ((f q + Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
      refine iSup_congr fun q => ?_
      rw [minimalPrimeComponent_coheight_eq_quotientPrimeOver_height_add_coheight
        (k := k) (S := S) x q]
    _ = (((⨆ q, f q) + Order.coheight x : ℕ∞) : WithBot ℕ∞) :=
      iSup_coe_enat_add_const f (Order.coheight x)
    _ = ((x.asIdeal.height + Order.coheight x : ℕ∞) : WithBot ℕ∞) := by
      rw [iSup_quotientPrimeOver_height_eq_height (S := S) x]
    _ = (x.asIdeal.height : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) := rfl

/-- Helper for Chap10 Lemma 10 130 1: the remaining algebraic component supremum after
reindexing by minimal primes below `x.asIdeal`. -/
private theorem
    iSup_ringKrullDim_minimalPrimeQuotientsBelow_eq_height_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
      (x.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  have hquotient_to_coheight :
      (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
        ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          (Order.coheight
            (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
              WithBot ℕ∞) := by
    exact iSup_congr fun q =>
      ringKrullDim_minimalPrimeQuotient_eq_coheight (S := S) q.1
  have hx_trdeg_to_coheight :
      (Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) : WithBot ℕ∞) =
        (Order.coheight x : WithBot ℕ∞) := by
    simpa using residueField_trdeg_toNat_eq_coheight (k := k) (S := S) x.asIdeal
  calc
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
        ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          (Order.coheight
            (⟨q.1.1, Ideal.minimalPrimes_isPrime q.1.2⟩ : PrimeSpectrum S) :
              WithBot ℕ∞) := hquotient_to_coheight
    _ = (x.asIdeal.height : WithBot ℕ∞) + (Order.coheight x : WithBot ℕ∞) :=
      iSup_coheight_minimalPrimesBelow_eq_height_add_coheight (k := k) (S := S) x
    _ = (x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
      rw [hx_trdeg_to_coheight]

/-- Helper for Chap10 Lemma 10 130 1: the supremum of dimensions of irreducible components
through `x` equals the height of `x.asIdeal` plus the transcendence degree of its residue field. -/
private theorem iSup_topologicalKrullDim_irreducibleComponents_through_eq_height_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
      (x.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  calc
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
        (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
          topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1.1 : Set S))) :=
      iSup_topologicalKrullDim_irreducibleComponents_through_eq_iSup_zeroLocus_minimalPrimesBelow
        (S := S) x
    _ = (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }, ringKrullDim (S ⧸ q.1.1)) := by
      exact iSup_congr fun q =>
        topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient (S := S) q.1
    _ = (x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) :=
      iSup_ringKrullDim_minimalPrimeQuotientsBelow_eq_height_add_trdeg_residueField
        (k := k) (S := S) x

/-- Helper for Chap10 Lemma 10 130 1: the local topological dimension at a prime is the height of
that prime plus the transcendence degree of its residue field. -/
private theorem topologicalKrullDimAt_eq_height_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      (x.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  -- Proof comment: rewrite local dimension as the supremum over irreducible components through
  -- `x`, then apply the isolated component/minimal-prime formula.
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := k) (S := S) x]
  exact iSup_topologicalKrullDim_irreducibleComponents_through_eq_height_add_trdeg_residueField
    (k := k) (S := S) x

-- Route correction: removing the direct `Lemma_10_116_3` import isolates the only broken branch
-- to the local-dimension formula itself; the remaining proof skeleton stays on the stable
-- quasi-finite/flatness route in this file.
/-- Helper for Chap10 Lemma 10 130 1: local topological Krull dimension equals the Krull
dimension of the localized ring plus the residue-field transcendence degree. -/
private theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ringKrullDim (Localization.AtPrime x.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
  -- Proof comment: first express the local dimension by the height/trdeg formula, then replace
  -- the height with the Krull dimension of the canonical localization at `x.asIdeal`.
  calc
    topologicalKrullDimAt x =
        (x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) :=
      topologicalKrullDimAt_eq_height_add_trdeg_residueField (k := k) (S := S) x
    _ = ringKrullDim (Localization.AtPrime x.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
      rw [← IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal
        (Localization.AtPrime x.asIdeal)]

/-- Helper for Chap10 Lemma 10 130 1: quasi-finiteness of the polynomial presentation forces the
residue-field transcendence degree at `q` to agree with that at the contracted prime of
`k[y₁, …, y_d]`. -/
private theorem residueFieldTrdeg_toNat_eq_under_of_quasiFinitePolynomial
    (π : P →ₐ[k] S) (hπ : π.QuasiFinite) (q : PrimeSpectrum S) :
    let _ : Algebra P S := π.toAlgebra
    let p : Ideal P := q.asIdeal.under P
    Cardinal.toNat (Algebra.trdeg k q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k p.ResidueField) := by
  dsimp
  letI : Algebra P S := π.toAlgebra
  letI : Algebra.QuasiFinite P S := RingHom.QuasiFinite.toAlgebra hπ
  let p : Ideal P := q.asIdeal.under P
  have htrdeg :
      Algebra.trdeg k q.asIdeal.ResidueField = Algebra.trdeg k p.ResidueField := by
    letI : Module.Finite p.ResidueField q.asIdeal.ResidueField := inferInstance
    letI : Algebra.IsAlgebraic p.ResidueField q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_finite (R := p.ResidueField) (A := q.asIdeal.ResidueField)
    have htrdeg_add :=
      trdeg_add_eq (R := k) (S := p.ResidueField) (A := q.asIdeal.ResidueField)
    have htrdeg_zero :
        Algebra.trdeg p.ResidueField q.asIdeal.ResidueField = 0 :=
      trdeg_eq_zero (R := p.ResidueField) (A := q.asIdeal.ResidueField)
    -- Proof comment: quasi-finiteness makes the residue-field extension algebraic, so the tower
    -- formula collapses to equality of the base-field transcendence degrees.
    simpa [p, htrdeg_zero] using htrdeg_add
  exact congrArg Cardinal.toNat htrdeg

/-- Helper for Chap10 Lemma 10 130 1: the fiber local ring of a quasi-finite polynomial
presentation has Krull dimension `0`. -/
private theorem ringKrullDim_fiberLocalRingAt_eq_zero_of_quasiFinitePolynomial
    (π : P →ₐ[k] S) (hπ : π.QuasiFinite) (q : PrimeSpectrum S) :
    let _ : Algebra P S := π.toAlgebra
    ringKrullDim (fiberLocalRingAt P S q) = 0 := by
  dsimp
  letI : Algebra P S := π.toAlgebra
  letI : Algebra.QuasiFinite P S := RingHom.QuasiFinite.toAlgebra hπ
  let p : PrimeSpectrum P := PrimeSpectrum.comap (algebraMap P S) q
  have hfiber :
      Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    refine
      ((quasiFiniteAt_primesOver_tfae_fiberFinite (R := P) (S := S) p).out 0 1 rfl rfl) ?_
    intro q' hq'
    -- Proof comment: the global quasi-finite presentation is quasi-finite at every prime above
    -- the chosen contracted prime.
    simpa using (inferInstance : Algebra.QuasiFiniteAt P q'.asIdeal)
  letI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := hfiber
  have hArt : IsArtinianRing (fiberLocalRingAt P S q) := by
    -- Proof comment: the local fiber ring is a localization of a finite algebra over a field.
    dsimp [fiberLocalRingAt]
    exact IsArtinianRing.localization_artinian
      (fiberPrimeAt P S q).asIdeal.primeCompl
      (Localization.AtPrime (fiberPrimeAt P S q).asIdeal)
  letI : IsArtinianRing (fiberLocalRingAt P S q) := hArt
  have hNoeth : IsNoetherianRing (fiberLocalRingAt P S q) := inferInstance
  letI : IsNoetherianRing (fiberLocalRingAt P S q) := hNoeth
  have hle : Ring.KrullDimLE 0 (fiberLocalRingAt P S q) :=
    (isArtinianRing_iff_krullDimLE_zero (R := fiberLocalRingAt P S q)).mp hArt
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle

/-- Helper for Chap10 Lemma 10 130 1: on the quasi-finite polynomial presentation, membership in
the `d`-th dimension stratum is equivalent to equality of the local Krull dimensions of `S_q` and
of the localized polynomial ring at the contracted prime. -/
private theorem
    mem_dimensionStratum_iff_ringKrullDim_localizationAtPrime_eq_under_ofQuasiFinitePolynomial
    (π : P →ₐ[k] S) (hπ : π.QuasiFinite) (q : PrimeSpectrum S) :
    let _ : Algebra P S := π.toAlgebra
    let p : PrimeSpectrum P := PrimeSpectrum.comap (algebraMap P S) q
    q ∈ PrimeSpectrum.dimensionStratum S d ↔
      ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
  dsimp
  letI : Algebra P S := π.toAlgebra
  let p : PrimeSpectrum P := PrimeSpectrum.comap (algebraMap P S) q
  have hqdim :=
    topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
      (k := k) (S := S) q
  have hpdim :=
    topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
      (k := k) (S := P) p
  have htrdeg :
      Cardinal.toNat (Algebra.trdeg k q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
    -- Proof comment: compare the residue fields at `q` and at the contracted prime `p`.
    simpa [p, PrimeSpectrum.comap_asIdeal, Ideal.under_def] using
      residueFieldTrdeg_toNat_eq_under_of_quasiFinitePolynomial
        (π := π) (hπ := hπ) q
  have hpcalc :
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) = d := by
    -- Proof comment: every point of affine `d`-space has local topological dimension `d`.
    calc
      ringKrullDim (Localization.AtPrime p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
        topologicalKrullDimAt p := by
          simpa using hpdim.symm
      _ = d := by
          simpa using topologicalKrullDimAt_mvPolynomial_eq_nat (F := k) d p
  constructor
  · intro hstratum
    have hqcalc :
        ringKrullDim (Localization.AtPrime q.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) = d := by
      -- Proof comment: rewrite the target stratum condition and normalize the residue-field term.
      rw [← htrdeg]
      simpa [PrimeSpectrum.mem_dimensionStratum, hqdim] using hstratum
    obtain ⟨nq, hnq⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring
      (T := Localization.AtPrime q.asIdeal)
    obtain ⟨np, hnp⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring
      (T := Localization.AtPrime p.asIdeal)
    rw [hnq, hnp] at hqcalc hpcalc
    have hqnat :
        nq + Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) = d := by
      exact_mod_cast hqcalc
    have hpnat :
        np + Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) = d := by
      exact_mod_cast hpcalc
    have hdim : nq = np := by
      omega
    simpa [hnq, hnp, hdim]
  · intro hdim
    -- Proof comment: substitute the local-dimension equality into the polynomial normal form.
    rw [PrimeSpectrum.mem_dimensionStratum, hqdim, htrdeg]
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
        ringKrullDim (Localization.AtPrime p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
            rw [hdim]
      _ = d := hpcalc

/-- Helper for Chap10 Lemma 10 130 1: the quotient of `S_q` by the image of the maximal ideal of
`P_p` has Krull dimension `0`. -/
private theorem
    ringKrullDim_quotient_localizationAtPrime_map_maximalIdeal_eq_zero_of_quasiFinitePolynomial
    (π : P →ₐ[k] S) (hπ : π.QuasiFinite) (q : PrimeSpectrum S) :
    let _ : Algebra P S := π.toAlgebra
    let p : Ideal P := q.asIdeal.under P
    ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal))
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))) = 0 := by
  dsimp
  letI : Algebra P S := π.toAlgebra
  let p : Ideal P := q.asIdeal.under P
  letI : p.IsPrime := Ideal.comap_isPrime (algebraMap P S) q.asIdeal
  let ρ : Localization.AtPrime p →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p q.asIdeal (algebraMap P S) (by
      simpa [p, Ideal.under_def])
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := ρ.toAlgebra
  have hmap :
      Ideal.map
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
        Ideal.map (algebraMap P (Localization.AtPrime q.asIdeal)) p := by
    letI : q.asIdeal.LiesOver p := by
      simpa [p] using (Ideal.over_under q.asIdeal)
    -- Proof comment: rewrite the localized closed-fiber ideal as the extension of the contracted
    -- prime from the polynomial source.
    simpa [p] using
      localized_base_prime_eq_map_maximalIdeal (R := P) (S := S) p q.asIdeal ‹_›
  calc
    ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime q.asIdeal))
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))) =
      ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸ Ideal.map (algebraMap P
          (Localization.AtPrime q.asIdeal)) p) := by
        rw [hmap]
    _ = ringKrullDim (fiberLocalRingAt P S q) := by
      -- Proof comment: the quotient presentation from Lemma 10.112.6 is the canonical local
      -- fiber ring at `q`.
      simpa [p, Ideal.under_def] using
        ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
          (R := P) (S := S) q
    _ = 0 := by
      -- Proof comment: quasi-finiteness kills the local fiber dimension.
      simpa using
        ringKrullDim_fiberLocalRingAt_eq_zero_of_quasiFinitePolynomial
          (π := π) (hπ := hπ) q

/-- Helper for Chap10 Lemma 10 130 1: the tuple-valued parameter ideal agrees with the list-based
owner `Ideal.ofList` on the same generators. -/
private lemma parameterIdeal_eq_idealOfList_ofFn
    {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (x : Fin n → maximalIdeal R) :
    Ideal.ofList (List.ofFn fun i : Fin n ↦ ((x i : maximalIdeal R) : R)) =
      parameterIdeal x := by
  -- Proof comment: both ideal owners are just the span of the same finite family of generators.
  rw [Ideal.ofList, parameterIdeal_eq_span]
  congr 1
  ext r
  constructor
  · intro hr
    rcases List.mem_ofFn.mp hr with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Helper for Chap10 Lemma 10 130 1: once `S_q` is Cohen-Macaulay and has the same local
dimension as the contracted polynomial localization, the localized presentation is flat. -/
private theorem flat_localizationAtPrime_under_of_cohenMacaulaySelf_of_quasiFinitePolynomial
    (π : P →ₐ[k] S) (hπ : π.QuasiFinite) (q : PrimeSpectrum S) :
    let _ : Algebra P S := π.toAlgebra
    let p : Ideal P := q.asIdeal.under P
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) →
      ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime p) →
      Module.Flat (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := by
  dsimp
  intro hCM hdim
  letI : Algebra P S := π.toAlgebra
  let p : Ideal P := q.asIdeal.under P
  letI : p.IsPrime := Ideal.comap_isPrime (algebraMap P S) q.asIdeal
  let ρ : Localization.AtPrime p →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p q.asIdeal (algebraMap P S) (by
      simpa [p, Ideal.under_def])
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := ρ.toAlgebra
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  have hclosedFiber :
      ringKrullDim (Ideal.Fiber (IsLocalRing.maximalIdeal Rp) Sq) = 0 := by
    -- Proof comment: the closed fiber is the quotient by the mapped source maximal ideal, and the
    -- quasi-finite local fiber computation already shows that quotient has dimension `0`.
    calc
      ringKrullDim (Ideal.Fiber (IsLocalRing.maximalIdeal Rp) Sq) =
          ringKrullDim (Sq ⧸
            Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) := by
              symm
              exact ringKrullDim_eq_of_ringEquiv
                (closedFiber_quotient_equiv (R := Rp) (S := Sq)).toRingEquiv
      _ = 0 := by
          simpa [Rp, Sq, p] using
            ringKrullDim_quotient_localizationAtPrime_map_maximalIdeal_eq_zero_of_quasiFinitePolynomial
              (π := π) (hπ := hπ) q
  have hflat :
      (algebraMap Rp Sq).Flat := by
    -- Proof comment: the localized source is regular local, the target is Cohen-Macaulay, and
    -- the closed fiber has dimension `0`, so the dimension-formula flatness theorem applies.
    refine algebraMap_flat_of_isRegularLocalRing_of_cohenMacaulay_of_dimension_formula
      (R := Rp) (S := Sq) hCM ?_
    calc
      ringKrullDim Sq = ringKrullDim Rp := hdim
      _ = ringKrullDim Rp + 0 := by simp
      _ = ringKrullDim Rp + ringKrullDim (Ideal.Fiber (IsLocalRing.maximalIdeal Rp) Sq) := by
          rw [hclosedFiber]
  exact (RingHom.flat_algebraMap_iff).mp hflat

/-- Chap10 Lemma 10 130 1: for a finite type `k`-algebra `S` over a field `k` and a quasi-finite map
`π : k[y₁, …, y_d] → S`, the primes `q : Spec(S)` for which the local ring `S_q` is flat over
this chosen polynomial presentation are exactly the primes for which `S_q` is Cohen-Macaulay and
the local topological dimension stratum of `Spec(S)` at `q` is `d`. -/
@[stacks 00RE]
theorem flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial
    (π : MvPolynomial (Fin d) k →ₐ[k] S) (hπ : π.QuasiFinite) :
    let _ : Algebra (MvPolynomial (Fin d) k) S := π.toAlgebra
    Module.flatOverBaseLocus (MvPolynomial (Fin d) k) S S =
      { q : PrimeSpectrum S |
          Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal) } ∩
        PrimeSpectrum.dimensionStratum S d := by
  dsimp
  letI : Algebra P S := π.toAlgebra
  ext q
  constructor
  · intro hflat
    change
      Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal) ∧
        q ∈ PrimeSpectrum.dimensionStratum S d
    let p : Ideal P := q.asIdeal.under P
    letI : p.IsPrime := Ideal.comap_isPrime (algebraMap P S) q.asIdeal
    let ρ : Localization.AtPrime p →+* Localization.AtPrime q.asIdeal :=
      Localization.localRingHom p q.asIdeal (algebraMap P S) (by
        simpa [p, Ideal.under_def])
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := ρ.toAlgebra
    have hflatLocal :
        Module.Flat (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
      (mem_flatOverBaseLocus_iff_flat_localizationAtPrime_under (π := π) q).mp hflat
    letI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) := hflatLocal
    letI : Algebra.QuasiFinite P S := RingHom.QuasiFinite.toAlgebra hπ
    have hle :
        ringKrullDim (Localization.AtPrime q.asIdeal) ≤
          ringKrullDim (Localization.AtPrime p) := by
      -- Proof comment: quasi-finiteness gives the standard upper bound on the localized target
      -- dimension.
      simpa [p] using
        ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt
          (R := P) (S := S) q.asIdeal
    have hCMsource :
        Module.CohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
      inferInstance
    have hCMtarget :
        Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal) :=
      cohenMacaulayRing_of_flat_localHom_of_ringKrullDim_le
        (R := Localization.AtPrime p) (S := Localization.AtPrime q.asIdeal)
        hCMsource hle
    have hdimEq :
        ringKrullDim (Localization.AtPrime q.asIdeal) =
          ringKrullDim (Localization.AtPrime p) := by
      -- Proof comment: the same flat local argument upgrades the inequality to equality.
      simpa using
        (ringKrullDim_eq_of_flat_localHom_of_ringKrullDim_le_of_cohenMacaulayRing
          (R := Localization.AtPrime p) (S := Localization.AtPrime q.asIdeal)
          hCMsource hle).symm
    refine ⟨hCMtarget, ?_⟩
    exact
      (mem_dimensionStratum_iff_ringKrullDim_localizationAtPrime_eq_under_ofQuasiFinitePolynomial
        (π := π) (hπ := hπ) q).mpr hdimEq
  · intro hq
    change
      Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal) ∧
        q ∈ PrimeSpectrum.dimensionStratum S d at hq
    rcases hq with ⟨hCM, hstratum⟩
    have hdimEq :
        ringKrullDim (Localization.AtPrime q.asIdeal) =
          ringKrullDim
            (Localization.AtPrime (PrimeSpectrum.comap (algebraMap P S) q).asIdeal) :=
      (mem_dimensionStratum_iff_ringKrullDim_localizationAtPrime_eq_under_ofQuasiFinitePolynomial
        (π := π) (hπ := hπ) q).mp hstratum
    have hflatLocal :
        Module.Flat
          (Localization.AtPrime (PrimeSpectrum.comap (algebraMap P S) q).asIdeal)
          (Localization.AtPrime q.asIdeal) :=
      flat_localizationAtPrime_under_of_cohenMacaulaySelf_of_quasiFinitePolynomial
        (π := π) (hπ := hπ) q hCM hdimEq
    exact
      (mem_flatOverBaseLocus_iff_flat_localizationAtPrime_under
        (π := π) q).mpr hflatLocal

end
