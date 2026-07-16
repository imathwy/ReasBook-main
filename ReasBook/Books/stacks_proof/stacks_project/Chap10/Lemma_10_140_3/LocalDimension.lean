import stacks_proof.stacks_project.Chap10.Definition_10_103_1
import stacks_proof.stacks_project.Chap10.Definition_10_125_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_6
import stacks_proof.stacks_project.Chap10.Lemma_10_112_9
import stacks_proof.stacks_project.Chap10.Lemma_10_113_1
import stacks_proof.stacks_project.Chap10.Lemma_10_114_7
import stacks_proof.stacks_project.Chap10.Lemma_10_122_4
import stacks_proof.stacks_project.Chap10.Lemma_10_125_4
import stacks_proof.stacks_project.Chap10.Lemma_10_128_1

universe u v

open TopologicalSpace

namespace Algebra

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-- Helper for Chap10 Lemma 10 140 3: equal contracted base primes give the same residue-field
transcendence-degree term for a fixed target prime. -/
private lemma residueFieldTrdeg_toNat_eq_of_base_eq
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {p p' : Ideal R} [p.IsPrime] [p'.IsPrime]
    {P : Ideal A} [P.IsPrime] [P.LiesOver p] [P.LiesOver p'] (hp : p = p') :
    Cardinal.toNat (Algebra.trdeg p.ResidueField P.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p'.ResidueField P.ResidueField) := by
  -- Proof comment: substituting the base prime avoids rewriting through residue-field
  -- implementations.
  cases hp
  rfl

/-- Helper for Chap10 Lemma 10 140 3: every prime of a domain algebra over a field lies over the
zero prime of the base field. -/
private lemma fieldBase_liesOver_bot
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) :
    p.asIdeal.LiesOver (⊥ : Ideal k) := by
  -- Proof comment: the contraction of a prime ideal to a field is proper, hence it must be `⊥`.
  refine ⟨?_⟩
  have hproper : p.asIdeal.under k ≠ ⊤ := by
    intro htop
    have hone_under : (1 : k) ∈ p.asIdeal.under k := by
      rw [htop]
      trivial
    have hone : (1 : A) ∈ p.asIdeal := by
      simpa [Ideal.under_def] using hone_under
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one p.asIdeal).mpr hone)
  rcases IsSimpleOrder.eq_bot_or_eq_top (p.asIdeal.under k) with hbot | htop
  · exact hbot.symm
  · exact (hproper htop).elim

/-- Helper for Chap10 Lemma 10 140 3: replacing a field by the residue field of its zero prime
does not change the natural-number transcendence degree of a compatible target field. -/
private theorem fieldBotResidueField_trdeg_toNat_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra ((⊥ : Ideal K).ResidueField) L]
    [IsScalarTower K ((⊥ : Ideal K).ResidueField) L] :
    Cardinal.toNat (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L) =
      Cardinal.toNat (Algebra.trdeg K L) := by
  -- Proof comment: identify the zero-prime residue field with the fraction field of `K`, then
  -- use tower additivity with a zero algebraic base term.
  letI : IsFractionRing K ((⊥ : Ideal K).ResidueField) := by
    let e : K ≃ₐ[K] K ⧸ (⊥ : Ideal K) := (AlgEquiv.quotientBot K K).symm
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap K ((⊥ : Ideal K).ResidueField) x =
      algebraMap (K ⧸ (⊥ : Ideal K)) ((⊥ : Ideal K).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    rfl
  have hbase_alg : Algebra.IsAlgebraic K ((⊥ : Ideal K).ResidueField) := by
    let e : (⊥ : Ideal K).ResidueField ≃ₐ[K] K :=
      (FractionRing.algEquiv K ((⊥ : Ideal K).ResidueField)).symm.trans
        (FractionRing.algEquiv K K)
    exact Algebra.IsAlgebraic.of_injective e.toAlgHom e.injective
  have hbase_zero : Algebra.trdeg K ((⊥ : Ideal K).ResidueField) = 0 := by
    exact trdeg_eq_zero (R := K) (A := (⊥ : Ideal K).ResidueField)
  have hsum :=
    lift_trdeg_add_eq (R := K) (S := (⊥ : Ideal K).ResidueField) (A := L)
  have hlift_eq :
      Cardinal.lift.{u, v} (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L) =
        Cardinal.lift.{u, v} (Algebra.trdeg K L) := by
    -- Proof comment: the residue-field base step is algebraic, so only the target trdeg
    -- survives.
    simpa [hbase_zero] using hsum
  rw [← Cardinal.toNat_lift.{u, v} (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L),
    ← Cardinal.toNat_lift.{u, v} (Algebra.trdeg K L), hlift_eq]

/-- Helper for Chap10 Lemma 10 140 3: the zero prime of a field has zero prime height in natural
number form. -/
private theorem fieldBot_primeHeight_toNat_eq_zero {k : Type u} [Field k] :
    ENat.toNat (Ideal.primeHeight (⊥ : Ideal k)) = 0 := by
  -- Proof comment: the zero ideal is the unique minimal prime of a field.
  have hheight : Ideal.primeHeight (⊥ : Ideal k) = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  simpa [hheight]

/-- Helper for Chap10 Lemma 10 140 3: the contraction of a prime in a domain algebra over a
field contributes zero prime height on the base side. -/
private theorem fieldBase_primeHeight_under_toNat_eq_zero
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight (p.asIdeal.under k)) = 0 := by
  -- Proof comment: contract to the zero ideal of the base field and evaluate the concrete
  -- zero-height term there.
  have hunder : p.asIdeal.under k = (⊥ : Ideal k) := by
    simpa using (fieldBase_liesOver_bot (k := k) (A := A) p).over.symm
  simpa [hunder] using fieldBot_primeHeight_toNat_eq_zero (k := k)

/-- Helper for Chap10 Lemma 10 140 3: after contracting a prime of a domain algebra to the base
field, the residue-field transcendence term is the ordinary base-field transcendence term. -/
private theorem fieldBase_residueFieldTrdeg_under_toNat_eq
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) :
    Cardinal.toNat
        (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  letI : p.asIdeal.LiesOver (p.asIdeal.under k) := ⟨rfl⟩
  letI : p.asIdeal.LiesOver (⊥ : Ideal k) := fieldBase_liesOver_bot (k := k) (A := A) p
  have hunder : p.asIdeal.under k = (⊥ : Ideal k) := by
    simpa using (fieldBase_liesOver_bot (k := k) (A := A) p).over.symm
  have hbase :
      Cardinal.toNat
          (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg (⊥ : Ideal k).ResidueField p.asIdeal.ResidueField) :=
    residueFieldTrdeg_toNat_eq_of_base_eq
      (R := k) (A := A) (p := p.asIdeal.under k) (p' := (⊥ : Ideal k))
      (P := p.asIdeal) hunder
  -- Proof comment: the zero-prime residue field of the base field is just another algebraic
  -- avatar of the base field itself.
  exact hbase.trans
    (fieldBotResidueField_trdeg_toNat_eq (K := k) (L := p.asIdeal.ResidueField))

/- The next helper block isolates the quotient/transcendence/coheight part of the old
`10.116.3` dependency. This support file copies only the field-base ingredients it actually uses,
so the remaining route stays dependency-closed without the broken `DimensionEquality` split. -/
/-- Helper for Chap10 Lemma 10 140 3: a finite-type domain over a field has Krull dimension equal
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
    have hzero : Algebra.trdeg (MvPolynomial (Fin n) k) A = 0 := by
      exact trdeg_eq_zero (R := MvPolynomial (Fin n) k) (A := A)
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

/-- Helper for Chap10 Lemma 10 140 3: for a finite-type domain over a field, replacing both
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

/-- Helper for Chap10 Lemma 10 140 3: the field-base height-plus-residue-field term is bounded
above by the base-field transcendence degree. -/
private theorem fieldBase_primeHeight_add_residueFieldTrdeg_toNat_le_trdeg
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) ≤
      Cardinal.toNat (Algebra.trdeg k A) := by
  have hgeneric :
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) =
        ENat.toNat (Ideal.primeHeight (p.asIdeal.under k)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
    -- Proof comment: specialize the universally catenary equality owner to the field base case.
    have hinj : Function.Injective (algebraMap k A) :=
      FaithfulSMul.algebraMap_injective k A
    letI : UniversallyCatenaryRing.{u, v} k := field_universallyCatenaryRing (k := k)
    exact
      primeHeight_add_residueFieldTrdeg_eq_primeHeight_under_add_trdeg_of_universallyCatenary
        (R := k) (S := A) hinj p
  have hheight := fieldBase_primeHeight_under_toNat_eq_zero (k := k) (A := A) p
  have hresidue := fieldBase_residueFieldTrdeg_under_toNat_eq (k := k) (A := A) p
  have hdim :
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
    calc
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
        ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) := by
          rw [hresidue]
      _ = ENat.toNat (Ideal.primeHeight (p.asIdeal.under k)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := hgeneric
      _ = Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
          rw [hheight]
          simp
  have hfrac := fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain (k := k) (A := A)
  exact le_of_eq (by simpa [hfrac] using hdim)

/-- Helper for Chap10 Lemma 10 140 3: the base-field transcendence degree is bounded above by the
field-base height-plus-residue-field term. -/
private theorem fieldBase_trdeg_toNat_le_primeHeight_add_residueFieldTrdeg_toNat
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    Cardinal.toNat (Algebra.trdeg k A) ≤
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  have hgeneric :
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) =
        ENat.toNat (Ideal.primeHeight (p.asIdeal.under k)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
    have hinj : Function.Injective (algebraMap k A) :=
      FaithfulSMul.algebraMap_injective k A
    letI : UniversallyCatenaryRing.{u, v} k := field_universallyCatenaryRing (k := k)
    exact
      primeHeight_add_residueFieldTrdeg_eq_primeHeight_under_add_trdeg_of_universallyCatenary
        (R := k) (S := A) hinj p
  have hheight := fieldBase_primeHeight_under_toNat_eq_zero (k := k) (A := A) p
  have hresidue := fieldBase_residueFieldTrdeg_under_toNat_eq (k := k) (A := A) p
  have hdim :
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
    calc
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
        ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) := by
          rw [hresidue]
      _ = ENat.toNat (Ideal.primeHeight (p.asIdeal.under k)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := hgeneric
      _ = Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
          rw [hheight]
          simp
  have hfrac := fractionRing_trdeg_toNat_eq_trdeg_of_finiteTypeDomain (k := k) (A := A)
  exact le_of_eq (by simpa [hfrac] using hdim.symm)

/-- Helper for Chap10 Lemma 10 140 3: the field-base dimension formula in natural-number form for
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

/-- Helper for Chap10 Lemma 10 140 3: convert the natural-number prime-height formula to the
`WithBot ℕ∞` height formula used by `ringKrullDim`. -/
private theorem primeHeight_toNat_add_coe_eq_height_add
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] (n : ℕ) :
    (((ENat.toNat (Ideal.primeHeight p) + n : ℕ) : ℕ∞) : WithBot ℕ∞) =
      (p.height : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
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

/-- Helper for Chap10 Lemma 10 140 3: a finite-type domain over a field satisfies the
height-plus-residue-field transcendence dimension formula at every prime. -/
private theorem finiteTypeDomain_ringKrullDim_eq_height_add_trdeg_residueField
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    ringKrullDim A =
      (p.asIdeal.height : WithBot ℕ∞) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
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

/-- Helper for Chap10 Lemma 10 140 3: the residue field of a prime and the corresponding prime
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

/-- Helper for Chap10 Lemma 10 140 3: a prime quotient has Krull dimension equal to the
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

/-- Helper for Chap10 Lemma 10 140 3: the Krull dimension of a prime quotient is the coheight of
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

/-- Helper for Chap10 Lemma 10 140 3: the residue-field transcendence degree of a prime equals
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

-- Route correction: this support file isolates the single local-dimension theorem needed by
-- `Lemma_10_140_3`, so the main item no longer depends on the broken `Lemma_10_116_3` import
-- chain through the missing `Lemma_10_103_13.olean`.
/-- Helper for Chap10 Lemma 10 140 3: components through a point can be reindexed by minimal
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

/-- Helper for Chap10 Lemma 10 140 3: the component `V(q)` attached to a minimal prime has the
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

/-- Helper for Chap10 Lemma 10 140 3: the prime of `S ⧸ q` corresponding to `x` when `q` is a
minimal prime below `x.asIdeal`. -/
private noncomputable def quotientPrimeOver
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    PrimeSpectrum (S ⧸ q.1) :=
  (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1).symm ⟨x, hqx⟩

/-- Helper for Chap10 Lemma 10 140 3: the quotient prime over `x` contracts back to
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
/-- Helper for Chap10 Lemma 10 140 3: the residue field of the quotient prime over `x` has the
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

/-- Helper for Chap10 Lemma 10 140 3: the quotient-prime height is bounded by the height of the
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

/-- Helper for Chap10 Lemma 10 140 3: each minimal-prime quotient has coheight equal to the
coheight of its corresponding minimal point in `Spec S`. -/
private theorem ringKrullDim_minimalPrimeQuotient_eq_coheight
    (q : minimalPrimes S) :
    ringKrullDim (S ⧸ q.1) =
      (Order.coheight (⟨q.1, Ideal.minimalPrimes_isPrime q.2⟩ : PrimeSpectrum S) :
        WithBot ℕ∞) := by
  letI : q.1.IsPrime := Ideal.minimalPrimes_isPrime q.2
  exact ringKrullDim_quotient_eq_coheight (S := S) q.1

/-- Helper for Chap10 Lemma 10 140 3: every chain ending at `x` lies in a quotient component of a
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

/-- Helper for Chap10 Lemma 10 140 3: quotient primes over all minimal components below `x`
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

/-- Helper for Chap10 Lemma 10 140 3: the quotient prime over `x` has the same coheight as `x`
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

/-- Helper for Chap10 Lemma 10 140 3: the coheight of a minimal component through `x` splits as
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

/-- Helper for Chap10 Lemma 10 140 3: a constant can be pulled out of a nonempty supremum of
`ℕ∞` values after coercing to `WithBot ℕ∞`. -/
private theorem iSup_coe_enat_add_const {ι : Type*} [Nonempty ι]
    (f : ι → ℕ∞) (c : ℕ∞) :
    (⨆ i, ((f i + c : ℕ∞) : WithBot ℕ∞)) =
      (((⨆ i, f i) + c : ℕ∞) : WithBot ℕ∞) := by
  -- Proof comment: move the coercion outside once, then use the `ℕ∞` additive supremum rule.
  rw [← WithBot.coe_iSup (OrderTop.bddAbove (Set.range fun i => f i + c)), ENat.iSup_add]

/-- Helper for Chap10 Lemma 10 140 3: the remaining order-theoretic component identity after the
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

/-- Helper for Chap10 Lemma 10 140 3: the remaining algebraic component supremum after
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
    -- Proof comment: every minimal-prime quotient dimension is already the coheight of its
    -- corresponding minimal point.
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

/-- Helper for Chap10 Lemma 10 140 3: the supremum of dimensions of irreducible components
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
      -- Proof comment: each component zero locus is the spectrum of its minimal-prime quotient.
      exact iSup_congr fun q =>
        topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient (S := S) q.1
    _ = (x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) :=
      iSup_ringKrullDim_minimalPrimeQuotientsBelow_eq_height_add_trdeg_residueField
        (k := k) (S := S) x

/-- Helper for Chap10 Lemma 10 140 3: the local topological dimension at a prime is the height of
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

/-- Helper for Chap10 Lemma 10 140 3: the missing local-dimension formula needed in
`Lemma_10_140_3`, proved directly by the minimal-prime component route instead of importing the
broken `Lemma_10_116_3` chain. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField_viaMinimalPrimes
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

end

end Algebra
