import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_105_3
import stacks_proof.stacks_project.Chap10.Lemma_10_25_1
import stacks_proof.stacks_project.Chap10.Lemma_10_105_5
import stacks_proof.stacks_project.Chap10.Lemma_10_105_9
import stacks_proof.stacks_project.Chap10.Lemma_10_113_1.ExactDrop
import stacks_proof.stacks_project.Chap10.Lemma_10_113_1

-- Acyclic support for the equality part of Lemma 10.113.1.

noncomputable section

universe u v w

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S]

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: the natural-number transcendence degree
of the fraction-field extension induced by an injective domain map. -/
private noncomputable abbrev fractionRingTrdeg
    (hinj : Function.Injective (algebraMap R S)) : ℕ :=
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  Cardinal.toNat (trdeg (FractionRing R) (FractionRing S))

end

end Algebra

/-- Helper for Chap10 Lemma 10 116 3: two successive height/residue-field equalities combine by
canceling the intermediate height term. -/
private lemma towerStep_primeHeightResidueFieldTrdeg_eq
    {heightR heightT heightS genericRT genericTS residueRT residueTS : ℕ}
    (hRT : heightT + residueRT = heightR + genericRT)
    (hTS : heightS + residueTS = heightT + genericTS) :
    heightS + (residueRT + residueTS) = heightR + (genericRT + genericTS) := by
  -- This is the arithmetic spine of the finite-adjoin equality induction.
  omega

/-- Helper for Chap10 Lemma 10 116 3: an essentially finite type field extension has finite
transcendence degree. -/
private lemma trdeg_lt_aleph0_of_essFiniteType_field
    {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L] :
    Algebra.trdeg K L < Cardinal.aleph0 := by
  -- Choose finite field generators and bound the transcendence degree by that finite set.
  obtain ⟨t, ht⟩ := IntermediateField.fg_top K L
  have ht_alg : Algebra.IsAlgebraic (Algebra.adjoin K (t : Set L)) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, ht,
      Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  exact
    lt_of_le_of_lt
      (Algebra.IsAlgebraic.trdeg_le_cardinalMk K (t : Set L))
      (by simpa using t.finite_toSet.lt_aleph0)

/-- Helper for Chap10 Lemma 10 116 3: contracting a prime through an intermediate algebra stage
and then to the base is the same as direct contraction to the base. -/
private lemma comap_under_eq_under_in_tower
    {R : Type u} {T : Type v} {U : Type w}
    [CommRing R] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    (q : PrimeSpectrum U) :
    let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
    qT.asIdeal.under R = q.asIdeal.under R := by
  let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
  ext r
  -- Both contractions test membership after mapping the same base element into `U`.
  change algebraMap T U (algebraMap R T r) ∈ q.asIdeal ↔ algebraMap R U r ∈ q.asIdeal
  rw [IsScalarTower.algebraMap_apply R T U r]

/-- Helper for Chap10 Lemma 10 116 3: if one element generates the algebra, the corresponding
polynomial evaluation map is surjective. -/
private lemma singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) :
    Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] B) := by
  -- The one-generator presentation identifies the range of evaluation at `x` with `A[x]`.
  exact
    (AlgHom.range_eq_top _).mp
      ((Algebra.adjoin_singleton_eq_range_aeval A x).symm.trans hx)

/-- Helper for Chap10 Lemma 10 116 3: in a one-generator presentation, contracting the lifted
prime back to the coefficient ring agrees with direct contraction. -/
private lemma singleGenerator_comap_under_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    q'.asIdeal.under A = q.asIdeal.under A := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  ext a
  -- Evaluation sends the coefficient polynomial `C a` to the original scalar in `B`.
  change Polynomial.C a ∈ Ideal.comap φ.toRingHom q.asIdeal ↔ algebraMap A B a ∈ q.asIdeal
  rw [Ideal.mem_comap]
  simp [φ]

/-- Helper for Chap10 Lemma 10 116 3: the one-generator surjective presentation identifies the
residue fields at corresponding primes. -/
private lemma singleGenerator_residueFieldMap_bijective_of_surjective_aeval
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    Function.Bijective (Ideal.ResidueField.map q'.asIdeal q.asIdeal φ.toRingHom rfl) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  have hsurj : Function.Surjective φ :=
    singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  -- Surjectivity of the presentation is stable on local rings, hence on residue fields.
  exact (RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective _ _ rfl

/-- Helper for Chap10 Lemma 10 116 3: equal base primes give the same residue-field
transcendence-degree term for a fixed target prime. -/
private lemma residueFieldTrdeg_toNat_eq_of_base_eq
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {p p' : Ideal R} [p.IsPrime] [p'.IsPrime]
    {P : Ideal A} [P.IsPrime] [P.LiesOver p] [P.LiesOver p'] (hp : p = p') :
    Cardinal.toNat (Algebra.trdeg p.ResidueField P.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p'.ResidueField P.ResidueField) := by
  -- Substituting the base prime avoids rewriting through residue-field implementation details.
  cases hp
  rfl

/-- Helper for Chap10 Lemma 10 116 3: the one-generator residue-field isomorphism preserves the
transcendence-degree term after identifying the contracted base prime. -/
private lemma singleGenerator_residueFieldTrdeg_toNat_eq_comap
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let p : Ideal A := q'.asIdeal.under A
  letI : q'.asIdeal.LiesOver p := ⟨rfl⟩
  have hp : p = q.asIdeal.under A := by
    -- The polynomial antecedent and the original prime have the same contraction to `A`.
    simpa [p, q'] using singleGenerator_comap_under_eq (A := A) (B := B) x q
  letI : q.asIdeal.LiesOver p := by
    refine ⟨?_⟩
    exact hp
  let f : q'.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map q'.asIdeal q.asIdeal φ.toRingHom rfl
  have hf_base :
      f.comp (algebraMap p.ResidueField q'.asIdeal.ResidueField) =
        algebraMap p.ResidueField q.asIdeal.ResidueField := by
    -- It is enough to compare the two residue-field maps on representatives from `A`.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext a
    calc
      f (algebraMap p.ResidueField q'.asIdeal.ResidueField
          (algebraMap A p.ResidueField a))
          = f (algebraMap A q'.asIdeal.ResidueField a) := by
              rw [IsScalarTower.algebraMap_apply A p.ResidueField
                q'.asIdeal.ResidueField a]
      _ = f (algebraMap (Polynomial A) q'.asIdeal.ResidueField (Polynomial.C a)) := by
              rw [IsScalarTower.algebraMap_apply A (Polynomial A) q'.asIdeal.ResidueField a,
                Polynomial.algebraMap_eq]
      _ = algebraMap B q.asIdeal.ResidueField (φ (Polynomial.C a)) := by
              rw [Ideal.ResidueField.map_algebraMap]
              rfl
      _ = algebraMap B q.asIdeal.ResidueField (algebraMap A B a) := by
              simp [φ]
      _ = algebraMap A q.asIdeal.ResidueField a := by
              rw [IsScalarTower.algebraMap_apply A B q.asIdeal.ResidueField a]
      _ = algebraMap p.ResidueField q.asIdeal.ResidueField
            (algebraMap A p.ResidueField a) := by
              rw [IsScalarTower.algebraMap_apply A p.ResidueField q.asIdeal.ResidueField a]
  let fAlg : q'.asIdeal.ResidueField →ₐ[p.ResidueField] q.asIdeal.ResidueField :=
    { f with
      commutes' := fun r ↦ DFunLike.congr_fun hf_base r }
  let e : q'.asIdeal.ResidueField ≃ₐ[p.ResidueField] q.asIdeal.ResidueField :=
    AlgEquiv.ofBijective fAlg
      (singleGenerator_residueFieldMap_bijective_of_surjective_aeval
        (A := A) (B := B) x hx q)
  have htarget :
      Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q'.asIdeal.ResidueField) := by
    -- Transport transcendence degree across the residue-field algebra equivalence.
    simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e).symm
  have hleftBase :
      Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
    -- Replace the direct contraction by the polynomial-side contraction through the equality
    -- proved above.
    exact
      (residueFieldTrdeg_toNat_eq_of_base_eq
        (R := A) (A := B) (p := p) (p' := q.asIdeal.under A) (P := q.asIdeal) hp).symm
  -- Finally assemble the base-prime replacement with the residue-field isomorphism.
  calc
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := hleftBase
    _ = Cardinal.toNat (Algebra.trdeg p.ResidueField q'.asIdeal.ResidueField) := htarget
    _ = Cardinal.toNat
          (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
          rfl

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: in the injective one-generator
polynomial branch, the generic fraction-field transcendence degree is one. -/
private lemma singleGenerator_fractionRingTrdeg_eq_one_of_ker_eq_bot
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) :
    RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] B).toRingHom = ⊥ →
      Algebra.fractionRingTrdeg hinj = 1 := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  intro hker
  let _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hφ_surj : Function.Surjective φ :=
    singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  have hφ_inj : Function.Injective φ := by
    -- The zero-kernel branch makes the polynomial presentation an isomorphism.
    rw [RingHom.injective_iff_ker_eq_bot]
    simpa [φ] using hker
  let e : Polynomial A ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let eFrac : FractionRing (Polynomial A) ≃ₐ[A] FractionRing B :=
    IsFractionRing.algEquivOfAlgEquiv e
  let _ : FaithfulSMul A (Polynomial A) :=
    (faithfulSMul_iff_algebraMap_injective A (Polynomial A)).mpr (by
      simpa using (Polynomial.C_injective (R := A)))
  let _ : FaithfulSMul (Polynomial A) (FractionRing (Polynomial A)) :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial A)
      (FractionRing (Polynomial A))).mpr
      (IsFractionRing.injective (Polynomial A) (FractionRing (Polynomial A)))
  let _ : FaithfulSMul A (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective A (FractionRing A)).mpr
      (IsFractionRing.injective A (FractionRing A))
  have hfracPoly :
      Algebra.trdeg (Polynomial A) (FractionRing (Polynomial A)) = 0 := by
    let _ : Algebra.IsAlgebraic (Polynomial A) (FractionRing (Polynomial A)) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial A)
          (K := FractionRing (Polynomial A)) (C := FractionRing (Polynomial A))).mpr
          (inferInstance :
            Algebra.IsAlgebraic (FractionRing (Polynomial A))
              (FractionRing (Polynomial A)))
    -- Passing from a domain to its fraction field adds no transcendence.
    simpa using
      (trdeg_eq_zero :
        Algebra.trdeg (Polynomial A) (FractionRing (Polynomial A)) = 0)
  have hpolyFrac :
      Algebra.trdeg A (FractionRing (Polynomial A)) = 1 := by
    -- Compute `Frac(A[X])` over `A` by the tower `A -> A[X] -> Frac(A[X])`.
    have hsum := trdeg_add_eq (R := A) (S := Polynomial A)
      (A := FractionRing (Polynomial A))
    rw [Polynomial.trdeg_of_isDomain, hfracPoly] at hsum
    simpa using hsum.symm
  have hAFracA :
      Algebra.trdeg A (FractionRing A) = 0 := by
    let _ : Algebra.IsAlgebraic A (FractionRing A) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing A) = 0)
  have hAFracB :
      Algebra.trdeg A (FractionRing B) = 1 := by
    -- Transport the polynomial computation across the one-generator presentation.
    calc
      Algebra.trdeg A (FractionRing B)
          = Algebra.trdeg A (FractionRing (Polynomial A)) := by
              simpa using (AlgEquiv.trdeg_eq (R := A) eFrac).symm
      _ = 1 := hpolyFrac
  have hFrac :
      Algebra.trdeg (FractionRing A) (FractionRing B) = 1 := by
    -- Algebraic base change from `A` to `Frac(A)` does not change the generic term.
    have hsum := trdeg_add_eq (R := A) (S := FractionRing A) (A := FractionRing B)
    rw [hAFracA, hAFracB] at hsum
    simpa using hsum
  change Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 1
  simpa [hFrac] using rfl

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: in the one-generator quotient branch
with nonzero kernel, the generic fraction-field transcendence degree is zero. -/
private lemma singleGenerator_fractionRingTrdeg_eq_zero_of_ker_ne_bot
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) :
    RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] B).toRingHom ≠ ⊥ →
      Algebra.fractionRingTrdeg hinj = 0 := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  intro hker
  let _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let _ : FaithfulSMul A (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective A (FractionRing A)).mpr
      (IsFractionRing.injective A (FractionRing A))
  have hxAlg : IsAlgebraic A x := by
    -- A nonzero kernel gives a nontrivial polynomial relation for `x`.
    rw [isAlgebraic_iff_not_injective]
    intro hφ_inj
    apply hker
    rw [RingHom.injective_iff_ker_eq_bot] at hφ_inj
    simpa [φ] using hφ_inj
  have hBAlg : Algebra.IsAlgebraic A B := by
    -- Since `B = A[x]`, algebraicity of the generator makes all of `B` algebraic.
    refine Algebra.isAlgebraic_iff.2 ?_
    rw [← hx]
    refine (Algebra.isAlgebraic_adjoin_iff (R := A) (s := ({x} : Set B))).2 ?_
    intro y hy
    simpa [Set.mem_singleton_iff.mp hy] using hxAlg
  have hAFracB :
      Algebra.trdeg A (FractionRing B) = 0 := by
    let _ : Algebra.IsAlgebraic A B := hBAlg
    let _ : Algebra.IsAlgebraic B (FractionRing B) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := B) (K := FractionRing B)
          (C := FractionRing B)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing B) (FractionRing B))
    let _ : Algebra.IsAlgebraic A (FractionRing B) :=
      Algebra.IsAlgebraic.trans (R := A) (S := B) (A := FractionRing B)
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing B) = 0)
  have hAFracA :
      Algebra.trdeg A (FractionRing A) = 0 := by
    let _ : Algebra.IsAlgebraic A (FractionRing A) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing A) = 0)
  have hFrac :
      Algebra.trdeg (FractionRing A) (FractionRing B) = 0 := by
    -- The algebraic top extension forces the fraction-field generic term to vanish.
    have hsum := trdeg_add_eq (R := A) (S := FractionRing A) (A := FractionRing B)
    rw [hAFracA, hAFracB] at hsum
    simpa using hsum
  change Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0
  simpa [hFrac] using rfl

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: after coercing to `WithBot ℕ∞`,
the natural-number prime height of a Noetherian prime is the Krull dimension of its localization. -/
private lemma primeHeightNatCast_eq_ringKrullDim_localizationAtPrime
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    (((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime p) := by
  -- Rewrite local dimension as height and use Noetherian finiteness to recover `toNat`.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    Ideal.height_eq_primeHeight]
  exact_mod_cast ENat.coe_toNat (Ideal.primeHeight_ne_top p)

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: in a one-generator presentation, the
prime complement of the comapped prime maps onto the target prime complement. -/
private lemma singleGenerator_primeCompl_map_comap_aeval
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  have hφ_surj : Function.Surjective φ :=
    singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  ext y
  constructor
  · -- A mapped element outside the comapped prime is outside the target prime.
    rintro ⟨z, hz, rfl⟩
    simpa [q', Ideal.mem_primeCompl_iff, Ideal.mem_comap] using hz
  · -- Surjectivity of the one-generator presentation supplies the required preimage.
    intro hy
    obtain ⟨z, rfl⟩ := hφ_surj y
    refine ⟨z, ?_, rfl⟩
    simpa [q', Ideal.mem_primeCompl_iff, Ideal.mem_comap] using hy

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: the localized one-generator evaluation
map is surjective at corresponding primes. -/
private lemma singleGenerator_localAlgHom_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    let L := Localization.AtPrime q'.asIdeal
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    Function.Surjective φloc := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let L := Localization.AtPrime q'.asIdeal
  let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
    Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
  have hφ_surj : Function.Surjective φ :=
    singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  -- Surjectivity of the presentation is preserved by the induced map on local rings.
  simpa [φloc, Localization.localAlgHom] using
    (RingHom.surjectiveOnStalks_of_surjective hφ_surj).localRingHom_surjective
      q'.asIdeal q.asIdeal rfl

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: localizing the one-generator
presentation sends the original kernel to the kernel of the localized map. -/
private lemma singleGenerator_localAlgHom_ker_eq_map_kernel
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    let L := Localization.AtPrime q'.asIdeal
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    RingHom.ker φloc.toRingHom = Ideal.map (algebraMap (Polynomial A) L) n := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let L := Localization.AtPrime q'.asIdeal
  let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
    Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
  have hprimeCompl :
      Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl :=
    singleGenerator_primeCompl_map_comap_aeval (A := A) (B := B) x hx q
  -- The localization API computes this kernel once the two prime complements are identified.
  dsimp [φloc, n]
  simpa [Localization.localAlgHom, Localization.localRingHom, L] using
    (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
      φ.toRingHom hprimeCompl)

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: the localized target is the quotient of
the localized polynomial source by the localized evaluation kernel. -/
private noncomputable abbrev singleGenerator_localQuotientAlgEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    let L := Localization.AtPrime q'.asIdeal
    let K : Ideal L := Ideal.map (algebraMap (Polynomial A) L) n
    Localization.AtPrime q.asIdeal ≃ₐ[A] (L ⧸ K) :=
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let L := Localization.AtPrime q'.asIdeal
  let K : Ideal L := Ideal.map (algebraMap (Polynomial A) L) n
  let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
    Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
  let hφloc_surj : Function.Surjective φloc :=
    singleGenerator_localAlgHom_surjective (A := A) (B := B) x hx q
  let hker : RingHom.ker φloc.toRingHom = K :=
    singleGenerator_localAlgHom_ker_eq_map_kernel (A := A) (B := B) x hx q
  (Ideal.quotientKerAlgEquivOfSurjective hφloc_surj).symm.trans
    (Ideal.quotientEquivAlgOfEq A hker)

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: the kernel of a one-generator
evaluation map contracts trivially to the coefficient ring when the original algebra map is
injective. -/
private lemma singleGenerator_aevalKernel_under_eq_bot
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hinj : Function.Injective (algebraMap A B)) :
    (RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] B).toRingHom).under A =
      (⊥ : Ideal A) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  ext a
  -- Constants in the evaluation kernel are exactly elements killed by `A → B`, hence zero.
  change φ (Polynomial.C a) = 0 ↔ a ∈ (⊥ : Ideal A)
  constructor
  · intro ha
    exact hinj <| by simpa [φ] using ha
  · intro ha
    rw [Ideal.mem_bot] at ha
    subst a
    simp [φ]

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: a polynomial prime whose contraction to
the coefficient domain is zero is disjoint from the nonzero constant polynomials. -/
private lemma polynomialPrime_disjoint_coeffPrimeCompl_of_under_bot
    {A : Type u} [CommRing A] [IsDomain A] {P : Ideal (Polynomial A)} [P.IsPrime]
    (hunder : P.under A = (⊥ : Ideal A)) :
    Disjoint (((⊥ : Ideal A).primeCompl.map Polynomial.C : Submonoid (Polynomial A)) :
      Set (Polynomial A)) (P : Set (Polynomial A)) := by
  -- Pull an alleged intersection element back to a coefficient in the zero contraction.
  refine Set.disjoint_left.mpr fun f hf hfP ↦ ?_
  rcases hf with ⟨a, ha, rfl⟩
  have hcoeff : a ∈ P.under A := by
    simpa [Ideal.under_def, Polynomial.algebraMap_eq] using hfP
  have hbot : a ∈ (⊥ : Ideal A) := by
    simpa [hunder] using hcoeff
  exact ha hbot

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: localizing coefficients at the zero
prime does not kill a nonzero polynomial prime disjoint from the nonzero constants. -/
private lemma polynomialPrime_map_coeffLocalization_ne_bot_of_under_bot_ne_bot
    {A : Type u} [CommRing A] [IsDomain A] {P : Ideal (Polynomial A)} [P.IsPrime]
    (hP : P ≠ ⊥) (hunder : P.under A = (⊥ : Ideal A)) :
    let F0 := Localization.AtPrime (⊥ : Ideal A)
    let S := Polynomial F0
    letI : Algebra (Polynomial A) S := (Polynomial.mapRingHom (algebraMap A F0)).toAlgebra
    Ideal.map (algebraMap (Polynomial A) S) P ≠ ⊥ := by
  dsimp
  let F0 := Localization.AtPrime (⊥ : Ideal A)
  let S := Polynomial F0
  let M : Submonoid (Polynomial A) := (⊥ : Ideal A).primeCompl.map Polynomial.C
  letI : Algebra (Polynomial A) S := (Polynomial.mapRingHom (algebraMap A F0)).toAlgebra
  letI : IsLocalization M S := Polynomial.isLocalization (⊥ : Ideal A).primeCompl F0
  have hdisj : Disjoint (M : Set (Polynomial A)) (P : Set (Polynomial A)) :=
    polynomialPrime_disjoint_coeffPrimeCompl_of_under_bot hunder
  have hcomap :
      Ideal.comap (algebraMap (Polynomial A) S)
        (Ideal.map (algebraMap (Polynomial A) S) P) = P := by
    -- The coefficient localization is disjoint from `P`, so map-then-comap returns `P`.
    simpa [M, S] using
      IsLocalization.comap_map_of_isPrime_disjoint M S (I := P) inferInstance hdisj
  intro hmap
  apply hP
  have hmap' : Ideal.map (algebraMap (Polynomial A) S) P = (⊥ : Ideal S) := by
    exact hmap
  have hinjA : Function.Injective (algebraMap A F0) :=
    IsLocalization.injective F0 (show (⊥ : Ideal A).primeCompl ≤ nonZeroDivisors A from
      (⊥ : Ideal A).primeCompl_le_nonZeroDivisors)
  have hinjPoly : Function.Injective (algebraMap (Polynomial A) S) := by
    -- Injectivity of coefficient localization lifts coefficientwise to polynomials.
    intro f g hfg
    exact Polynomial.map_injective (algebraMap A F0) hinjA hfg
  calc
    P = Ideal.comap (algebraMap (Polynomial A) S)
        (Ideal.map (algebraMap (Polynomial A) S) P) := hcomap.symm
    _ = Ideal.comap (algebraMap (Polynomial A) S) (⊥ : Ideal S) := by rw [hmap']
    _ = (⊥ : Ideal (Polynomial A)) := Ideal.comap_bot_of_injective _ hinjPoly

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: a nonzero polynomial prime with zero
coefficient contraction has height one. -/
private lemma polynomialPrime_height_eq_one_of_under_bot_ne_bot
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {P : Ideal (Polynomial A)} [P.IsPrime]
    (hP : P ≠ ⊥) (hunder : P.under A = (⊥ : Ideal A)) :
    P.height = 1 := by
  let F0 := Localization.AtPrime (⊥ : Ideal A)
  let S := Polynomial F0
  let M : Submonoid (Polynomial A) := (⊥ : Ideal A).primeCompl.map Polynomial.C
  letI : Algebra (Polynomial A) S := (Polynomial.mapRingHom (algebraMap A F0)).toAlgebra
  letI : IsLocalization M S := Polynomial.isLocalization (⊥ : Ideal A).primeCompl F0
  have hdisj : Disjoint (M : Set (Polynomial A)) (P : Set (Polynomial A)) :=
    polynomialPrime_disjoint_coeffPrimeCompl_of_under_bot hunder
  let P' : Ideal S := Ideal.map (algebraMap (Polynomial A) S) P
  have hP'_prime : P'.IsPrime := by
    -- The localized image of a prime remains prime because the denominators are disjoint.
    dsimp [P']
    exact IsLocalization.isPrime_of_isPrime_disjoint M S P inferInstance hdisj
  letI : P'.IsPrime := hP'_prime
  have hP'_ne : P' ≠ ⊥ := by
    simpa [P', S, F0] using
      polynomialPrime_map_coeffLocalization_ne_bot_of_under_bot_ne_bot hP hunder
  have hbot_min : (⊥ : Ideal A) ∈ minimalPrimes A := by
    -- In a domain, the zero ideal is the unique minimal prime.
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  let pmin : minimalPrimes A := ⟨(⊥ : Ideal A), hbot_min⟩
  have hfield : IsField F0 := by
    simpa [F0, pmin] using isField_localizationAtPrime_of_minimalPrime pmin
  letI : Field F0 := hfield.toField
  have hP'_max : P'.IsMaximal := IsPrime.to_maximal_ideal hP'_ne
  letI : P'.IsMaximal := hP'_max
  have hP'_height : P'.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal P' Ideal.polynomial_not_isField
  have hheight_map : P'.height = P.height := by
    -- Transport the height calculation back along the coefficient localization.
    simpa [P'] using IsLocalization.height_map_of_disjoint M P hdisj
  exact hheight_map ▸ hP'_height

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: if a localized prime contracts to a
height-one prime, then its prime height is one. -/
private lemma localizedPrime_primeHeight_eq_one_of_comap_height_one
    {R : Type u} {T : Type v} [CommRing R] [CommRing T]
    (M : Submonoid R) [Algebra R T] [IsLocalization M T]
    {P : Ideal R} [P.IsPrime] {K : Ideal T} [K.IsPrime]
    (hcomap : Ideal.comap (algebraMap R T) K = P) (hP : P.height = 1) :
    Ideal.primeHeight K = 1 := by
  -- Compare height across localization, then return from height to prime height.
  calc
    Ideal.primeHeight K = K.height := (Ideal.height_eq_primeHeight (I := K)).symm
    _ = (Ideal.comap (algebraMap R T) K).height := (IsLocalization.height_comap M K).symm
    _ = P.height := by rw [hcomap]
    _ = 1 := hP

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: in the nonzero-kernel one-generator
case, catenarity makes the target prime height exactly one less than the height of its polynomial
antecedent. -/
private lemma singleGenerator_quotientCase_primeHeight_succ_eq_comap_primeHeight_of_universallyCatenary
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [Algebra A B] [UniversallyCatenaryRing.{u, u} A]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    n ≠ ⊥ →
      ENat.toNat (Ideal.primeHeight q.asIdeal) + 1 =
        ENat.toNat (Ideal.primeHeight q'.asIdeal) := by
  dsimp
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let L := Localization.AtPrime q'.asIdeal
  let K : Ideal L := Ideal.map (algebraMap (Polynomial A) L) n
  intro hn
  -- Route correction: the quotient equivalence is consumed through the dedicated `A`-algebra
  -- helper, avoiding the stale inline `L`-algebra quotient construction.
  let e : Localization.AtPrime q.asIdeal ≃ₐ[A] (L ⧸ K) :=
    singleGenerator_localQuotientAlgEquiv (A := A) (B := B) x hx q
  have hn_prime : n.IsPrime := by
    dsimp [n]
    exact RingHom.ker_isPrime φ.toRingHom
  letI : n.IsPrime := hn_prime
  have hK_prime : K.IsPrime := by
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    have hker :
        RingHom.ker φloc.toRingHom = K :=
      singleGenerator_localAlgHom_ker_eq_map_kernel (A := A) (B := B) x hx q
    rw [← hker]
    exact RingHom.ker_isPrime φloc.toRingHom
  letI : K.IsPrime := hK_prime
  have hcomap :
      Ideal.comap (algebraMap (Polynomial A) L) K = n := by
    have hn_le : n ≤ q'.asIdeal := by
      intro f hf
      change f ∈ Ideal.comap φ.toRingHom q.asIdeal
      rw [Ideal.mem_comap]
      have hzero : φ f = 0 := by
        simpa [n, RingHom.mem_ker] using hf
      simpa [hzero] using (show (0 : B) ∈ q.asIdeal from Ideal.zero_mem _)
    have hdisj : Disjoint (q'.asIdeal.primeCompl : Set (Polynomial A)) n := by
      rw [Set.disjoint_left]
      intro f hfq hfn
      exact (Ideal.mem_primeCompl_iff.mp hfq) (hn_le hfn)
    -- Contracting the localized kernel recovers the original polynomial kernel.
    simpa [K] using
      (IsLocalization.comap_map_of_isPrime_disjoint q'.asIdeal.primeCompl L hn_prime hdisj)
  have hunder : n.under A = (⊥ : Ideal A) := by
    -- Reuse the extracted contraction helper for the coefficient-side normalization.
    simpa [n, φ] using singleGenerator_aevalKernel_under_eq_bot (A := A) (B := B) x hinj
  letI : UniversallyCatenaryRing (Polynomial A) :=
    universallyCatenaryRing_of_finiteType (A := A) (S := Polynomial A)
  letI : UniversallyCatenaryRing L := localization_universallyCatenaryRing q'.asIdeal.primeCompl
  have hK :
      Ideal.primeHeight K = 1 := by
    -- First compute the source kernel height by localizing coefficients to the fraction field.
    have hn_height : n.height = 1 :=
      polynomialPrime_height_eq_one_of_under_bot_ne_bot (P := n) hn hunder
    exact
      localizedPrime_primeHeight_eq_one_of_comap_height_one
        q'.asIdeal.primeCompl hcomap hn_height
  have hdrop :
      ringKrullDim (L ⧸ K) + 1 = ringKrullDim L :=
    ringKrullDim_quotient_add_eq_of_primeHeight_one_catenary_local_domain (L := L) K hK
  have hlocal :
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1 =
        ringKrullDim (Localization.AtPrime q'.asIdeal) := by
    -- Transport the exact quotient drop through the localized one-generator presentation.
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1 =
          ringKrullDim (L ⧸ K) + 1 := by
            rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
      _ = ringKrullDim L := hdrop
      _ = ringKrullDim (Localization.AtPrime q'.asIdeal) := by
            rfl
  have hheight :
      ((((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) + 1) =
        (((ENat.toNat (Ideal.primeHeight q'.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    letI : Algebra.FiniteType A B := by
      have hφ_surj : Function.Surjective φ :=
        singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
      exact Algebra.FiniteType.of_surjective φ hφ_surj
    letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    -- Rewrite both local Krull dimensions as natural-number prime heights.
    rw [primeHeightNatCast_eq_ringKrullDim_localizationAtPrime (p := q.asIdeal),
      primeHeightNatCast_eq_ringKrullDim_localizationAtPrime (p := q'.asIdeal)]
    simpa [L] using hlocal
  exact_mod_cast hheight
/-  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let L := Localization.AtPrime q'.asIdeal
  let K : Ideal L := Ideal.map (algebraMap (Polynomial A) L) n
  intro hn
  let e :
      Localization.AtPrime q.asIdeal ≃ₐ[A] (L ⧸ K) :=
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    let hφ_surj : Function.Surjective φ :=
      singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
    let hφloc_surj : Function.Surjective φloc := by
      -- Localizing a surjective map at corresponding primes stays surjective on local rings.
      simpa [φloc, Localization.localAlgHom] using
        (RingHom.surjectiveOnStalks_of_surjective hφ_surj).localRingHom_surjective
          q'.asIdeal q.asIdeal rfl
    let hprimeCompl :
        Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
      -- The source and target localizations are taken at corresponding prime complements.
      ext f
      simp [q', Ideal.mem_primeCompl, Ideal.mem_comap]
    let hker :
        RingHom.ker φloc.toRingHom = K := by
      -- Localization turns the original kernel into the displayed localized ideal.
      dsimp [φloc, K, n]
      simpa [Localization.localAlgHom, Localization.localRingHom] using
        (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
          φ.toRingHom hprimeCompl)
    -- Repackage the localized surjection as a quotient by its kernel, then normalize that kernel.
    (Ideal.quotientKerAlgEquivOfSurjective hφloc_surj).symm.trans
      (Ideal.quotientEquivAlgOfEq L hker)
  letI : UniversallyCatenaryRing (Polynomial A) :=
    universallyCatenaryRing_of_finiteType (A := A) (S := Polynomial A)
  letI : UniversallyCatenaryRing L := localization_universallyCatenaryRing q'.asIdeal.primeCompl
  have hK :
      Ideal.primeHeight K = 1 := by
    have hn_prime : n.IsPrime := by
      dsimp [n]
      exact RingHom.ker_isPrime φ.toRingHom
    letI : n.IsPrime := hn_prime
    have hK_prime : K.IsPrime := by
      let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
        Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
      have hprimeCompl :
          Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
        -- Reuse the corresponding-prime complement normalization for the localized kernel.
        ext f
        simp [q', Ideal.mem_primeCompl, Ideal.mem_comap]
      have hker :
          RingHom.ker φloc.toRingHom = K := by
        dsimp [φloc, K, n]
        simpa [Localization.localAlgHom, Localization.localRingHom] using
          (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
            φ.toRingHom hprimeCompl)
      rw [← hker]
      exact RingHom.ker_isPrime φloc.toRingHom
    letI : K.IsPrime := hK_prime
    have hcomap :
        Ideal.comap (algebraMap (Polynomial A) L) K = n := by
      have hn_le : n ≤ q'.asIdeal := by
        intro f hf
        change f ∈ Ideal.comap φ.toRingHom q.asIdeal
        rw [Ideal.mem_comap]
        have hzero : φ f = 0 := by
          simpa [n, RingHom.mem_ker] using hf
        simpa [hzero] using (show (0 : B) ∈ q.asIdeal from Ideal.zero_mem _)
      have hdisj : Disjoint (q'.asIdeal.primeCompl : Set (Polynomial A)) n := by
        simpa [Set.disjoint_iff, Set.ext_iff, not_imp_comm] using hn_le
      -- Contracting the localized kernel recovers the original polynomial kernel.
      simpa [K] using
        (IsLocalization.comap_map_of_isPrime_disjoint q'.asIdeal.primeCompl L hn_prime hdisj)
    have hbot_height : (⊥ : Ideal A).height = 0 := by
      have hbot_primeHeight : (⊥ : Ideal A).primeHeight = 0 := by
        rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
        simp
      simpa [Ideal.height_eq_primeHeight] using hbot_primeHeight
    have hunder : n.under A = (⊥ : Ideal A) := by
      ext a
      -- The constants in the kernel are exactly the kernel of the injective map `A → B`.
      change φ (Polynomial.C a) = 0 ↔ a ∈ (⊥ : Ideal A)
      constructor
      · intro ha
        exact hinj <| by simpa [φ] using ha
      · intro ha
        simpa [φ] using ha
    have hheight :
        K.height = 1 := by
      calc
        K.height = (Ideal.comap (algebraMap (Polynomial A) L) K).height := by
          symm
          exact IsLocalization.height_comap q'.asIdeal.primeCompl K
        _ = n.height := by rw [hcomap]
        _ = (⊥ : Ideal A).height + 1 := by
          letI : n.LiesOver (⊥ : Ideal A) := by
            refine ⟨?_⟩
            change n.under A = (⊥ : Ideal A)
            exact hunder
          simpa using (Polynomial.height_eq_height_add_one (p := (⊥ : Ideal A)) (P := n))
        _ = 1 := by simp [hbot_height]
    -- Convert the computed ideal height to prime height for the exact-drop owner.
    simpa [Ideal.height_eq_primeHeight] using hheight
  have hdrop :
      ringKrullDim (L ⧸ K) + 1 = ringKrullDim L :=
    ringKrullDim_quotient_add_eq_of_primeHeight_one_catenary_local_domain (L := L) K hK
  have hlocal :
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1 =
        ringKrullDim (Localization.AtPrime q'.asIdeal) := by
    -- Transport the exact quotient drop through the localized one-generator presentation.
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1 =
          ringKrullDim (L ⧸ K) + 1 := by
            rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
      _ = ringKrullDim L := hdrop
      _ = ringKrullDim (Localization.AtPrime q'.asIdeal) := by
            rfl
  have hheight :
      ((((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) + 1) =
        (((ENat.toNat (Ideal.primeHeight q'.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    -- Rewrite both local Krull dimensions as natural-number prime heights.
    rw [primeHeightNatCast_eq_ringKrullDim_localizationAtPrime (p := q.asIdeal)]
    simpa [L] using hlocal
  exact_mod_cast hheight
-/

/-- Helper for Chap10 Lemma 10 116 3: the source map into a finite adjoin stage is injective
when the ambient algebra map is injective. -/
private lemma adjoinFinset_algebraMap_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) (s : Finset S) :
    Function.Injective (algebraMap R (Algebra.adjoin R (s : Set S))) := by
  -- Compare elements after coercing the finite adjoin stage back into the ambient algebra.
  intro x y hxy
  apply hinj
  change (((algebraMap R (Algebra.adjoin R (s : Set S)) x :
      Algebra.adjoin R (s : Set S)) : S)) =
    (((algebraMap R (Algebra.adjoin R (s : Set S)) y :
      Algebra.adjoin R (s : Set S)) : S))
  simpa using congrArg (fun z : Algebra.adjoin R (s : Set S) ↦ (z : S)) hxy

/-- Helper for Chap10 Lemma 10 116 3: each finite adjoin stage is finite type over the source
ring. -/
private lemma adjoinFinset_finiteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (s : Finset S) :
    Algebra.FiniteType R (Algebra.adjoin R (s : Set S)) := by
  let T : Subalgebra R S := Algebra.adjoin R (s : Set S)
  have hfg : T.FG := by
    -- The stage is generated by the finite set appearing in its definition.
    exact Subalgebra.fg_def.2 ⟨(s : Set S), s.finite_toSet, rfl⟩
  have hfgTop : (⊤ : Subalgebra R T).FG := (Subalgebra.fg_top T).2 hfg
  have hftTop : Algebra.FiniteType R (⊤ : Subalgebra R T) :=
    (Subalgebra.fg_iff_finiteType (⊤ : Subalgebra R T)).mp hfgTop
  -- Transfer finite type across the canonical equivalence from the top subalgebra to the stage.
  exact Algebra.FiniteType.equiv hftTop Subalgebra.topEquiv

/-- Helper for Chap10 Lemma 10 116 3: finite adjoin stages over a Noetherian source are
Noetherian. -/
private lemma adjoinFinset_isNoetherianRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] (s : Finset S) :
    IsNoetherianRing (Algebra.adjoin R (s : Set S)) := by
  let T : Subalgebra R S := Algebra.adjoin R (s : Set S)
  have hfg : T.FG := by
    -- The displayed finite set presents the subalgebra as a finite adjoin.
    exact Subalgebra.fg_def.2 ⟨(s : Set S), s.finite_toSet, rfl⟩
  exact isNoetherianRing_of_fg hfg

/-- Helper for Chap10 Lemma 10 116 3: a finite adjoin stage is contained in the stage obtained
by inserting one more generator. -/
private lemma adjoinFinset_le_insert_adjoinFinset
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [DecidableEq S] (t : Finset S) (x : S) :
    Algebra.adjoin R (t : Set S) ≤
      Algebra.adjoin R (((insert x t : Finset S) : Set S)) := by
  -- Monotonicity of `Algebra.adjoin` turns the set inclusion of generators into stage inclusion.
  have hsubset : (t : Set S) ⊆ (((insert x t : Finset S) : Set S)) := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  exact Algebra.adjoin_mono hsubset

/-- Helper for Chap10 Lemma 10 116 3: the inserted generator belongs to the inserted finite
adjoin stage. -/
private lemma insertedElement_mem_adjoinFinsetStage
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [DecidableEq S] (t : Finset S) (x : S) :
    x ∈ Algebra.adjoin R (((insert x t : Finset S) : Set S)) := by
  -- The new element is one of the displayed generators of the inserted stage.
  exact Algebra.subset_adjoin (by simp)

/-- Helper for Chap10 Lemma 10 116 3: after adjoining one new element to a finite stage, the new
stage is generated over the previous stage by that single inserted element. -/
private lemma adjoinSingleton_eq_top_over_adjoinFinsetStage
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [DecidableEq S] (t : Finset S) (x : S) :
    let T : Subalgebra R S := Algebra.adjoin R (t : Set S)
    let A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
    let hTA : T ≤ A := adjoinFinset_le_insert_adjoinFinset (R := R) (S := S) t x
    letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
    letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
    let xA : A := ⟨x, insertedElement_mem_adjoinFinsetStage (R := R) (S := S) t x⟩
    Algebra.adjoin T ({xA} : Set A) = ⊤ := by
  classical
  dsimp
  set T : Subalgebra R S := Algebra.adjoin R (t : Set S)
  set A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
  have hTA : T ≤ A := by
    -- Reuse the named inclusion after introducing stable abbreviations for the two stages.
    simpa [T, A] using adjoinFinset_le_insert_adjoinFinset (R := R) (S := S) t x
  letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
  letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
  have hxA_mem : x ∈ A := by
    -- Package the inserted generator as an element of the new stage.
    simpa [A] using insertedElement_mem_adjoinFinsetStage (R := R) (S := S) t x
  let xA : A := ⟨x, hxA_mem⟩
  apply top_unique
  intro y hy
  clear hy
  -- Check the finite-stage generators and then close under the algebra operations.
  refine Algebra.adjoin_induction
    (s := (((insert x t : Finset S) : Set S)))
    (p := fun z hz => ∀ hzA : z ∈ A, (⟨z, hzA⟩ : A) ∈ Algebra.adjoin T ({xA} : Set A))
    ?_ ?_ ?_ ?_ y.2 y.2
  · intro z hz hzA
    rcases Finset.mem_insert.mp hz with rfl | hzt
    · -- The new generator is exactly the chosen singleton generator over `T`.
      change xA ∈ Algebra.adjoin T ({xA} : Set A)
      exact Algebra.subset_adjoin (by simp)
    · -- Old generators already come from the previous stage through the inclusion `T → A`.
      have hzT : z ∈ T := by
        dsimp [T]
        exact Algebra.subset_adjoin (show z ∈ (t : Set S) from hzt)
      change algebraMap T A ⟨z, hzT⟩ ∈ Algebra.adjoin T ({xA} : Set A)
      exact Subalgebra.algebraMap_mem _ _
  · intro r hrA
    -- Scalars from `R` lie in the previous stage and hence in the singleton adjoin over it.
    change algebraMap T A (algebraMap R T r) ∈ Algebra.adjoin T ({xA} : Set A)
    exact Subalgebra.algebraMap_mem _ _
  · intro z w hz hw hz_mem hw_mem hzwA
    -- The singleton adjoin is closed under addition.
    have hzA : z ∈ A := by
      simpa [A] using hz
    have hwA : w ∈ A := by
      simpa [A] using hw
    simpa using Subalgebra.add_mem _ (hz_mem hzA) (hw_mem hwA)
  · intro z w hz hw hz_mem hw_mem hzwA
    -- The singleton adjoin is closed under multiplication.
    have hzA : z ∈ A := by
      simpa [A] using hz
    have hwA : w ∈ A := by
      simpa [A] using hw
    simpa using Subalgebra.mul_mem _ (hz_mem hzA) (hw_mem hwA)

/-- Helper for Chap10 Lemma 10 116 3: a finite type algebra is generated by some finite adjoin
stage. -/
private lemma existsFinset_adjoin_eq_top_of_finiteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] :
    ∃ s : Finset S, Algebra.adjoin R (s : Set S) = ⊤ := by
  -- Extract finite generators from the finite-type structure and convert that finite set to a
  -- `Finset` for the induction over adjoin stages.
  obtain ⟨t, htfinite, htTop⟩ := Subalgebra.fg_def.1
    (show (⊤ : Subalgebra R S).FG from (inferInstance : Algebra.FiniteType R S).out)
  refine ⟨htfinite.toFinset, ?_⟩
  simpa [htfinite.coe_toFinset] using htTop

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: if a finite adjoin stage is the whole
ambient algebra, then the canonical map from that stage to the ambient algebra is surjective. -/
private lemma adjoinStage_algebraMap_surjective_of_eq_top
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    Function.Surjective (algebraMap (Algebra.adjoin R (s : Set S)) S) := by
  intro y
  -- The stage equality says that every ambient element belongs to the chosen finite stage.
  refine ⟨⟨y, ?_⟩, rfl⟩
  simpa [hs] using (show y ∈ (⊤ : Subalgebra R S) from trivial)

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: the canonical map from a finite adjoin
stage equal to the whole ambient algebra is bijective. -/
private lemma adjoinStage_algebraMap_bijective_of_eq_top
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    Function.Bijective (algebraMap (Algebra.adjoin R (s : Set S)) S) := by
  constructor
  · intro x y hxy
    -- Elements of an adjoin stage are subtypes, so equality follows from equality in `S`.
    exact Subtype.ext hxy
  · -- Surjectivity is the terminal-stage membership statement isolated above.
    exact adjoinStage_algebraMap_surjective_of_eq_top (R := R) (S := S) s hs

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: a source map that is surjective on
stalks induces a bijection on residue fields at a lying-over pair of primes. -/
private lemma residueFieldMap_bijective_of_surjectiveOnStalks
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hsurj : (algebraMap A B).SurjectiveOnStalks) :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
  have hmap :
      Ideal.ResidueField.map p q (algebraMap A B) (Ideal.over_def q p) =
        algebraMap p.ResidueField q.ResidueField := by
    -- Compare the canonical residue-field map with the default algebra map on representatives.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext a
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap]
    calc
      algebraMap B q.ResidueField (algebraMap A B a) =
          algebraMap A q.ResidueField a := by
            rw [IsScalarTower.algebraMap_apply A B q.ResidueField a]
      _ = algebraMap p.ResidueField q.ResidueField (algebraMap A p.ResidueField a) := by
            rw [IsScalarTower.algebraMap_apply A p.ResidueField q.ResidueField a]
  -- The stalk-surjectivity owner supplies bijectivity for the canonical residue-field map.
  simpa [hmap] using hsurj.residueFieldMap_bijective p q (Ideal.over_def q p)

/-- Helper for Chap10 Lemma 10 116 3: residue-field transcendence degree is additive along a
finite-type tower of domain extensions. -/
theorem residueFieldTrdeg_tower_toNat_eq
    {R : Type u} {T : Type v} {U : Type v}
    [CommRing R] [CommRing T] [CommRing U] [IsDomain R] [IsDomain T] [IsDomain U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    [Algebra.FiniteType R T] [Algebra.FiniteType T U]
    (q : PrimeSpectrum U) :
    let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
        Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
  let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
  let pT : Ideal R := qT.asIdeal.under R
  let p : Ideal R := q.asIdeal.under R
  letI : pT.IsPrime := by
    dsimp [pT]
    infer_instance
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  have hp : pT = p := by
    -- Normalize the two contractions of the top prime to the same ideal of the base ring.
    simpa [pT, p, qT] using
      comap_under_eq_under_in_tower (R := R) (T := T) (U := U) q
  letI : qT.asIdeal.LiesOver pT := ⟨rfl⟩
  letI : q.asIdeal.LiesOver qT.asIdeal := ⟨rfl⟩
  letI : q.asIdeal.LiesOver pT := Ideal.LiesOver.trans q.asIdeal qT.asIdeal pT
  letI : q.asIdeal.LiesOver p := ⟨rfl⟩
  letI : Algebra.EssFiniteType pT.ResidueField qT.asIdeal.ResidueField := inferInstance
  letI : Algebra.EssFiniteType qT.asIdeal.ResidueField q.asIdeal.ResidueField := inferInstance
  have hbaseTop :
      Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg pT.ResidueField q.asIdeal.ResidueField) := by
    -- Equal base primes give the same residue-field source after substituting the contraction
    -- identity.
    exact
      (residueFieldTrdeg_toNat_eq_of_base_eq
        (R := R) (A := U) (p := pT) (p' := p) (P := q.asIdeal) hp).symm
  letI : FaithfulSMul pT.ResidueField qT.asIdeal.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective pT.ResidueField qT.asIdeal.ResidueField).mpr
      (RingHom.injective (algebraMap pT.ResidueField qT.asIdeal.ResidueField))
  letI : FaithfulSMul qT.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective qT.asIdeal.ResidueField q.asIdeal.ResidueField).mpr
      (RingHom.injective (algebraMap qT.asIdeal.ResidueField q.asIdeal.ResidueField))
  have hbase_lt :
      Algebra.trdeg pT.ResidueField qT.asIdeal.ResidueField < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field
      (K := pT.ResidueField) (L := qT.asIdeal.ResidueField)
  have htop_lt :
      Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field
      (K := qT.asIdeal.ResidueField) (L := q.asIdeal.ResidueField)
  have hsum :
      Algebra.trdeg pT.ResidueField qT.asIdeal.ResidueField +
          Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField =
        Algebra.trdeg pT.ResidueField q.asIdeal.ResidueField :=
    trdeg_add_eq
      (R := pT.ResidueField) (S := qT.asIdeal.ResidueField)
      (A := q.asIdeal.ResidueField)
  -- Convert cardinal additivity to the natural-number tower identity used by the dimension
  -- formula induction.
  calc
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
      = Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
          rfl
    _ = Cardinal.toNat (Algebra.trdeg pT.ResidueField q.asIdeal.ResidueField) := hbaseTop
    _ = Cardinal.toNat (Algebra.trdeg pT.ResidueField qT.asIdeal.ResidueField) +
          Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
            rw [← hsum, Cardinal.toNat_add hbase_lt htop_lt]
    _ = Cardinal.toNat
            (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
          Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
            rfl

/-- Helper for Chap10 Lemma 10 116 3: fraction-field transcendence degree is additive along a
finite-type tower of domain extensions. -/
theorem fractionRing_trdeg_tower_toNat_eq
    {R : Type u} {T : Type v} {U : Type v}
    [CommRing R] [CommRing T] [CommRing U] [IsDomain R] [IsDomain T] [IsDomain U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    [Algebra.FiniteType R T] [Algebra.FiniteType T U]
    [Algebra (FractionRing R) (FractionRing T)]
    [Algebra (FractionRing T) (FractionRing U)]
    [Algebra (FractionRing R) (FractionRing U)]
    [IsScalarTower R (FractionRing R) (FractionRing T)]
    [IsScalarTower T (FractionRing T) (FractionRing U)]
    [IsScalarTower (FractionRing R) (FractionRing T) (FractionRing U)] :
    Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing U)) =
      Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing T)) +
        Cardinal.toNat (Algebra.trdeg (FractionRing T) (FractionRing U)) := by
  letI : Algebra.EssFiniteType R (FractionRing T) := Algebra.EssFiniteType.comp R T (FractionRing T)
  letI : Algebra.EssFiniteType T (FractionRing U) := Algebra.EssFiniteType.comp T U (FractionRing U)
  letI : Algebra.EssFiniteType R (FractionRing U) := Algebra.EssFiniteType.comp R T (FractionRing U)
  letI : Algebra.EssFiniteType (FractionRing R) (FractionRing T) :=
    Algebra.EssFiniteType.of_comp R (FractionRing R) (FractionRing T)
  letI : Algebra.EssFiniteType (FractionRing T) (FractionRing U) :=
    Algebra.EssFiniteType.of_comp T (FractionRing T) (FractionRing U)
  letI : FaithfulSMul (FractionRing R) (FractionRing T) :=
    (faithfulSMul_iff_algebraMap_injective (FractionRing R) (FractionRing T)).mpr
      (RingHom.injective (algebraMap (FractionRing R) (FractionRing T)))
  letI : FaithfulSMul (FractionRing T) (FractionRing U) :=
    (faithfulSMul_iff_algebraMap_injective (FractionRing T) (FractionRing U)).mpr
      (RingHom.injective (algebraMap (FractionRing T) (FractionRing U)))
  have hRT_lt :
      Algebra.trdeg (FractionRing R) (FractionRing T) < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field (K := FractionRing R) (L := FractionRing T)
  have hTU_lt :
      Algebra.trdeg (FractionRing T) (FractionRing U) < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field (K := FractionRing T) (L := FractionRing U)
  -- Rewrite cardinal-valued tower additivity into the natural-number form used by finite stages.
  rw [← trdeg_add_eq (R := FractionRing R) (S := FractionRing T) (A := FractionRing U)]
  exact Cardinal.toNat_add hRT_lt hTU_lt

/-- Helper for Chap10 Lemma 10 116 3: every prime of a domain algebra over a field lies over
the zero prime of the base field. -/
private lemma fieldBase_liesOver_bot
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) :
    p.asIdeal.LiesOver (⊥ : Ideal k) := by
  -- The contraction of a prime ideal to a field is a proper ideal, hence the zero ideal.
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

/-- Helper for Chap10 Lemma 10 116 3: replacing a field by the residue field of its zero prime
does not change the natural-number transcendence degree of a compatible target field. -/
private theorem fieldBotResidueField_trdeg_toNat_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra ((⊥ : Ideal K).ResidueField) L]
    [IsScalarTower K ((⊥ : Ideal K).ResidueField) L] :
    Cardinal.toNat (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L) =
      Cardinal.toNat (Algebra.trdeg K L) := by
  -- Identify the zero-prime residue field with the fraction field of the base field.
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
    -- The base step of the tower is algebraic, so its transcendence degree vanishes.
    exact trdeg_eq_zero (R := K) (A := (⊥ : Ideal K).ResidueField)
  have hsum :=
    lift_trdeg_add_eq (R := K) (S := (⊥ : Ideal K).ResidueField) (A := L)
  have hlift_eq :
      Cardinal.lift.{u, v} (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L) =
        Cardinal.lift.{u, v} (Algebra.trdeg K L) := by
    -- Tower additivity now has a zero base term, leaving the target trdeg unchanged.
    simpa [hbase_zero] using hsum
  rw [← Cardinal.toNat_lift.{u, v} (Algebra.trdeg ((⊥ : Ideal K).ResidueField) L),
    ← Cardinal.toNat_lift.{u, v} (Algebra.trdeg K L), hlift_eq]

/-- Helper for Chap10 Lemma 10 116 3: the zero prime of a field has zero prime height as a
natural number. -/
private theorem fieldBot_primeHeight_toNat_eq_zero {k : Type u} [Field k] :
    ENat.toNat (Ideal.primeHeight (⊥ : Ideal k)) = 0 := by
  -- The zero ideal is the unique minimal prime in a field, so its height is zero.
  have hheight : Ideal.primeHeight (⊥ : Ideal k) = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  simpa [hheight]

/-- Helper for Chap10 Lemma 10 116 3: the contraction of a prime in a domain algebra over a
field has zero prime-height contribution. -/
private theorem fieldBase_primeHeight_under_toNat_eq_zero
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight (p.asIdeal.under k)) = 0 := by
  -- First identify the contraction with the zero ideal of the field.
  have hunder : p.asIdeal.under k = (⊥ : Ideal k) := by
    simpa using (fieldBase_liesOver_bot (k := k) (A := A) p).over.symm
  -- Rewriting the contraction leaves a concrete zero prime-height term.
  simpa [hunder] using fieldBot_primeHeight_toNat_eq_zero (k := k)

/-- Helper for Chap10 Lemma 10 116 3: after contracting a prime of a domain algebra to the base
field, the residue-field transcendence term is the ordinary base-field transcendence term. -/
private theorem fieldBase_residueFieldTrdeg_under_toNat_eq
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (p : PrimeSpectrum A) :
    Cardinal.toNat
        (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) := by
  -- Install the lying-over instance so the residue-field algebra over the zero contraction is
  -- available after rewriting the source prime to `⊥`.
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
  -- The zero-prime residue field of the base field has the same trdeg as the base field itself.
  exact hbase.trans
    (fieldBotResidueField_trdeg_toNat_eq (K := k) (L := p.asIdeal.ResidueField))

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: a finite module with zero-dimensional
support over a Noetherian local ring is Cohen-Macaulay. -/
private theorem cohenMacaulay_of_supportDimZero_local
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdim : Module.supportDim A N = 0) : Module.CohenMacaulay A N := by
  -- In support dimension zero, the general depth bound forces depth to be zero as well.
  refine Module.CohenMacaulay.mk ?_
  let _ : Nontrivial N := by
    simp [← Module.supportDim_ne_bot_iff_nontrivial A, hdim]
  have hdepth_le : WithBot.some (moduleDepth A N : ℕ∞) ≤ 0 := by
    rw [← hdim]
    exact depth_le_supportDim
  have hdepth_eq : moduleDepth A N = 0 := by
    simpa using hdepth_le
  simpa [hdepth_eq] using hdim

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: fields are universally catenary. -/
private lemma field_universallyCatenaryRing {k : Type u} [Field k] :
    UniversallyCatenaryRing.{u, v} k := by
  have hCM : CohenMacaulayRing k := by
    -- Prime localizations of a field are fields, hence have zero support dimension as
    -- self-modules and are Cohen-Macaulay by the zero-dimensional local criterion.
    refine { toIsNoetherian := inferInstance, toLocallyCohenMacaulay := ?_ }
    refine { toFinite := inferInstance, localizedModule_cohenMacaulay := ?_ }
    intro p
    apply cohenMacaulay_of_supportDimZero_local
    rw [Module.supportDim_self_eq_ringKrullDim]
    have hpbot : p.asIdeal = (⊥ : Ideal k) := by
      rcases IsSimpleOrder.eq_bot_or_eq_top p.asIdeal with hbot | htop
      · exact hbot
      · exact (p.isPrime.ne_top htop).elim
    have hpmin : p.asIdeal ∈ minimalPrimes k := by
      rw [IsDomain.minimalPrimes_eq_singleton_bot]
      simp [hpbot]
    let pmin : minimalPrimes k := ⟨p.asIdeal, hpmin⟩
    have hfield : IsField (Localization.AtPrime p.asIdeal) := by
      simpa [pmin] using isField_localizationAtPrime_of_minimalPrime pmin
    letI : Field (Localization.AtPrime p.asIdeal) := hfield.toField
    exact ringKrullDim_eq_zero_of_field (Localization.AtPrime p.asIdeal)
  -- The earlier Cohen-Macaulay bridge supplies universal catenarity at the universe level
  -- required by the dimension formula.
  exact universallyCatenaryRing_of_cohenMacaulayRing (R := k) hCM

/-- Helper for Chap10 Lemma 10 113 1 DimensionEquality: universal catenarity upgrades the
finite-type dimension inequality for domains to the expected equality. -/
private theorem finiteType_primeHeightResidueFieldTrdeg_toNat_eq_fractionRing_trdeg_of_universallyCatenary
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] [UniversallyCatenaryRing.{u, v} R]
    [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)]
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  -- Route correction: this split file has the field-base consumers but not the polynomial-fiber
  -- transport and finite-adjoin equality owner stack. Use the canonical prime-spectrum owner from
  -- the aggregate item, then unfold this file's local generic-term abbreviation.
  simpa [Algebra.fractionRingTrdeg] using
    primeHeight_add_residueFieldTrdeg_eq_primeHeight_under_add_trdeg_of_universallyCatenary
      (R := R) (S := S) hinj q

/-- Helper for Chap10 Lemma 10 116 3: the finite-type equality theorem gives the field-base
height plus residue-field transcendence bound against the concrete fraction-field trdeg. -/
private theorem fieldBase_primeHeight_add_residueFieldTrdeg_toNat_le_fractionRing_trdeg
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Algebra (FractionRing k) (FractionRing A)]
    [IsScalarTower k (FractionRing k) (FractionRing A)] (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) ≤
      Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
  -- Derive the inequality from the isolated equality owner, avoiding the unstable imported
  -- inequality file while preserving the same field-base normalization.
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
      finiteType_primeHeightResidueFieldTrdeg_toNat_eq_fractionRing_trdeg_of_universallyCatenary
        (R := k) (S := A) hinj p
  have hheight := fieldBase_primeHeight_under_toNat_eq_zero (k := k) (A := A) p
  have hresidue := fieldBase_residueFieldTrdeg_under_toNat_eq (k := k) (A := A) p
  have heq :
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
    -- Normalize the contracted field prime to zero height and the residue-field source to `k`.
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
  exact le_of_eq heq

/-- Helper for Chap10 Lemma 10 116 3: field-base specialization of the equality case of
Lemma 10.113.1, normalized to the concrete fraction-field transcendence term. -/
theorem fieldBase_primeHeight_add_residueFieldTrdeg_toNat_eq_fractionRing_trdeg
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Algebra (FractionRing k) (FractionRing A)]
    [IsScalarTower k (FractionRing k) (FractionRing A)] (p : PrimeSpectrum A) :
    ENat.toNat (Ideal.primeHeight p.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k p.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
  -- The field-base transports are now separated from the remaining theorem-sized equality owner.
  have hgeneric :
      ENat.toNat (Ideal.primeHeight p.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (p.asIdeal.under k).ResidueField p.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (p.asIdeal.under k)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing k) (FractionRing A)) := by
    -- Replace the earlier direct reverse-inequality attempt by the universal-catenary owner.
    have hinj : Function.Injective (algebraMap k A) :=
      FaithfulSMul.algebraMap_injective k A
    letI : UniversallyCatenaryRing.{u, v} k := field_universallyCatenaryRing (k := k)
    exact
      finiteType_primeHeightResidueFieldTrdeg_toNat_eq_fractionRing_trdeg_of_universallyCatenary
        (R := k) (S := A) hinj p
  have hheight := fieldBase_primeHeight_under_toNat_eq_zero (k := k) (A := A) p
  have hresidue := fieldBase_residueFieldTrdeg_under_toNat_eq (k := k) (A := A) p
  -- With the generic equality in hand, the field contraction contributes zero height and its
  -- residue-field source is the base field itself.
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
