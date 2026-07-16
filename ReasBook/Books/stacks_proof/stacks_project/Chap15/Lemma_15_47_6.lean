import Mathlib
import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap10.Lemma_10_45_3
import stacks_proof.stacks_project.Chap10.Lemma_10_159_3
import stacks_proof.stacks_project.Chap15.Lemma_15_47_3
import stacks_proof.stacks_project.Chap15.Lemma_15_47_4
import stacks_proof.stacks_project.Chap15.Lemma_15_47_5
import stacks_proof.stacks_project.Chap15.Definition_15_47_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Helper for Lemma 15.47.6: a domain that is `J-1` is automatically `J-0`. -/
lemma isJ0Ring_of_isJ1Ring_domain
    (A : Type _) [CommRing A] [IsDomain A] [IsJ1Ring A] :
    IsJ0Ring A := by
  -- Use the open regular locus itself as the `J-0` witness; the generic point of a domain is
  -- regular because its local ring is a field.
  refine (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).2 ?_
  refine
    ⟨PrimeSpectrum.regularLocus A, (isJ1Ring_iff_regularLocus_isOpen).1 inferInstance, ?_,
      subset_rfl⟩
  refine ⟨⟨⊥, inferInstance⟩, ?_⟩
  change IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A))
  letI : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization ((⊥ : Ideal A).primeCompl)
        (Localization.AtPrime (⊥ : Ideal A)))
  letI : IsRegularLocalRing (FractionRing A) := by infer_instance
  let e : FractionRing A ≃ₐ[A] Localization.AtPrime (⊥ : Ideal A) :=
    FractionRing.algEquiv A (Localization.AtPrime (⊥ : Ideal A))
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- Helper for Lemma 15.47.6: the residue field of a prime quotient is the quotient's canonical
fraction field. -/
lemma quotient_residueField_isFractionRing
    {S : Type _} [CommRing S] (q : Ideal S) [q.IsPrime] :
    IsFractionRing (S ⧸ q) q.ResidueField := by
  -- This is the owner-level fraction-field instance attached to a prime quotient.
  infer_instance

/-- Helper for Lemma 15.47.6: the residue field at the generic point of a domain is its fraction
field. -/
lemma genericPoint_residueField_isFractionRing
    (A : Type _) [CommRing A] [IsDomain A] :
    let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
    IsFractionRing A q.asIdeal.ResidueField := by
  let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let e : A ≃+* A ⧸ (⊥ : Ideal A) :=
    RingEquiv.ofBijective (Ideal.Quotient.mk (⊥ : Ideal A))
      ((Ideal.Quotient.mk_bijective_iff_eq_bot (I := (⊥ : Ideal A))).2 rfl)
  -- Transport the quotient residue-field instance across the canonical `A ≃ A ⧸ (0)`.
  refine IsFractionRing.of_ringEquiv_left e ?_
  intro x
  rfl

/-- Helper for Lemma 15.47.6: an algebra equivalence with a `Type v` field makes the source field
`v`-small. -/
lemma field_small_of_algEquiv
    {k : Type u} [Field k] {K : Type _} [Field K] {L : Type v} [Field L]
    [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L) :
    Small.{v} K := by
  -- Transport smallness back along the inverse surjection `L → K`.
  exact small_of_surjective e.symm.surjective

/-- Helper for Lemma 15.47.6: an injective algebra map into a `Type v` field makes the source
ring `v`-small. -/
lemma small_of_injective_algebraMap_to_field
    {A : Type _} [CommRing A] {L : Type v} [Field L] [Algebra A L]
    (hinj : Function.Injective (algebraMap A L)) :
    Small.{v} A := by
  -- Any ring that injects into a `Type v` field can be shrunk to universe `v`.
  let _ : Small.{v} L := small_self L
  exact small_of_injective hinj

/-- Helper for Lemma 15.47.6: once a finite domain model with fraction field `L` is `v`-small,
its canonical shrink transports all clause `(4)` witness data into universe `Type v`. -/
lemma exists_shrunk_fraction_ring_model
    {A : Type _} [CommRing A] [Algebra R A] [Module.Finite R A] [IsDomain A]
    {L : Type v} [Field L] [Algebra R L] [Algebra A L] [IsScalarTower R A L]
    [IsFractionRing A L] [Small.{v} A] :
    ∃ (A' : Type v) (_ : CommRing A') (_ : Algebra R A') (_ : Module.Finite R A')
      (_ : IsDomain A') (_ : Algebra A' L) (_ : IsScalarTower R A' L)
      (_ : IsFractionRing A' L),
      True := by
  let e : Shrink.{v} A ≃ₐ[R] A := Shrink.algEquiv R A
  letI : Algebra R (Shrink.{v} A) := inferInstance
  letI : Module.Finite R (Shrink.{v} A) := Module.Finite.equiv (Shrink.linearEquiv R A).symm
  letI : IsDomain (Shrink.{v} A) := Function.Injective.isDomain e.toRingHom e.injective
  letI : Algebra (Shrink.{v} A) L := RingHom.toAlgebra ((algebraMap A L).comp e.toRingHom)
  -- Transport the scalar tower and fraction-ring structure once across `Shrink.algEquiv`.
  letI : IsScalarTower R (Shrink.{v} A) L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    calc
      (algebraMap R L) x = (algebraMap A L) ((algebraMap R A) x) := by
        symm
        simpa [RingHom.comp_apply] using
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R A L) x).symm
      _ = (algebraMap A L) (e ((algebraMap R (Shrink.{v} A)) x)) := by
        rw [e.commutes]
      _ = ((algebraMap (Shrink.{v} A) L).comp (algebraMap R (Shrink.{v} A))) x := by
        rfl
  letI : IsFractionRing (Shrink.{v} A) L := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap A L (e x) = algebraMap A L (e x)
    rfl
  exact ⟨Shrink.{v} A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, trivial⟩

/-- Helper for Lemma 15.47.6: a finite purely inseparable residue-field extension admits a finite
`R`-algebra domain model whose fraction field is the target field. -/
lemma exists_finite_domain_model_of_purelyInseparable_residueField_extension
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Algebra R L] [IsScalarTower R p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L] :
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower R A L)
      (_ : IsFractionRing A L),
      True := by
  -- Follow Lemma `10.159.3`: realize `L / κ(p)` by a finite free `R`-algebra and then pass to
  -- the quotient by the extended prime.
  obtain ⟨S, hSComm, hRS, hSfree, hSfinite, hmodel⟩ :=
    exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv
      (p := p) L
  letI : CommRing S := hSComm
  letI : Algebra R S := hRS
  letI : Module.Free R S := hSfree
  letI : Module.Finite R S := hSfinite
  let q : Ideal S := p.map (algebraMap R S)
  rcases hmodel with ⟨hqprime, hqover, ⟨eκL⟩⟩
  letI : q.IsPrime := hqprime
  letI : Algebra R (S ⧸ q) := by infer_instance
  letI : Module.Finite R (S ⧸ q) := by infer_instance
  letI : IsDomain (S ⧸ q) := Ideal.Quotient.isDomain q
  letI : Algebra (S ⧸ q) q.ResidueField := inferInstance
  letI : IsFractionRing (S ⧸ q) q.ResidueField :=
    quotient_residueField_isFractionRing q
  letI : Algebra q.ResidueField L := eκL.toRingHom.toAlgebra
  letI : Algebra (S ⧸ q) L :=
    RingHom.toAlgebra ((eκL : q.ResidueField →+* L).comp (algebraMap (S ⧸ q) q.ResidueField))
  letI : IsScalarTower (S ⧸ q) q.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R p.ResidueField q.ResidueField := by infer_instance
  letI : IsScalarTower R (S ⧸ q) q.ResidueField := by infer_instance
  letI : IsScalarTower R (S ⧸ q) L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    calc
      (algebraMap R L) x = (algebraMap p.ResidueField L) ((algebraMap R p.ResidueField) x) := by
        symm
        simpa [RingHom.comp_apply] using
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R p.ResidueField L) x).symm
      _ = eκL ((algebraMap p.ResidueField q.ResidueField) ((algebraMap R p.ResidueField) x)) := by
        symm
        exact eκL.commutes ((algebraMap R p.ResidueField) x)
      _ = eκL ((algebraMap (S ⧸ q) q.ResidueField) ((algebraMap R (S ⧸ q)) x)) := by
        have hsame :
            (algebraMap p.ResidueField q.ResidueField) ((algebraMap R p.ResidueField) x) =
              (algebraMap (S ⧸ q) q.ResidueField) ((algebraMap R (S ⧸ q)) x) := by
          calc
            (algebraMap p.ResidueField q.ResidueField) ((algebraMap R p.ResidueField) x) =
                (algebraMap R q.ResidueField) x := by
              symm
              exact
                DFunLike.congr_fun (IsScalarTower.algebraMap_eq R p.ResidueField q.ResidueField) x
            _ = (algebraMap (S ⧸ q) q.ResidueField) ((algebraMap R (S ⧸ q)) x) := by
              exact
                DFunLike.congr_fun (IsScalarTower.algebraMap_eq R (S ⧸ q) q.ResidueField) x
        rw [hsame]
      _ = ((algebraMap (S ⧸ q) L).comp (algebraMap R (S ⧸ q))) x := by
        rfl
  letI : FaithfulSMul (S ⧸ q) L :=
    FaithfulSMul.of_field_isFractionRing
      (R := S ⧸ q) (S := L) (K := q.ResidueField) (L := L)
  letI : IsFractionRing (S ⧸ q) L := by
    -- Re-express each `z : L` through `eκL.symm z` in the canonical residue-field fraction ring.
    refine IsFractionRing.of_field (S ⧸ q) L ?_
    intro z
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (S ⧸ q) (eκL.symm z)
    refine ⟨x, y, ?_⟩
    have hxyL := congrArg eκL hxy
    simpa using hxyL.symm
  have hquot_inj : Function.Injective (algebraMap (S ⧸ q) L) :=
    IsFractionRing.injective (S ⧸ q) L
  letI : Small.{v} (S ⧸ q) :=
    small_of_injective_algebraMap_to_field (A := S ⧸ q) (L := L) hquot_inj
  -- Route correction: the source-faithful witness is already `S ⧸ q`; the only remaining Lean
  -- work is to shrink this quotient from `Type (max u v)` to `Type v` and transport its algebra,
  -- domain, finite, and fraction-ring structures across `Shrink.algEquiv`.
  let _ := hqover
  exact exists_shrunk_fraction_ring_model (R := R) (A := S ⧸ q) (L := L)

/-- Helper for Lemma 15.47.6: for the kernel prime `p = ker(R → A)` and the generic point
`q = (0) ∈ Spec A`, the canonical map on residue fields gives the scalar tower
`R → κ(p) → Frac(A)`. -/
private theorem kernel_generic_point_residueField_isScalarTower
    (A : Type v) [CommRing A] [Algebra R A] [IsDomain A] :
    let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
    IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  -- The residue-field map is defined so that it agrees with the composite `R → A → κ(q)`.
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext x
  simpa [p] using
    (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R A) rfl x).symm

/-- Helper for Lemma 15.47.6: the source proof first applies Lemma `10.45.3` to the generic
residue-field extension attached to the kernel prime of `R → A`. -/
private theorem exists_purelyInseparable_lift_over_generic_point
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A] :
    let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
    ∃ (L : Type v) (_ : Field L) (_ : Algebra p.asIdeal.ResidueField L)
      (K' : Type v) (_ : Field K') (_ : Algebra p.asIdeal.ResidueField K')
      (_ : Algebra q.asIdeal.ResidueField K') (_ : Algebra L K')
      (_ : IsScalarTower p.asIdeal.ResidueField q.asIdeal.ResidueField K')
      (_ : IsScalarTower p.asIdeal.ResidueField L K')
      (_ : FiniteDimensional q.asIdeal.ResidueField K')
      (_ : IsPurelyInseparable q.asIdeal.ResidueField K')
      (_ : FiniteDimensional p.asIdeal.ResidueField L)
      (_ : IsPurelyInseparable p.asIdeal.ResidueField L),
      (IsScalarTower.toAlgHom p.asIdeal.ResidueField L K').fieldRange ⊔
        (IsScalarTower.toAlgHom p.asIdeal.ResidueField q.asIdeal.ResidueField K').fieldRange = ⊤ := by
  let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  -- The generic point of a domain provides the fraction-field side of the source tower.
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  let _ : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    kernel_generic_point_residueField_isScalarTower (R := R) A
  let _ : Algebra.EssFiniteType p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    -- Build the residue-field extension in the same algebra structure used by the tensor route.
    let _ : Algebra.EssFiniteType A q.asIdeal.ResidueField := inferInstance
    let _ : Algebra.EssFiniteType R q.asIdeal.ResidueField :=
      Algebra.EssFiniteType.comp R A q.asIdeal.ResidueField
    exact Algebra.EssFiniteType.of_comp R p.asIdeal.ResidueField q.asIdeal.ResidueField
  -- Lemma `10.45.3` packages the purely inseparable/separable lift and the compositum equality.
  exact
    exists_purelyInseparable_lift_with_compositum_top
      (k := p.asIdeal.ResidueField) (K := q.asIdeal.ResidueField)

/-- Helper for Lemma 15.47.6: the same generic-point residue-field extension also admits the
source-faithful purely inseparable/separable lift `κ(p) ⊂ L ⊂ K'`. -/
private theorem exists_separable_over_lift_over_generic_point
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A] :
    let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
    ∃ (L : Type v) (_ : Field L) (_ : Algebra p.asIdeal.ResidueField L)
      (K' : Type v) (_ : Field K') (_ : Algebra p.asIdeal.ResidueField K')
      (_ : Algebra q.asIdeal.ResidueField K') (_ : Algebra L K')
      (_ : IsScalarTower p.asIdeal.ResidueField q.asIdeal.ResidueField K')
      (_ : IsScalarTower p.asIdeal.ResidueField L K')
      (_ : FiniteDimensional q.asIdeal.ResidueField K')
      (_ : IsPurelyInseparable q.asIdeal.ResidueField K')
      (_ : FiniteDimensional p.asIdeal.ResidueField L)
      (_ : IsPurelyInseparable p.asIdeal.ResidueField L),
      Algebra.IsSeparableOver L K' := by
  let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  -- Reuse the generic-point scalar tower so Lemma `10.45.3 (1)` applies in the textbook tower.
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  let _ : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    kernel_generic_point_residueField_isScalarTower (R := R) A
  let _ : Algebra.EssFiniteType p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    -- The residue field at the generic point is essentially of finite type over `κ(p)` because
    -- it is obtained from the finite type `R`-algebra `A` by passing to a prime quotient and then
    -- localizing.
    let _ : Algebra.EssFiniteType A q.asIdeal.ResidueField := inferInstance
    let _ : Algebra.EssFiniteType R q.asIdeal.ResidueField :=
      Algebra.EssFiniteType.comp R A q.asIdeal.ResidueField
    exact Algebra.EssFiniteType.of_comp R p.asIdeal.ResidueField q.asIdeal.ResidueField
  -- This is exactly the source-faithful lift `κ(p) ⊂ L ⊂ K'` with `K' / L` separable.
  exact
    exists_purelyInseparable_lift_with_separable_over
      (k := p.asIdeal.ResidueField) (K := q.asIdeal.ResidueField)

/-- Helper for Lemma 15.47.6: if `K' / K` is purely inseparable and `K' / L` is separable, then
the images of `L` and `K` generate all of `K'`. -/
private theorem fieldRange_sup_eq_top_of_purelyInseparable_and_separable
    {k : Type u} {K : Type v} {L : Type v} {K' : Type v}
    [Field k] [Field K] [Field L] [Field K']
    [Algebra k K] [Algebra k L] [Algebra k K']
    [Algebra K K'] [Algebra L K']
    [IsScalarTower k K K'] [IsScalarTower k L K']
    [IsPurelyInseparable K K'] [Algebra.IsSeparable L K'] :
    (IsScalarTower.toAlgHom k L K').fieldRange ⊔
      (IsScalarTower.toAlgHom k K K').fieldRange = ⊤ := by
  let lRange : IntermediateField k K' := (IsScalarTower.toAlgHom k L K').fieldRange
  let kRange : IntermediateField k K' := (IsScalarTower.toAlgHom k K K').fieldRange
  let S : IntermediateField k K' := lRange ⊔ kRange
  let eL : L ≃ₐ[k] lRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k L K')
  let eK' : K' ≃+* K' := RingEquiv.refl K'
  have hcomp :
      RingHom.comp (algebraMap lRange K') eL.toRingEquiv =
        RingHom.comp eK' (algebraMap L K') := by
    -- The transported base field `lRange` acts on `K'` through the same embedding `L → K'`.
    ext x
    rfl
  have hsepRange : Algebra.IsSeparable lRange K' :=
    Algebra.IsSeparable.of_equiv_equiv eL.toRingEquiv eK' hcomp
  letI : Algebra.IsSeparable lRange K' := hsepRange
  letI : Algebra lRange S :=
    RingHom.toAlgebra (IntermediateField.inclusion (le_sup_left : lRange ≤ S))
  letI : IsScalarTower lRange S K' := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    rfl
  have hsepSup : Algebra.IsSeparable S K' :=
    Algebra.isSeparable_tower_top_of_isSeparable lRange S K'
  letI : Algebra.IsSeparable S K' := hsepSup
  let eK : K ≃ₐ[k] kRange :=
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k K K')
  letI : Algebra K S :=
    RingHom.toAlgebra
      ((IntermediateField.inclusion (le_sup_right : kRange ≤ S)).comp eK.toAlgHom)
  letI : IsScalarTower K S K' := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    rfl
  letI : IsPurelyInseparable S K' := inferInstance
  have hsurj : Function.Surjective (algebraMap S K') :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable S K'
  -- Once the top extension is both separable and purely inseparable, it must be trivial.
  ext x
  constructor
  · intro _
    trivial
  · intro _
    rcases hsurj x with ⟨y, rfl⟩
    exact y.2

/-- Helper for Lemma 15.47.6: clause `(4)` reduces the finite-type domain case to the textbook
tensor-image model over the chosen purely inseparable residue-field witness. -/
private theorem isJ0Ring_of_finiteType_domain_from_clause4
    (h4 :
      ∀ (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
        [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
        let _ : Algebra R L :=
          RingHom.toAlgebra
            ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
        let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
        ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
          (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower R A L)
          (_ : IsFractionRing A L),
          IsJ0Ring A)
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A] :
    IsJ0Ring A := by
  let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  letI : p.asIdeal.IsPrime := by infer_instance
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  -- Route correction: lock in the source tower `κ(p) ⊂ L ⊂ K'` before introducing the tensor
  -- image ring. This avoids drifting into an unrelated descent argument.
  obtain ⟨L, hLField, hκL, K', hK'Field, hκK', hFracK', hLK', htowerFrac, htowerL,
      hfdK', hpureK', hfdL, hpureL, hsep⟩ :=
    exists_separable_over_lift_over_generic_point (R := R) (A := A)
  letI : Field L := hLField
  letI : Algebra p.asIdeal.ResidueField L := hκL
  letI : Field K' := hK'Field
  letI : Algebra p.asIdeal.ResidueField K' := hκK'
  letI : Algebra q.asIdeal.ResidueField K' := hFracK'
  letI : Algebra L K' := hLK'
  letI : IsScalarTower p.asIdeal.ResidueField q.asIdeal.ResidueField K' := htowerFrac
  letI : IsScalarTower p.asIdeal.ResidueField L K' := htowerL
  letI : FiniteDimensional q.asIdeal.ResidueField K' := hfdK'
  letI : IsPurelyInseparable q.asIdeal.ResidueField K' := hpureK'
  letI : FiniteDimensional p.asIdeal.ResidueField L := hfdL
  letI : IsPurelyInseparable p.asIdeal.ResidueField L := hpureL
  letI : Algebra R L :=
    RingHom.toAlgebra
      ((algebraMap p.asIdeal.ResidueField L).comp (algebraMap R p.asIdeal.ResidueField))
  letI : IsScalarTower R p.asIdeal.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  -- Clause `(4)` now supplies the source-faithful `J-0` domain model `R₀ ⊂ L`.
  obtain ⟨R₀, hR₀Comm, hRR₀, hR₀finite, hR₀dom, hR₀L, htowerR₀L, hfracR₀, hR₀J0⟩ :=
    h4 p.asIdeal L
  letI : CommRing R₀ := hR₀Comm
  letI : Algebra R R₀ := hRR₀
  letI : Module.Finite R R₀ := hR₀finite
  letI : IsDomain R₀ := hR₀dom
  letI : Algebra R₀ L := hR₀L
  letI : IsScalarTower R R₀ L := htowerR₀L
  letI : IsFractionRing R₀ L := hfracR₀
  letI : IsJ0Ring R₀ := hR₀J0
  let _ : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    kernel_generic_point_residueField_isScalarTower (R := R) A
  letI : IsFractionRing A q.asIdeal.ResidueField :=
    genericPoint_residueField_isFractionRing A
  have hsup :
      (IsScalarTower.toAlgHom p.asIdeal.ResidueField L K').fieldRange ⊔
        (IsScalarTower.toAlgHom p.asIdeal.ResidueField q.asIdeal.ResidueField K').fieldRange =
          ⊤ := by
    -- The chosen lift is now the separable one from the source proof, so the compositum-top
    -- statement comes from the previously isolated purely-inseparable/separable field lemma.
    exact
      fieldRange_sup_eq_top_of_purelyInseparable_and_separable
        (k := p.asIdeal.ResidueField) (K := q.asIdeal.ResidueField) (L := L) (K' := K')
  -- Route correction: name the canonical tensor-image map before asking for the remaining owner
  -- packaging. This keeps the source proof's ring `S'` fixed throughout the next plan.
  let leftMap : A →ₐ[R] K' :=
    { toRingHom := (algebraMap q.asIdeal.ResidueField K').comp (algebraMap A q.asIdeal.ResidueField)
      commutes' := by
        intro r
        change (algebraMap q.asIdeal.ResidueField K')
            ((algebraMap A q.asIdeal.ResidueField) ((algebraMap R A) r)) =
          algebraMap R K' r
        rw [← IsScalarTower.algebraMap_eq R A q.asIdeal.ResidueField]
        rw [← IsScalarTower.algebraMap_eq R q.asIdeal.ResidueField K'] }
  let rightMap : R₀ →ₐ[R] K' :=
    { toRingHom := (algebraMap L K').comp (algebraMap R₀ L)
      commutes' := by
        intro r
        change (algebraMap L K') ((algebraMap R₀ L) ((algebraMap R R₀) r)) =
          algebraMap R K' r
        rw [← IsScalarTower.algebraMap_eq R R₀ L]
        rw [← IsScalarTower.algebraMap_eq R L K'] }
  let φR : A ⊗[R] R₀ →ₐ[R] K' := Algebra.TensorProduct.productMap leftMap rightMap
  -- TODO: package `B := φR.range` with its `A`- and `R₀`-algebra structures, use `hsup` to show
  -- `FractionRing B ≃ K'`, transport `hsep : Algebra.IsSeparableOver L K'` into the exact
  -- wrapper `Algebra.fractionRingIsSeparableOver (R := R₀) (S := B) _`, and then apply
  -- Lemmas `15.47.5` and `15.47.4`.
  let _ := hsup
  let _ := φR
  let _ := hsep
  sorry

/- Domain-style sampling:
- primary domain: the chapter's `J-0`/`J-1`/`J-2` hierarchy for Noetherian rings and its
  fraction-field / residue-field bridge criteria;
- sampled owner declarations of the same kind:
  `IsJ0Ring`,
  `IsJ1Ring`,
  `IsJ2Ring`,
  `isJ2Ring_iff_forall_finiteType_isJ1`;
- best owner abstraction: this file is `source-facing`, but its public API should still be
  organized around the existing owners `IsJ0Ring`, `IsJ1Ring`, and `IsJ2Ring` from
  `Definition_15_47_1`, while the residue-field clause should use the canonical prime-ideal owner
  `p : Ideal R` with `[p.IsPrime]` and `p.ResidueField` rather than a `PrimeSpectrum` wrapper;
- primitive vs. derived: the primitive data in conditions `(2)` and `(3)` are the finite type /
  finite `R`-algebra structures together with the domain hypothesis in `(2)`. Noetherianity of
  those target rings is derived from the owner conclusions `IsJ0Ring A` and `IsJ1Ring A`, so it
  should not remain primitive public data in this `TFAE` statement. Likewise, the prime-spectrum
  presentation of condition `(4)` is derived from the prime ideal and should not stay as the
  algebra-facing owner surface. The `R`-algebra structure on a residue-field extension
  `L / p.ResidueField` is derived internal data coming from `R → p.ResidueField → L`, so it should
  not be exposed as a primitive binder in the public clause. For the witness algebra in `(4)`,
  the source-faithful primitive witness data are that `A` is a finite `R`-algebra domain with
  `IsFractionRing A L` and `IsJ0Ring A`; the domain hypothesis is not derivable from
  `IsFractionRing A L` in mathlib, so it must remain explicit in the public clause.
-/

-- Proof sketch: `(1) → (2)` and `(1) → (3)` follow by applying the defining `J-2` property to
-- finite type and finite `R`-algebras, with the domain case giving `J-0` because a domain that is
-- `J-1` is `J-0`. For `(2) → (1)`, apply Lemma `15.47.3` to each prime quotient of a finite type
-- `R`-algebra. The implication `(3) → (4)` is obtained by applying `(3)` to the finite
-- `R`-algebra whose fraction field is the given purely inseparable residue-field extension, while
-- `(4) → (2)` follows by replacing the fraction field of a finite type domain algebra by a finite
-- purely inseparable/separable tower as in Lemma `10.42.4`, choosing a `J-0` model over the
-- residue field, and descending `J-0` back along Lemmas `15.47.5` and `15.47.4`.
/-- Lemma 15.47.6: for a Noetherian ring `R`, the following are equivalent: `R` is `J-2`; every
finite type `R`-algebra that is a domain is `J-0`; every finite `R`-algebra is `J-1`; and for
every prime `p` and every finite purely inseparable extension `L / κ(p)`, there exists a finite
`R`-algebra domain that is `J-0` and has fraction field `L`. -/
@[stacks 07PC]
theorem isJ2Ring_tfae_finiteType_domain_isJ0_finite_algebra_isJ1_purelyInseparable_residueField_extension
    : List.TFAE
        [ IsJ2Ring.{u, v} R,
          ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A],
            IsJ0Ring A,
          ∀ (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A],
            IsJ1Ring A,
          ∀ (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
            [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
            let _ : Algebra R L :=
              RingHom.toAlgebra
                ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
            let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
            ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
              (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower R A L)
              (_ : IsFractionRing A L),
              IsJ0Ring A
        ] := by
  have hiff :
      IsJ2Ring.{u, v} R ↔
        ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A], IsJ1Ring A :=
    isJ2Ring_iff_forall_finiteType_isJ1 (R := R)
  tfae_have 1 → 2 := by
    intro h1 A _ _ _ _
    -- Clause `(1)` says every finite type algebra is `J-1`; for domains, the generic point then
    -- turns this open regular locus into a nonempty regular open.
    have hJ1_all := hiff.mp h1
    letI : IsJ1Ring A := hJ1_all A
    exact isJ0Ring_of_isJ1Ring_domain A
  tfae_have 2 → 1 := by
    intro h2
    -- By Lemma `15.47.3`, it suffices to prove that every prime quotient of a finite type
    -- `R`-algebra is `J-0`.
    rw [hiff]
    intro A _ _ _
    letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
    exact
      _root_.isJ1Ring_of_isJ0Ring_quotient_by_prime
        (R := A) fun p ↦ by
      letI : Algebra R (A ⧸ p.asIdeal) := by infer_instance
      letI : Algebra.FiniteType R (A ⧸ p.asIdeal) := by infer_instance
      letI : IsDomain (A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
      exact h2 (A ⧸ p.asIdeal)
  tfae_have 1 → 3 := by
    intro h1 A _ _ _
    -- A finite `R`-algebra is finite type, so clause `(1)` applies directly.
    have hJ1_all := hiff.mp h1
    exact hJ1_all A
  tfae_have 3 → 4 := by
    intro h3 p hp L hL hRL hfd hpi
    -- First build the finite domain model of the residue-field extension, then apply clause `(3)`
    -- to obtain `J-1`, and finally use the domain bridge `J-1 → J-0`.
    let _ : Algebra R L :=
      RingHom.toAlgebra ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
    let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨A, hAComm, hRA, hAfinite, hAdom, hAL, htower, hfrac, -⟩ :=
      exists_finite_domain_model_of_purelyInseparable_residueField_extension
        (R := R) p L
    letI : CommRing A := hAComm
    letI : Algebra R A := hRA
    letI : Module.Finite R A := hAfinite
    letI : IsDomain A := hAdom
    letI : Algebra A L := hAL
    letI : IsScalarTower R A L := htower
    letI : IsFractionRing A L := hfrac
    have hJ1A : IsJ1Ring A := h3 A
    letI : IsJ1Ring A := hJ1A
    exact ⟨A, hAComm, hRA, hAfinite, hAdom, hAL, htower, hfrac,
      isJ0Ring_of_isJ1Ring_domain A⟩
  tfae_have 4 → 2 := by
    intro h4 A _ _ _ _
    -- Route correction: the only remaining gap is the tensor-image packaging inside the helper;
    -- the source-faithful field tower and clause `(4)` witness are already fixed.
    exact isJ0Ring_of_finiteType_domain_from_clause4 (R := R) h4 A
  tfae_finish

end
