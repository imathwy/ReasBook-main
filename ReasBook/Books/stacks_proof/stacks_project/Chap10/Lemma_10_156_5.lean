import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_46_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing
open Algebra.TensorProduct

universe u v w

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [Algebra A B] [Algebra A C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [Algebra.IsIntegral A C]

local notation "TensorD" => B ⊗[A] C
local notation "ClosedFiberA" => ResidueField A ⊗[A] C

/-- Helper for Lemma 10.156.5: a local ring integral over a field has only one prime ideal. -/
lemma subsingleton_primeSpectrum_of_isLocalRing_of_integral_over_field
    {K : Type*} {R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [Algebra.IsIntegral K R] :
    Subsingleton (PrimeSpectrum R) := by
  refine ⟨fun p q ↦ ?_⟩
  -- Every prime contracts to the zero maximal ideal of the field, so it is maximal upstairs.
  have hp_max : p.asIdeal.IsMaximal := by
    have hp_comap_max : (Ideal.comap (algebraMap K R) p.asIdeal).IsMaximal := by
      have hp_comap_bot :
          Ideal.comap (algebraMap K R) p.asIdeal = (⊥ : Ideal K) := by
        exact Ideal.eq_bot_of_prime (I := Ideal.comap (algebraMap K R) p.asIdeal)
      simpa [hp_comap_bot] using (inferInstance : (⊥ : Ideal K).IsMaximal)
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p.asIdeal hp_comap_max
  have hq_max : q.asIdeal.IsMaximal := by
    have hq_comap_max : (Ideal.comap (algebraMap K R) q.asIdeal).IsMaximal := by
      have hq_comap_bot :
          Ideal.comap (algebraMap K R) q.asIdeal = (⊥ : Ideal K) := by
        exact Ideal.eq_bot_of_prime (I := Ideal.comap (algebraMap K R) q.asIdeal)
      simpa [hq_comap_bot] using (inferInstance : (⊥ : Ideal K).IsMaximal)
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.asIdeal hq_comap_max
  -- The unique maximal ideal of the local ring is therefore the unique prime ideal.
  exact PrimeSpectrum.ext <|
    (IsLocalRing.eq_maximalIdeal hp_max).trans (IsLocalRing.eq_maximalIdeal hq_max).symm

section

omit [IsLocalRing A] [IsLocalRing C] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A C)]

/-- Helper for Lemma 10.156.5: every maximal ideal of `B ⊗[A] C` contracts to `maximalIdeal B`
along the left structural map. -/
lemma maximal_comap_includeLeft_eq_maximalIdeal
    (Q : Ideal TensorD) [Q.IsMaximal] :
    Ideal.comap (includeLeft : B →ₐ[A] TensorD) Q = maximalIdeal B := by
  letI : Algebra.IsIntegral B TensorD := inferInstance
  have hQcomap_max :
      (Ideal.comap (includeLeft : B →ₐ[A] TensorD) Q).IsMaximal := by
    simpa using
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) (S := TensorD) Q)
  -- In the local source ring, there is only one maximal ideal to contract to.
  exact IsLocalRing.eq_maximalIdeal hQcomap_max

end

/-- Helper for Lemma 10.156.5: the closed fiber over `maximalIdeal A` already has only one prime
ideal because it is a local ring integral over the field `ResidueField A`. -/
lemma subsingleton_primeSpectrum_closedFiber :
    Subsingleton (PrimeSpectrum ClosedFiberA) := by
  -- Base change preserves integrality, so the existing field-integral local-ring lemma applies.
  exact
    subsingleton_primeSpectrum_of_isLocalRing_of_integral_over_field
      (K := ResidueField A) (R := ClosedFiberA)

/-- Helper for Lemma 10.156.5: the closed fiber over `maximalIdeal A` has a distinguished unique
prime, namely its maximal ideal. -/
@[reducible] noncomputable def unique_primeSpectrum_closedFiber :
    Unique (PrimeSpectrum ClosedFiberA) := by
  let q0 : PrimeSpectrum ClosedFiberA := ⟨maximalIdeal ClosedFiberA, inferInstance⟩
  refine { default := q0, uniq := ?_ }
  intro q
  exact (subsingleton_primeSpectrum_closedFiber (A := A) (C := C)).elim q q0

/-- Helper for Lemma 10.156.5: the closed fiber over `maximalIdeal A` is the quotient
`C / maximalIdeal A • C` as a ring. -/
noncomputable def closedFiberA_quotient_ringEquiv :
    (C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A)) ≃+* ClosedFiberA :=
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal A)).toRingEquiv).trans <|
    (Algebra.TensorProduct.comm A C (ResidueField A)).toRingEquiv

section

omit [IsLocalRing C] [IsLocalHom (algebraMap A C)] [Algebra.IsIntegral A C]

/-- Helper for Lemma 10.156.5: under the quotient model of the closed fiber, the class of
`c : C` maps to its image in `ClosedFiberA`. -/
@[simp] lemma closedFiberA_quotient_equiv_mk (c : C) :
    closedFiberA_quotient_ringEquiv
        (Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c) =
      algebraMap C ClosedFiberA c := by
  -- Unfold the quotient description and evaluate the standard tensor-product maps on `c`.
  rw [closedFiberA_quotient_ringEquiv, RingEquiv.trans_apply]
  change
    (Algebra.TensorProduct.comm A C (ResidueField A))
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal A))
          (Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c)) =
      algebraMap C ClosedFiberA c
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  rw [Algebra.TensorProduct.right_algebraMap_apply]
  exact
    Algebra.TensorProduct.comm_tmul
      (R := A) (A := C) (B := ResidueField A) c (1 : ResidueField A)

/-- Helper for Lemma 10.156.5: the canonical map `C → ClosedFiberA` is surjective because the
closed fiber is a quotient of `C`. -/
lemma closedFiberA_algebraMap_surjective :
    Function.Surjective (algebraMap C ClosedFiberA) := by
  intro x
  obtain ⟨y, rfl⟩ := closedFiberA_quotient_ringEquiv.surjective x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨c, (closedFiberA_quotient_equiv_mk (A := A) (C := C) c).symm⟩

end

/-- Helper for Lemma 10.156.5: the residue field at the maximal ideal of a local ring agrees with
its ordinary residue field. -/
private noncomputable def maximalIdealResidueFieldEquiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 10.156.5: the maximal-ideal residue-field equivalence sends the image of an
element to its ordinary residue class. -/
private theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (r : R) :
    maximalIdealResidueFieldEquiv R (algebraMap R (maximalIdeal R).ResidueField r) =
      residue R r := by
  -- Rewrite the source element through the quotient presentation of `ResidueField R`.
  rw [show algebraMap R (maximalIdeal R).ResidueField r =
      algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R r) by rfl]
  -- The chosen equivalence is inverse to the canonical algebra map.
  exact (maximalIdealResidueFieldEquiv R).apply_symm_apply (residue R r)

/-- Helper for Lemma 10.156.5: the maximal-ideal residue-field model is compatible with the
ordinary residue-field map induced by a local ring homomorphism. -/
private theorem maximalIdealResidueFieldEquiv_comp_residueFieldMap
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    (maximalIdealResidueFieldEquiv S).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdealResidueFieldEquiv R).toRingHom := by
  -- Compare both residue-field maps on residue classes coming from elements of the source ring.
  apply Ideal.ResidueField.ringHom_ext
  ext r
  change
    maximalIdealResidueFieldEquiv S
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap R (maximalIdeal R).ResidueField r)) =
      ResidueField.map f
        (maximalIdealResidueFieldEquiv R (algebraMap R (maximalIdeal R).ResidueField r))
  -- Each side is the residue class of `f r` in the ordinary residue field of `S`.
  rw [Ideal.ResidueField.map_algebraMap, maximalIdealResidueFieldEquiv_apply_algebraMap,
    maximalIdealResidueFieldEquiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 10.156.5: the residue field at the unique closed-fiber prime is the same
as the residue field of `C` as a ring. -/
noncomputable def closedFiber_default_residueField_ringEquiv_residueFieldC :
    let q0 : PrimeSpectrum ClosedFiberA := (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
    q0.asIdeal.ResidueField ≃+* (maximalIdeal C).ResidueField := by
  let q0 : PrimeSpectrum ClosedFiberA :=
    (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
  have hsurj : Function.Surjective (algebraMap C ClosedFiberA) :=
    closedFiberA_algebraMap_surjective (A := A) (C := C)
  have hmap :
      Ideal.map (algebraMap C ClosedFiberA) (maximalIdeal C) = q0.asIdeal := by
    -- The surjective quotient map `C → ClosedFiberA` carries the maximal ideal of `C` onto the
    -- maximal ideal of the local quotient.
    simpa [q0] using
      (IsLocalRing.map_maximalIdeal_of_surjective (algebraMap C ClosedFiberA) hsurj)
  have hker_eq :
      RingHom.ker (algebraMap C ClosedFiberA) =
        Ideal.map (algebraMap A C) (maximalIdeal A) := by
    ext c
    constructor
    · intro hc
      have hquot :
          closedFiberA_quotient_ringEquiv
              (Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c) = 0 := by
        simpa [RingHom.mem_ker, closedFiberA_quotient_equiv_mk] using hc
      have hmk :
          Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c = 0 :=
        closedFiberA_quotient_ringEquiv.injective (by simpa using hquot)
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hmk
    · intro hc
      have hmk :
          Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c = 0 := by
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
      simpa [RingHom.mem_ker, closedFiberA_quotient_equiv_mk] using
        congrArg closedFiberA_quotient_ringEquiv hmk
  have hker_le : RingHom.ker (algebraMap C ClosedFiberA) ≤ maximalIdeal C := by
    rw [hker_eq]
    exact Ideal.map_le_iff_le_comap.mpr <|
      by simpa [IsLocalRing.maximalIdeal_comap (algebraMap A C)] using
        (le_rfl : maximalIdeal A ≤ maximalIdeal A)
  have hcomap :
      Ideal.comap (algebraMap C ClosedFiberA) q0.asIdeal = maximalIdeal C := by
    calc
      Ideal.comap (algebraMap C ClosedFiberA) q0.asIdeal =
          Ideal.comap (algebraMap C ClosedFiberA)
            (Ideal.map (algebraMap C ClosedFiberA) (maximalIdeal C)) := by
            rw [hmap]
      _ = maximalIdeal C ⊔ Ideal.comap (algebraMap C ClosedFiberA) ⊥ := by
            exact Ideal.comap_map_of_surjective (algebraMap C ClosedFiberA) hsurj (maximalIdeal C)
      _ = maximalIdeal C := by
            rw [sup_eq_left.mpr]
            simpa [RingHom.ker_eq_comap_bot] using hker_le
  let e :
      (maximalIdeal C).ResidueField ≃+* q0.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map (maximalIdeal C) q0.asIdeal
        (algebraMap C ClosedFiberA) hcomap.symm)
      ((RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective _ _ hcomap.symm)
  -- Turn the residue-field map around so later left-branch work can compare the closed fiber
  -- directly with `ResidueField C`.
  exact e.symm

/-- Helper for Lemma 10.156.5: the unique prime of the closed fiber contracts to the maximal
ideal of `C`. -/
lemma closedFiber_default_comap_eq_maximalIdeal :
    let q0 : PrimeSpectrum ClosedFiberA := (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
    Ideal.comap (algebraMap C ClosedFiberA) q0.asIdeal = maximalIdeal C := by
  let q0 : PrimeSpectrum ClosedFiberA :=
    (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
  have hsurj : Function.Surjective (algebraMap C ClosedFiberA) :=
    closedFiberA_algebraMap_surjective (A := A) (C := C)
  have hmap :
      Ideal.map (algebraMap C ClosedFiberA) (maximalIdeal C) = q0.asIdeal := by
    -- The surjective quotient map `C → ClosedFiberA` sends the maximal ideal of `C` onto the
    -- maximal ideal of the local closed fiber.
    simpa [q0] using
      (IsLocalRing.map_maximalIdeal_of_surjective (algebraMap C ClosedFiberA) hsurj)
  have hker_eq :
      RingHom.ker (algebraMap C ClosedFiberA) =
        Ideal.map (algebraMap A C) (maximalIdeal A) := by
    -- Compare the kernel with the quotient presentation of the closed fiber.
    ext c
    constructor
    · intro hc
      have hquot :
          closedFiberA_quotient_ringEquiv
              (Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c) = 0 := by
        simpa [RingHom.mem_ker, closedFiberA_quotient_equiv_mk] using hc
      have hmk :
          Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c = 0 :=
        closedFiberA_quotient_ringEquiv.injective (by simpa using hquot)
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hmk
    · intro hc
      have hmk :
          Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)) c = 0 := by
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
      simpa [RingHom.mem_ker, closedFiberA_quotient_equiv_mk] using
        congrArg closedFiberA_quotient_ringEquiv hmk
  have hker_le : RingHom.ker (algebraMap C ClosedFiberA) ≤ maximalIdeal C := by
    -- The kernel is generated by the image of `maximalIdeal A`, hence it lies in `maximalIdeal C`
    -- because `A → C` is local.
    rw [hker_eq]
    exact Ideal.map_le_iff_le_comap.mpr <|
      by simpa [IsLocalRing.maximalIdeal_comap (algebraMap A C)] using
        (le_rfl : maximalIdeal A ≤ maximalIdeal A)
  -- The contraction is the unique maximal ideal containing the kernel of the quotient map.
  calc
    Ideal.comap (algebraMap C ClosedFiberA) q0.asIdeal =
        Ideal.comap (algebraMap C ClosedFiberA)
          (Ideal.map (algebraMap C ClosedFiberA) (maximalIdeal C)) := by
          rw [hmap]
    _ = maximalIdeal C ⊔ Ideal.comap (algebraMap C ClosedFiberA) ⊥ := by
          exact Ideal.comap_map_of_surjective (algebraMap C ClosedFiberA) hsurj (maximalIdeal C)
    _ = maximalIdeal C := by
          rw [sup_eq_left.mpr]
          simpa [RingHom.ker_eq_comap_bot] using hker_le

/-- Helper for Lemma 10.156.5: the residue field at the unique closed-fiber prime identifies with
`ResidueField C` as a `ResidueField A`-algebra. -/
private noncomputable instance maximalIdealResidueField_algebra_residueFieldA :
    Algebra (ResidueField A) (maximalIdeal C).ResidueField :=
  ((Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal C) (algebraMap A C)
      (IsLocalRing.maximalIdeal_comap (algebraMap A C)).symm).comp
    (maximalIdealResidueFieldEquiv A).symm.toRingHom).toAlgebra

section

omit [Algebra.IsIntegral A C]

/-- Helper for Lemma 10.156.5: the induced `ResidueField A`-algebra structure on
`(maximalIdeal C).ResidueField` is compatible with the original `A`-algebra structure. -/
private theorem maximalIdealResidueField_algebra_residueFieldA_comp_algebraMap :
    (algebraMap (ResidueField A) (maximalIdeal C).ResidueField).comp
        (algebraMap A (ResidueField A)) =
      algebraMap A (maximalIdeal C).ResidueField := by
  ext a
  -- Rewrite the source residue class through the maximal-ideal residue-field equivalence on `A`.
  change
    Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal C) (algebraMap A C)
        (IsLocalRing.maximalIdeal_comap (algebraMap A C)).symm
        ((maximalIdealResidueFieldEquiv A).symm (residue A a)) =
      algebraMap A (maximalIdeal C).ResidueField a
  have hresidue :
      (maximalIdealResidueFieldEquiv A).symm (residue A a) =
        algebraMap A (maximalIdeal A).ResidueField a := by
    have happly :
        maximalIdealResidueFieldEquiv A
            ((maximalIdealResidueFieldEquiv A).symm (residue A a)) =
          maximalIdealResidueFieldEquiv A
            (algebraMap A (maximalIdeal A).ResidueField a) := by
      rw [(maximalIdealResidueFieldEquiv A).apply_symm_apply]
      simpa using (maximalIdealResidueFieldEquiv_apply_algebraMap A a).symm
    exact (maximalIdealResidueFieldEquiv A).injective happly
  rw [hresidue, Ideal.ResidueField.map_algebraMap]
  rfl

end

/-- Helper for Lemma 10.156.5: the induced `ResidueField A`-algebra structure on
`(maximalIdeal C).ResidueField` forms a scalar tower with the original `A`-algebra structure. -/
private noncomputable instance maximalIdealResidueField_isScalarTower_residueFieldA :
    IsScalarTower A (ResidueField A) (maximalIdeal C).ResidueField :=
  IsScalarTower.of_algebraMap_eq'
    (maximalIdealResidueField_algebra_residueFieldA_comp_algebraMap (A := A) (C := C)).symm

section

omit [IsLocalRing A] [IsLocalHom (algebraMap A C)] [Algebra.IsIntegral A C]

/-- Helper for Lemma 10.156.5: the maximal-ideal residue-field identification for `C` is already
`A`-linear. -/
private theorem maximalIdealResidueFieldEquiv_commutes_algebraMap
    (a : A) :
    maximalIdealResidueFieldEquiv C (algebraMap A (maximalIdeal C).ResidueField a) =
      algebraMap A (ResidueField C) a := by
  -- Rewrite both `A`-algebra maps through the underlying element of `C`.
  simpa using
    (maximalIdealResidueFieldEquiv_apply_algebraMap C (algebraMap A C a))

end

/-- Helper for Lemma 10.156.5: the unique closed-fiber residue field identifies with the maximal
ideal residue field of `C` as a `ResidueField A`-algebra. -/
noncomputable def closedFiber_default_residueField_algEquiv_maximalIdealResidueFieldC_aux :
    let q0 : PrimeSpectrum ClosedFiberA := (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
    q0.asIdeal.ResidueField ≃ₐ[ResidueField A] (maximalIdeal C).ResidueField := by
  let q0 : PrimeSpectrum ClosedFiberA :=
    (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
  have hsurj : Function.Surjective (algebraMap C ClosedFiberA) :=
    closedFiberA_algebraMap_surjective (A := A) (C := C)
  have hcomap :
      Ideal.comap (algebraMap C ClosedFiberA) q0.asIdeal = maximalIdeal C :=
    closedFiber_default_comap_eq_maximalIdeal (A := A) (C := C)
  let eA : (maximalIdeal C).ResidueField ≃ₐ[A] q0.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ (R := A) (maximalIdeal C) q0.asIdeal
        (includeRight : C →ₐ[A] ClosedFiberA) (by simpa using hcomap.symm))
      (by
        -- Surjectivity on stalks upgrades the quotient residue-field map to an isomorphism.
        simpa [Ideal.ResidueField.mapₐ_apply] using
          ((RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective
            (maximalIdeal C) q0.asIdeal hcomap.symm))
  -- Extend scalars from `A` to `ResidueField A` through the surjective residue map.
  exact eA.symm.extendScalarsOfSurjective (residue_surjective (R := A))

/-- Helper for Lemma 10.156.5: the residue field at the zero prime of a field is canonically the
field itself. -/
private noncomputable def field_bot_residueField_algEquiv
    (K : Type*) [Field K] :
    ((⊥ : Ideal K).ResidueField) ≃ₐ[K] K := by
  let eQuot :
      (K ⧸ (⊥ : Ideal K)) ≃ₐ[K] ((⊥ : Ideal K).ResidueField) :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K (K ⧸ (⊥ : Ideal K)) ((⊥ : Ideal K).ResidueField))
      (Ideal.bijective_algebraMap_quotient_residueField (⊥ : Ideal K))
  -- Replace the bottom-prime residue field by the field quotient `K ⧸ ⊥`.
  exact eQuot.symm.trans (AlgEquiv.quotientBot K K)

/-- Helper for Lemma 10.156.5: after extending scalars from `A` to `ResidueField A`, the maximal
ideal residue-field identification for `C` becomes `ResidueField A`-linear. -/
private noncomputable def maximalIdealResidueFieldEquiv_algEquiv_residueFieldA :
    (maximalIdeal C).ResidueField ≃ₐ[ResidueField A] ResidueField C := by
  let eA : (maximalIdeal C).ResidueField ≃ₐ[A] ResidueField C :=
    AlgEquiv.ofRingEquiv (f := maximalIdealResidueFieldEquiv C)
      (maximalIdealResidueFieldEquiv_commutes_algebraMap (A := A) (C := C))
  -- The `A`-linear comparison descends along the surjective residue map `A → κ(A)`.
  exact eA.extendScalarsOfSurjective (residue_surjective (R := A))

/-- Helper for Lemma 10.156.5: the unique closed-fiber residue field identifies with the ordinary
residue field of `C` through the maximal-ideal residue-field model. -/
noncomputable def closedFiber_default_residueField_algEquiv_residueFieldC_aux :
    let q0 : PrimeSpectrum ClosedFiberA := (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
    q0.asIdeal.ResidueField ≃ₐ[ResidueField A] ResidueField C := by
  let q0 : PrimeSpectrum ClosedFiberA :=
    (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
  let eClosed :
      q0.asIdeal.ResidueField ≃ₐ[ResidueField A] (maximalIdeal C).ResidueField :=
    closedFiber_default_residueField_algEquiv_maximalIdealResidueFieldC_aux (A := A) (C := C)
  let eResidue :
      (maximalIdeal C).ResidueField ≃ₐ[ResidueField A] ResidueField C :=
    maximalIdealResidueFieldEquiv_algEquiv_residueFieldA (A := A) (C := C)
  -- Compose the closed-fiber comparison with the local-ring residue-field identification.
  exact eClosed.trans eResidue

/-- Helper for Lemma 10.156.5: the residue field at the unique closed-fiber prime identifies with
`ResidueField C` as a `ResidueField A`-algebra. -/
noncomputable def closedFiber_default_residueField_algEquiv_residueFieldC :
    let q0 : PrimeSpectrum ClosedFiberA := (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
    q0.asIdeal.ResidueField ≃ₐ[ResidueField A] ResidueField C :=
  closedFiber_default_residueField_algEquiv_residueFieldC_aux (A := A) (C := C)

/-- Helper for Lemma 10.156.5: in the left purely inseparable branch, the closed fiber
`κ(A) ⊗[A] C` induces purely inseparable residue-field extensions over `κ(A)`. -/
lemma closedFiber_hasPurelyInseparableResidueFieldExtensions_of_left_branch
    (hκC : IsPurelyInseparable (ResidueField A) (ResidueField C)) :
    (algebraMap (ResidueField A) ClosedFiberA).HasPurelyInseparableResidueFieldExtensions := by
  intro q
  let q0 : PrimeSpectrum ClosedFiberA :=
    (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
  have hq : q = q0 := (subsingleton_primeSpectrum_closedFiber (A := A) (C := C)).elim q q0
  subst q
  let p : PrimeSpectrum (ResidueField A) :=
    PrimeSpectrum.comap (algebraMap (ResidueField A) ClosedFiberA) q0
  have hp : p.asIdeal = (⊥ : Ideal (ResidueField A)) := Ideal.eq_bot_of_prime (I := p.asIdeal)
  have hp' : p = (⟨⊥, inferInstance⟩ : PrimeSpectrum (ResidueField A)) := by
    exact PrimeSpectrum.ext hp
  have hq0 :
      IsPurelyInseparable (ResidueField A) q0.asIdeal.ResidueField := by
    -- Transport the given left-branch hypothesis across the unique closed-fiber residue-field
    -- comparison.
    letI : Algebra (ResidueField A) q0.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (R := Localization.AtPrime q0.asIdeal)
    letI := hκC
    exact
      (closedFiber_default_residueField_algEquiv_residueFieldC
        (A := A) (C := C)).symm.isPurelyInseparable
  let fκ :
      p.asIdeal.ResidueField →+* q0.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q0.asIdeal
      (algebraMap (ResidueField A) ClosedFiberA) rfl
  letI : Algebra p.asIdeal.ResidueField q0.asIdeal.ResidueField := fκ.toAlgebra
  letI : Algebra (ResidueField A) q0.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (R := Localization.AtPrime q0.asIdeal)
  have hfκ_comp :
      algebraMap (ResidueField A) q0.asIdeal.ResidueField =
        fκ.comp (algebraMap (ResidueField A) p.asIdeal.ResidueField) := by
    ext a
    rw [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply (ResidueField A) ClosedFiberA q0.asIdeal.ResidueField]
  letI : IsScalarTower (ResidueField A) p.asIdeal.ResidueField q0.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' hfκ_comp
  have hpure :
      IsPurelyInseparable p.asIdeal.ResidueField q0.asIdeal.ResidueField := by
    let eSource :
        p.asIdeal.ResidueField ≃ₐ[ResidueField A]
          ((⊥ : Ideal (ResidueField A)).ResidueField) :=
      AlgEquiv.ofBijective
        (Ideal.ResidueField.mapₐ p.asIdeal (⊥ : Ideal (ResidueField A))
          (Algebra.ofId _ _) (by simpa using hp))
        ((RingHom.surjectiveOnStalks_of_surjective (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective
          p.asIdeal (⊥ : Ideal (ResidueField A)) (by simpa using hp))
    have hp_source :
        IsPurelyInseparable (ResidueField A) p.asIdeal.ResidueField := by
      exact
        ((field_bot_residueField_algEquiv (ResidueField A)).symm.trans
          eSource.symm).isPurelyInseparable
    letI : IsPurelyInseparable (ResidueField A) p.asIdeal.ResidueField := hp_source
    letI : IsPurelyInseparable (ResidueField A) q0.asIdeal.ResidueField := hq0
    exact
      IsPurelyInseparable.tower_top (ResidueField A) p.asIdeal.ResidueField
        q0.asIdeal.ResidueField
  -- The contracted prime downstairs is the zero prime of the field `κ(A)`, so the canonical
  -- residue-field map is purely inseparable by `tower_top`.
  simpa [p, hp'] using hpure

/-- Helper for Lemma 10.156.5: the left closed fiber over `maximalIdeal B` is the base change of
the closed fiber over `maximalIdeal A`. -/
noncomputable def residueField_tensor_left_equiv_baseChange_closedFiber :
    ResidueField B ⊗[A] C ≃ₐ[ResidueField B]
      ResidueField B ⊗[ResidueField A] ClosedFiberA :=
  (Algebra.TensorProduct.cancelBaseChange
    (R := A) (S := ResidueField A) (T := ResidueField B)
    (A := ResidueField B) (B := C)).symm

/-- Helper for Lemma 10.156.5: in the left purely inseparable branch, the left closed fiber over
`maximalIdeal B` has a unique prime because it is the base change of a closed fiber whose spectral
map is a bijection with purely inseparable residue-field extensions. -/
@[reducible] noncomputable def unique_primeSpectrum_residueField_tensor_left_of_left_branch_aux
    (hκC : IsPurelyInseparable (ResidueField A) (ResidueField C)) :
    Unique (PrimeSpectrum (ResidueField B ⊗[A] C)) := by
  classical
  have hbij :
      Function.Bijective (PrimeSpectrum.comap (algebraMap (ResidueField A) ClosedFiberA)) := by
    refine ⟨?_, ?_⟩
    · intro q₁ q₂ hq
      exact (subsingleton_primeSpectrum_closedFiber (A := A) (C := C)).elim q₁ q₂
    · intro p
      let q0 : PrimeSpectrum ClosedFiberA :=
        (unique_primeSpectrum_closedFiber (A := A) (C := C)).default
      -- Both spectra are already singleton spaces, so surjectivity is automatic.
      exact ⟨q0, (Subsingleton.elim _ _)⟩
  have hInt : (algebraMap (ResidueField A) ClosedFiberA).IsIntegral :=
    algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral (ResidueField A) ClosedFiberA)
  obtain ⟨_, hbaseChange⟩ :=
    isHomeomorph_comap_and_baseChange_of_integral_bijective_and_purelyInseparableResidueFields
      (R := ResidueField A) (S := ClosedFiberA)
      hInt
      hbij
      (closedFiber_hasPurelyInseparableResidueFieldExtensions_of_left_branch
        (A := A) (C := C) hκC)
  have hbijBase :
      Function.Bijective
        (PrimeSpectrum.comap
          (algebraMap (ResidueField B)
            (ResidueField B ⊗[ResidueField A] ClosedFiberA))) :=
    -- Specialize Lemma `10.46.10` to the base change `ResidueField A → ResidueField B`
    -- and keep only the bijectivity clause to avoid elaborating the full triple repeatedly.
    (hbaseChange (R' := ResidueField B)).2.1
  have hsubBase :
      Subsingleton (PrimeSpectrum (ResidueField B ⊗[ResidueField A] ClosedFiberA)) := by
    refine ⟨fun q₁ q₂ ↦ hbijBase.1 ?_⟩
    apply PrimeSpectrum.ext
    calc
      (PrimeSpectrum.comap
          (algebraMap (ResidueField B)
            (ResidueField B ⊗[ResidueField A] ClosedFiberA)) q₁).asIdeal =
          (⊥ : Ideal (ResidueField B)) :=
        Ideal.eq_bot_of_prime
          (I := (PrimeSpectrum.comap
            (algebraMap (ResidueField B)
              (ResidueField B ⊗[ResidueField A] ClosedFiberA)) q₁).asIdeal)
      _ =
          (PrimeSpectrum.comap
            (algebraMap (ResidueField B)
              (ResidueField B ⊗[ResidueField A] ClosedFiberA)) q₂).asIdeal :=
        (Ideal.eq_bot_of_prime
          (I := (PrimeSpectrum.comap
            (algebraMap (ResidueField B)
              (ResidueField B ⊗[ResidueField A] ClosedFiberA)) q₂).asIdeal)).symm
  let qBase : PrimeSpectrum (ResidueField B ⊗[ResidueField A] ClosedFiberA) :=
    Classical.choose (hbijBase.2 (⟨⊥, inferInstance⟩ : PrimeSpectrum (ResidueField B)))
  let hUniqueBase :
      Unique (PrimeSpectrum (ResidueField B ⊗[ResidueField A] ClosedFiberA)) :=
    { default := qBase
      uniq := fun q ↦ hsubBase.elim q qBase }
  let eTensor :
      PrimeSpectrum (ResidueField B ⊗[A] C) ≃
        PrimeSpectrum (ResidueField B ⊗[ResidueField A] ClosedFiberA) :=
    (PrimeSpectrum.comapEquiv
      (residueField_tensor_left_equiv_baseChange_closedFiber
        (A := A) (B := B) (C := C)).toRingEquiv).toEquiv
  let q0 : PrimeSpectrum (ResidueField B ⊗[A] C) := eTensor.symm hUniqueBase.default
  refine { default := q0, uniq := ?_ }
  intro q
  -- The base-changed spectrum is already singleton, so transport that uniqueness back.
  apply eTensor.injective
  simpa [q0] using hUniqueBase.uniq (eTensor q)

/-- Helper for Lemma 10.156.5: in the left purely inseparable branch, the left closed fiber over
`maximalIdeal B` has a unique prime because it is the base change of a closed fiber whose spectral
map is a bijection with purely inseparable residue-field extensions. -/
@[reducible] noncomputable def unique_primeSpectrum_residueField_tensor_left_of_left_branch
    (hκC : IsPurelyInseparable (ResidueField A) (ResidueField C)) :
    Unique (PrimeSpectrum (ResidueField B ⊗[A] C)) :=
  unique_primeSpectrum_residueField_tensor_left_of_left_branch_aux
    (A := A) (B := B) (C := C) hκC

/-- Helper for Lemma 10.156.5: in the right purely inseparable branch, the left closed fiber over
`maximalIdeal B` has a unique prime because it is a purely inseparable base change of the already
singleton closed fiber over `maximalIdeal A`. -/
@[reducible] noncomputable def unique_primeSpectrum_residueField_tensor_left_of_right_branch
    (hκB : IsPurelyInseparable (ResidueField A) (ResidueField B)) :
    Unique (PrimeSpectrum (ResidueField B ⊗[A] C)) := by
  letI := hκB
  let eBase :
      PrimeSpectrum (ResidueField B ⊗[A] C) ≃
        PrimeSpectrum (ResidueField B ⊗[ResidueField A] ClosedFiberA) :=
    (PrimeSpectrum.comapEquiv
      (residueField_tensor_left_equiv_baseChange_closedFiber
        (A := A) (B := B) (C := C)).toRingEquiv).toEquiv
  let eComm :
      PrimeSpectrum (ResidueField B ⊗[ResidueField A] ClosedFiberA) ≃
        PrimeSpectrum (ClosedFiberA ⊗[ResidueField A] ResidueField B) :=
    (PrimeSpectrum.comapEquiv
      (Algebra.TensorProduct.comm
        (R := ResidueField A) (A := ResidueField B) (B := ClosedFiberA)).toRingEquiv).toEquiv
  let ePure :
      PrimeSpectrum (ClosedFiberA ⊗[ResidueField A] ResidueField B) ≃
        PrimeSpectrum ClosedFiberA :=
    Equiv.ofBijective
      (PrimeSpectrum.comap
        (algebraMap ClosedFiberA
          (ClosedFiberA ⊗[ResidueField A] ResidueField B)))
      (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable
        (k := ResidueField A) (K := ResidueField B) (R := ClosedFiberA)).bijective
  let e :
      PrimeSpectrum (ResidueField B ⊗[A] C) ≃ PrimeSpectrum ClosedFiberA :=
    eBase.trans <| eComm.trans ePure
  let qClosed : PrimeSpectrum ClosedFiberA := ⟨maximalIdeal ClosedFiberA, inferInstance⟩
  let q0 : PrimeSpectrum (ResidueField B ⊗[A] C) := e.symm qClosed
  refine { default := q0, uniq := ?_ }
  intro q
  -- Transport the unique closed-fiber prime back through the base-change equivalences.
  apply e.injective
  have hq : e q = qClosed :=
    (subsingleton_primeSpectrum_closedFiber (A := A) (C := C)).elim _ _
  simpa [q0] using hq

/-- Helper for Lemma 10.156.5: quotienting `B ⊗[A] C` by the ideal generated by `maximalIdeal B`
along the left structural map produces the source quotient `κ(B) ⊗[A] C`. -/
noncomputable def tensorProduct_quotient_left_maximal_equiv :
    (TensorD ⧸ Ideal.map (includeLeft : B →ₐ[A] TensorD) (maximalIdeal B)) ≃+*
      (ResidueField B ⊗[A] C) :=
  ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor
      (A := B) (B := TensorD) (I := maximalIdeal B)).toRingEquiv).trans <|
    (Algebra.TensorProduct.cancelBaseChange
      (R := A) (S := B) (T := ResidueField B) (A := ResidueField B) (B := C)).toRingEquiv

/-- Helper for Lemma 10.156.5: uniqueness of the prime spectrum of `κ(B) ⊗[A] C` transports to
the closed fiber over `maximalIdeal B`. -/
@[reducible] noncomputable def unique_primeSpectrum_left_closedFiber_of_unique_residueField_tensor
    (hTensor : Unique (PrimeSpectrum (ResidueField B ⊗[A] C))) :
    Unique (PrimeSpectrum ((maximalIdeal B).Fiber TensorD)) := by
  let eQuot :
      (maximalIdeal B).Fiber TensorD ≃+*
        (TensorD ⧸ Ideal.map (includeLeft : B →ₐ[A] TensorD) (maximalIdeal B)) :=
    ((Algebra.TensorProduct.congr
        (.symm <| .ofBijective _
          (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal B))) .refl).trans <|
      (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)).toRingEquiv
  let e :
      PrimeSpectrum ((maximalIdeal B).Fiber TensorD) ≃
        PrimeSpectrum (ResidueField B ⊗[A] C) :=
    (PrimeSpectrum.comapEquiv
      (eQuot.trans (tensorProduct_quotient_left_maximal_equiv
        (A := A) (B := B) (C := C)))).toEquiv
  refine
    { default := e.symm hTensor.default
      uniq := ?_ }
  intro q
  -- Identify every fiber prime with the transported distinguished prime through the algebra
  -- equivalence of the closed fiber.
  apply e.injective
  simpa using hTensor.uniq (e q)

section

omit [IsLocalRing A] [IsLocalRing C] [IsLocalHom (algebraMap A B)]
  [IsLocalHom (algebraMap A C)]

/-- Helper for Lemma 10.156.5: if the closed fiber over `maximalIdeal B` has a unique prime, then
`B ⊗[A] C` itself has a unique maximal ideal. -/
lemma unique_maximalIdeal_tensor_of_unique_left_closedFiber
    (hFiber : Unique (PrimeSpectrum (ResidueField B ⊗[A] C))) :
    ∃! I : Ideal TensorD, I.IsMaximal := by
  let pB : PrimeSpectrum B := ⟨maximalIdeal B, inferInstance⟩
  let eFiber :
      PrimeSpectrum.comap (algebraMap B TensorD) ⁻¹' ({pB} : Set (PrimeSpectrum B)) ≃
        PrimeSpectrum ((maximalIdeal B).Fiber TensorD) :=
    PrimeSpectrum.preimageEquivFiber B TensorD pB
  let hLeftFiber :
      Unique (PrimeSpectrum ((maximalIdeal B).Fiber TensorD)) :=
    unique_primeSpectrum_left_closedFiber_of_unique_residueField_tensor
      (A := A) (B := B) (C := C) hFiber
  let qOver :
      PrimeSpectrum.comap (algebraMap B TensorD) ⁻¹' ({pB} : Set (PrimeSpectrum B)) :=
    eFiber.symm hLeftFiber.default
  let q : PrimeSpectrum TensorD := qOver.1
  have hq_comap :
      Ideal.comap (algebraMap B TensorD) q.asIdeal = maximalIdeal B := by
    -- The chosen prime lies in the closed fiber over `maximalIdeal B` by construction.
    exact congrArg PrimeSpectrum.asIdeal qOver.2
  have hq_max : q.asIdeal.IsMaximal := by
    letI : Algebra.IsIntegral B TensorD := inferInstance
    have hq_comap_max :
        (Ideal.comap (algebraMap B TensorD) q.asIdeal).IsMaximal := by
      simpa [hq_comap] using (inferInstance : (maximalIdeal B).IsMaximal)
    -- Integrality of `B → B ⊗[A] C` promotes maximality from the contraction.
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.asIdeal hq_comap_max
  refine ⟨q.asIdeal, hq_max, ?_⟩
  intro I hI_max
  let Q : PrimeSpectrum TensorD := ⟨I, inferInstance⟩
  have hQ_comap :
      PrimeSpectrum.comap (algebraMap B TensorD) Q = pB := by
    apply PrimeSpectrum.ext
    -- Every maximal ideal of the tensor product lies over `maximalIdeal B`.
    simpa using maximal_comap_includeLeft_eq_maximalIdeal (A := A) (B := B) (C := C) (Q := I)
  let QOver :
      PrimeSpectrum.comap (algebraMap B TensorD) ⁻¹' ({pB} : Set (PrimeSpectrum B)) :=
    ⟨Q, hQ_comap⟩
  have hQOver_eq_qOver : QOver = qOver := by
    -- Route correction: compare maximal ideals upstairs by first comparing their points in the
    -- closed fiber over `maximalIdeal B`, not by quotienting again.
    exact eFiber.injective <| by
      simpa [qOver] using hLeftFiber.uniq (eFiber QOver)
  have hQ_eq_q : Q = q := congrArg Subtype.val hQOver_eq_qOver
  exact congrArg PrimeSpectrum.asIdeal hQ_eq_q

end

-- Proof sketch: every maximal ideal of `B ⊗[A] C` lies over the maximal ideal of `B` by the
-- previous contraction lemma. The remaining source-proof step is to show that the closed fiber
-- over this closed point has singleton spectrum under the purely inseparable hypothesis.
/-- Lemma 10.156.5: if `A → B` and `A → C` are local homomorphisms of local rings, `A → C` is
integral, and either `ResidueField C / ResidueField A` or `ResidueField B / ResidueField A` is
purely inseparable, then `B ⊗[A] C` is a local ring. -/
@[stacks 092Y]
theorem tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
    (hκ :
      IsPurelyInseparable (ResidueField A) (ResidueField C) ∨
        IsPurelyInseparable (ResidueField A) (ResidueField B))
    : IsLocalRing TensorD := by
  refine IsLocalRing.of_unique_max_ideal ?_
  rcases hκ with hκC | hκB
  · -- Route correction: the left branch now follows the same closed-fiber skeleton as the right
    -- branch, but it uses Lemma `10.46.10` for `κ(A) → κ(A) ⊗[A] C`.
    exact
      unique_maximalIdeal_tensor_of_unique_left_closedFiber
        (A := A) (B := B) (C := C)
        (unique_primeSpectrum_residueField_tensor_left_of_left_branch
          (A := A) (B := B) (C := C) hκC)
  · -- The right purely inseparable branch already gives a singleton closed fiber over `m_B`.
    exact
      unique_maximalIdeal_tensor_of_unique_left_closedFiber
        (A := A) (B := B) (C := C)
        (unique_primeSpectrum_residueField_tensor_left_of_right_branch
          (A := A) (B := B) (C := C) hκB)

-- Proof sketch: once the tensor product is known to be local, the maximal-ideal contraction
-- equality from `maximal_comap_includeLeft_eq_maximalIdeal` is exactly clause `(5)` of
-- `local_hom_TFAE`.
/-- Under the residue-field purely inseparable hypothesis, the canonical map
`B → B ⊗[A] C` is a local homomorphism. -/
theorem tensorProduct_includeLeft_isLocalHom_of_local_of_integral_of_residueField_purelyInseparable
    (hκ :
      IsPurelyInseparable (ResidueField A) (ResidueField C) ∨
        IsPurelyInseparable (ResidueField A) (ResidueField B))
    : IsLocalHom (includeLeft : B →ₐ[A] TensorD) := by
  letI : IsLocalRing TensorD :=
    tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
      (A := A) (B := B) (C := C) hκ
  -- Once `TensorD` is local, the contraction identity is exactly clause `(5)` of
  -- `IsLocalRing.local_hom_TFAE`.
  have hlocal :
      IsLocalHom ((includeLeft : B →ₐ[A] TensorD).toRingHom) := by
    refine
      ((IsLocalRing.local_hom_TFAE ((includeLeft : B →ₐ[A] TensorD).toRingHom)).out 4 0).mp ?_
    simpa using
      (maximal_comap_includeLeft_eq_maximalIdeal (Q := maximalIdeal TensorD))
  exact ⟨fun a ha ↦ hlocal.map_nonunit a ha⟩

/-- Helper for Lemma 10.156.5: once `B ⊗[A] C` is local, its maximal ideal contracts to the
maximal ideal of `C` along the right structural map. -/
lemma maximalIdeal_comap_includeRight_eq_maximalIdeal
    (hκ :
      IsPurelyInseparable (ResidueField A) (ResidueField C) ∨
        IsPurelyInseparable (ResidueField A) (ResidueField B))
    [IsLocalRing TensorD] :
    Ideal.comap (includeRight : C →ₐ[A] TensorD) (maximalIdeal TensorD) = maximalIdeal C := by
  letI : IsLocalHom (includeLeft : B →ₐ[A] TensorD) :=
    tensorProduct_includeLeft_isLocalHom_of_local_of_integral_of_residueField_purelyInseparable
      (A := A) (B := B) (C := C) hκ
  letI : IsLocalHom ((includeLeft : B →ₐ[A] TensorD).toRingHom) := by
    exact ⟨fun a ha ↦ by
      simpa using (IsLocalHom.map_nonunit (f := (includeLeft : B →ₐ[A] TensorD)) a ha)⟩
  have hATensor :
      IsLocalHom ((((includeLeft : B →ₐ[A] TensorD).toRingHom).comp (algebraMap A B))) := by
    infer_instance
  letI : IsLocalHom (algebraMap A TensorD) := by
    simpa using hATensor
  let q : Ideal C := Ideal.comap (includeRight : C →ₐ[A] TensorD) (maximalIdeal TensorD)
  have hq_comap :
      Ideal.comap (algebraMap A C) q = maximalIdeal A := by
    -- The right contraction lies over the closed point of `A` because `A → TensorD` is local.
    change Ideal.comap (((includeRight : C →ₐ[A] TensorD).toRingHom).comp (algebraMap A C))
        (maximalIdeal TensorD) = maximalIdeal A
    simpa [q] using
      (IsLocalRing.maximalIdeal_comap (algebraMap A TensorD))
  have hq_max :
      q.IsMaximal := by
    -- Integrality of `A → C` turns a prime over `maximalIdeal A` into a maximal ideal of `C`.
    have hq_comap_max :
        (Ideal.comap (algebraMap A C) q).IsMaximal := by
      simpa [hq_comap] using (inferInstance : (maximalIdeal A).IsMaximal)
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q hq_comap_max
  -- The local ring `C` has only one maximal ideal, so this contraction is `maximalIdeal C`.
  simpa [q] using IsLocalRing.eq_maximalIdeal hq_max

-- Proof sketch: after establishing locality of `B ⊗[A] C`, the right local-hom statement reduces
-- to showing that the maximal ideal of the tensor product contracts to the unique prime of `C`
-- over `maximalIdeal A`. The conceptual route is to identify that fiber with the closed fiber
-- `κ(A) ⊗[A] C`, which is local because `A → C` is integral and local.
/-- Under the residue-field purely inseparable hypothesis, the canonical map
`C → B ⊗[A] C` is a local homomorphism. -/
theorem tensorProduct_includeRight_isLocalHom_of_local_of_integral_of_residueField_purelyInseparable
    (hκ :
      IsPurelyInseparable (ResidueField A) (ResidueField C) ∨
        IsPurelyInseparable (ResidueField A) (ResidueField B))
    : IsLocalHom (includeRight : C →ₐ[A] TensorD) := by
  letI : IsLocalRing TensorD :=
    tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
      (A := A) (B := B) (C := C) hκ
  -- The contraction computed above is clause `(5)` of `IsLocalRing.local_hom_TFAE`.
  have hlocal :
      IsLocalHom ((includeRight : C →ₐ[A] TensorD).toRingHom) := by
    refine
      ((IsLocalRing.local_hom_TFAE ((includeRight : C →ₐ[A] TensorD).toRingHom)).out 4 0).mp ?_
    simpa using
      (maximalIdeal_comap_includeRight_eq_maximalIdeal
        (A := A) (B := B) (C := C) hκ)
  exact ⟨fun a ha ↦ hlocal.map_nonunit a ha⟩

end
