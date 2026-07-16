import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_26_3
import stacks_proof.stacks_project.Chap10.Lemma_10_47_2
import stacks_proof.stacks_project.Chap10.Lemma_10_112_8
import stacks_proof.stacks_project.Chap10.Definition_10_153_1
import stacks_proof.stacks_project.Chap10.Lemma_10_155_2
import stacks_proof.stacks_project.Chap15.Lemma_15_18_2
import stacks_proof.stacks_project.Chap15.Lemma_15_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open PrimeSpectrum
open scoped TensorProduct

universe u

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of strict henselizations, tensor products of local
  `k`-algebras, and minimal primes;
- sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `IsStrictHenselizationOf`,
  `minimalPrimes`,
  `Localization.AtPrime`,
  `Algebra.TensorProduct.includeLeft` / `includeRight`;
- best owner abstraction: the source-facing content is the contraction of a prime of the chosen
  strict henselization of the canonical closed-point localization of the tensor product to the
  pair of primes in the two tensor factors, while the canonical owners remain the closed-point
  prime, the strict-henselization structure, and the minimal primes as subtype owners;
- primitive data: the local `k`-algebras `A`, `B`, the closed-point localization of `A ⊗[k] B`,
  and its chosen strict henselization `C`;
- derived API: the two canonical maps `A → C`, `B → C`, and the induced map from primes of `C`
  to pairs of minimal primes of `A` and `B`; the localization step should be expressed through
  the canonical owner `Localization.AtPrime`, while the residue-field identifications with `k`
  should be `k`-algebra equivalences rather than bare ring equivalences.

Source/core/bridge triage:
- `source-facing`: `strictHenselianTensorMinimalPrimePair` and the bijection theorem below;
- `core/canonical`: `StrictHenselianLocalRing`, `IsStrictHenselizationOf`,
  `strictHenselianTensorClosedPoint`, `Ideal.comap`, `minimalPrimes`;
- `bridge/view`: the chosen strict henselization `C` of the canonical closed-point localization.
-/

variable {k A B C : Type u}
variable [Field k]
variable [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]

section ClosedPoint

variable [IsLocalRing A] [IsLocalRing B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The closed-point ideal `m_A ⊗ B + A ⊗ m_B` in the tensor product of two local `k`-algebras. -/
abbrev strictHenselianTensorClosedPointIdeal : Ideal (A ⊗[k] B) :=
  Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
      (IsLocalRing.maximalIdeal A) +
    Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
      (IsLocalRing.maximalIdeal B)

/-- Helper for Lemma 15.108.4: quotienting a local ring by its maximal ideal gives the usual
residue field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    R ⧸ maximalIdeal R ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).trans <|
      (RingEquiv.ofBijective
        (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.108.4: under the quotient-to-residue-field identification, the quotient
class of an element is its residue class. -/
private theorem maximalIdealQuotientResidueFieldEquiv_apply_mk
    (R : Type u) [CommRing R] [IsLocalRing R] (x : R) :
    maximalIdealQuotientResidueFieldEquiv R (Ideal.Quotient.mk (maximalIdeal R) x) =
      residue R x := by
  -- Both maps factor the same quotient class through the residue field owner.
  let eκR : ResidueField R ≃+* (maximalIdeal R).ResidueField :=
    RingEquiv.ofBijective
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  change
    eκR.symm
        (algebraMap R (maximalIdeal R).ResidueField x) =
      residue R x
  rw [show algebraMap R (maximalIdeal R).ResidueField x =
      eκR (residue R x) by rfl]
  exact eκR.symm_apply_apply (residue R x)

/-- Helper for Lemma 15.108.4: the quotient-by-maximal-ideal identification is compatible with
the ambient `k`-algebra structures. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldAlgEquiv
    (R : Type u) [CommRing R] [Algebra k R] [IsLocalRing R] :
    (R ⧸ maximalIdeal R) ≃ₐ[k] ResidueField R where
  toRingEquiv := maximalIdealQuotientResidueFieldEquiv R
  -- Both `k`-algebra structures come from the canonical quotient/residue maps.
  commutes' r := by
    exact maximalIdealQuotientResidueFieldEquiv_apply_mk R r

/-- Helper for Lemma 15.108.4: quotienting `A ⊗[k] B` by the left closed-point ideal produces the
base change of the residue field of `A`. -/
noncomputable abbrev strictHenselianTensor_leftClosedPointQuotAlgEquiv :
    ((A ⊗[k] B) ⧸
        Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
          (maximalIdeal A)) ≃ₐ[k] ResidueField A ⊗[k] B :=
  (AlgEquiv.restrictScalars k <|
      ((closedFiberQuotAlgEquiv :
          Ideal.Fiber (maximalIdeal A) (A ⊗[k] B) ≃ₐ[A]
            (A ⊗[k] B) ⧸ Ideal.map (algebraMap A (A ⊗[k] B)) (maximalIdeal A)).symm.trans
        (fiber_tensor_base_change_rightOrderAlgEquiv (R := k) (S := B) (R' := A)
          ⟨maximalIdeal A, maximalIdeal.isPrime A⟩))).trans <|
    (AlgEquiv.refl : ResidueField A ⊗[k] B ≃ₐ[k] ResidueField A ⊗[k] B)

/-- Helper for Lemma 15.108.4: quotienting `A ⊗[k] B` by the left closed-point ideal can also be
viewed directly as tensoring the quotient `A / m_A` with `B`. This route keeps the right tensor
factor visible, which is the source-faithful bridge for the second quotient. -/
noncomputable abbrev strictHenselianTensor_leftQuotTensorAlgEquiv :
    ((A ⊗[k] B) ⧸
        Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
          (maximalIdeal A)) ≃ₐ[k] (A ⧸ maximalIdeal A) ⊗[k] B :=
  AlgEquiv.restrictScalars k <|
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := k) (B := B) (I := maximalIdeal A)

/-- Helper for Lemma 15.108.4: under the direct left-quotient tensor presentation, the image of
the right closed-point ideal is exactly the obvious right closed-point ideal of
`(A / m_A) ⊗[k] B`. -/
lemma strictHenselianTensor_rightClosedPointIdeal_image_under_leftQuotTensor :
    Ideal.map
        (strictHenselianTensor_leftQuotTensorAlgEquiv (k := k) (A := A) (B := B)).toRingHom
        (Ideal.map
          (Ideal.Quotient.mk <|
            Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
              (maximalIdeal A))
          (Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
            (maximalIdeal B))) =
      Ideal.map
        (Algebra.TensorProduct.includeRight : B →ₐ[k] (A ⧸ maximalIdeal A) ⊗[k] B).toRingHom
        (maximalIdeal B) := by
  -- The quotient-tensor equivalence sends the class of `includeRight b` to the same tensor
  -- generator `1 ⊗ b`, so the mapped ideal is the right closed-point ideal on the nose.
  have hcomp :
      (((strictHenselianTensor_leftQuotTensorAlgEquiv (k := k) (A := A) (B := B)).toRingHom.comp
          (Ideal.Quotient.mk <|
            Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
              (maximalIdeal A))).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom) =
        (Algebra.TensorProduct.includeRight : B →ₐ[k] (A ⧸ maximalIdeal A) ⊗[k] B).toRingHom := by
    ext b
    simp [strictHenselianTensor_leftQuotTensorAlgEquiv,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  calc
    Ideal.map
        (strictHenselianTensor_leftQuotTensorAlgEquiv (k := k) (A := A) (B := B)).toRingHom
        (Ideal.map
          (Ideal.Quotient.mk <|
            Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
              (maximalIdeal A))
          (Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
            (maximalIdeal B))) =
        Ideal.map
          (((strictHenselianTensor_leftQuotTensorAlgEquiv (k := k) (A := A) (B := B)).toRingHom.comp
              (Ideal.Quotient.mk <|
                Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
                  (maximalIdeal A))).comp
            (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom)
          (maximalIdeal B) := by
            rw [Ideal.map_map, Ideal.map_map]
    _ =
        Ideal.map
          (Algebra.TensorProduct.includeRight : B →ₐ[k] (A ⧸ maximalIdeal A) ⊗[k] B).toRingHom
          (maximalIdeal B) := by
            rw [hcomp]

/-- Helper for Lemma 15.108.4: the closed-point ideal is the sum, equivalently the supremum, of
the left and right maximal-ideal images in the tensor product. -/
private theorem strictHenselianTensorClosedPointIdeal_eq_sup :
    (strictHenselianTensorClosedPointIdeal : Ideal (A ⊗[k] B)) =
      Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
        (maximalIdeal A) ⊔
      Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
        (maximalIdeal B) := by
  rw [strictHenselianTensorClosedPointIdeal, Ideal.add_eq_sup]

/-- Helper for Lemma 15.108.4: quotienting `A ⊗[k] B` by the closed-point ideal identifies with
the tensor product of the residue fields. -/
noncomputable abbrev strictHenselianTensor_closedPoint_quotient_equiv_residueField_tensor :
    ((A ⊗[k] B) ⧸ strictHenselianTensorClosedPointIdeal) ≃ₐ[k]
      ResidueField A ⊗[k] ResidueField B :=
  let Ileft :=
    Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom
      (maximalIdeal A)
  let Iright :=
    Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom
      (maximalIdeal B)
  let eDouble :
      (((A ⊗[k] B) ⧸ Ileft) ⧸ Ideal.map (Ideal.Quotient.mk Ileft) Iright) ≃ₐ[k]
        ((A ⊗[k] B) ⧸ strictHenselianTensorClosedPointIdeal) :=
    AlgEquiv.ofRingEquiv
      (f := (DoubleQuot.quotQuotEquivQuotSup Ileft Iright).trans <|
        Ideal.quotEquivOfEq (strictHenselianTensorClosedPointIdeal_eq_sup (k := k) (A := A)
          (B := B)).symm)
      (fun _ ↦ rfl)
  let eTransport :
      (((A ⊗[k] B) ⧸ Ileft) ⧸ Ideal.map (Ideal.Quotient.mk Ileft) Iright) ≃ₐ[k]
        (((A ⧸ maximalIdeal A) ⊗[k] B) ⧸
          Ideal.map
            (Algebra.TensorProduct.includeRight : B →ₐ[k] (A ⧸ maximalIdeal A) ⊗[k] B).toRingHom
            (maximalIdeal B)) :=
    Ideal.quotientEquivAlg
      (Ideal.map (Ideal.Quotient.mk Ileft) Iright)
      (Ideal.map
        (Algebra.TensorProduct.includeRight : B →ₐ[k] (A ⧸ maximalIdeal A) ⊗[k] B).toRingHom
        (maximalIdeal B))
      (strictHenselianTensor_leftQuotTensorAlgEquiv (k := k) (A := A) (B := B))
      (strictHenselianTensor_rightClosedPointIdeal_image_under_leftQuotTensor
        (k := k) (A := A) (B := B))
  let eRight :
      (((A ⧸ maximalIdeal A) ⊗[k] B) ⧸
          Ideal.map
            (Algebra.TensorProduct.includeRight : B →ₐ[k] (A ⧸ maximalIdeal A) ⊗[k] B).toRingHom
            (maximalIdeal B)) ≃ₐ[k]
        (A ⧸ maximalIdeal A) ⊗[k] (B ⧸ maximalIdeal B) :=
    AlgEquiv.restrictScalars k <|
      (Algebra.TensorProduct.tensorQuotientEquiv
        (R := k) (S := A ⧸ maximalIdeal A) (T := B) (A := A ⧸ maximalIdeal A)
        (maximalIdeal B)).symm
  let eResidue :
      (A ⧸ maximalIdeal A) ⊗[k] (B ⧸ maximalIdeal B) ≃ₐ[k]
        ResidueField A ⊗[k] ResidueField B :=
    Algebra.TensorProduct.congr
      (maximalIdealQuotientResidueFieldAlgEquiv (k := k) (R := A))
      (maximalIdealQuotientResidueFieldAlgEquiv (k := k) (R := B))
  eDouble.symm.trans <| eTransport.trans <| eRight.trans eResidue

-- Proof sketch: the residue-field identifications make the closed fiber of
-- `A ⊗[k] B → ResidueField A ⊗[k] ResidueField B` canonically the field `k`, so the closed-point
-- ideal is the kernel of a map to a field and hence prime.
/-- The closed-point ideal in `A ⊗[k] B` is prime once the residue fields of `A` and `B` are
identified with `k` as `k`-algebras. -/
theorem strictHenselianTensorClosedPointIdeal_isPrime
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) :
    (strictHenselianTensorClosedPointIdeal : Ideal (A ⊗[k] B)).IsPrime := by
  let eClosed :=
    strictHenselianTensor_closedPoint_quotient_equiv_residueField_tensor
      (k := k) (A := A) (B := B)
  let eResidue :
      ResidueField A ⊗[k] ResidueField B ≃ₐ[k] k :=
    (Algebra.TensorProduct.congr hκA hκB).trans (Algebra.TensorProduct.lid k k)
  let eTotal : ((A ⊗[k] B) ⧸ strictHenselianTensorClosedPointIdeal) ≃ₐ[k] k :=
    eClosed.trans eResidue
  -- Transport the field structure of `k` across the quotient equivalence.
  letI : Field ((A ⊗[k] B) ⧸ strictHenselianTensorClosedPointIdeal) :=
    eTotal.toRingEquiv.field
  -- A quotient by an ideal is a field exactly when the ideal is maximal, hence prime.
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient
    (strictHenselianTensorClosedPointIdeal : Ideal (A ⊗[k] B))).mp inferInstance

/-- The closed point of `Spec (A ⊗[k] B)` cut out by `m_A ⊗ B + A ⊗ m_B`. -/
abbrev strictHenselianTensorClosedPoint
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) :
    PrimeSpectrum (A ⊗[k] B) :=
  ⟨strictHenselianTensorClosedPointIdeal, strictHenselianTensorClosedPointIdeal_isPrime hκA hκB⟩

instance strictHenselianTensorClosedPoint_isPrime
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) :
    (strictHenselianTensorClosedPoint hκA hκB).asIdeal.IsPrime :=
  (strictHenselianTensorClosedPoint hκA hκB).isPrime

/-- The canonical localization of `A ⊗[k] B` at its closed point. -/
abbrev strictHenselianTensorClosedPointLocalization
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k) : Type u :=
  Localization.AtPrime (strictHenselianTensorClosedPoint hκA hκB).asIdeal

end ClosedPoint

section StrictHenselization

variable [StrictHenselianLocalRing A] [StrictHenselianLocalRing B]

section

variable (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k)

variable [CommRing C]
variable [Algebra (strictHenselianTensorClosedPointLocalization hκA hκB) C]

/-- The map from `A` to the chosen strict henselization of the closed-point localization of
`A ⊗[k] B`. -/
abbrev strictHenselianTensorStrictHenselizationLeftMap : A →+* C :=
  (algebraMap (strictHenselianTensorClosedPointLocalization hκA hκB) C).comp <|
    (algebraMap (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB)).comp <|
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom

/-- The map from `B` to the chosen strict henselization of the closed-point localization of
`A ⊗[k] B`. -/
abbrev strictHenselianTensorStrictHenselizationRightMap : B →+* C :=
  (algebraMap (strictHenselianTensorClosedPointLocalization hκA hκB) C).comp <|
    (algebraMap (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB)).comp <|
      (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom

/-- Helper for Lemma 15.108.4: the contraction of a minimal prime along a flat ring map is again
a minimal prime. -/
lemma comap_mem_minimalPrimes_of_flat_minimalPrime
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    (r : minimalPrimes S) :
    Ideal.comap φ r.1 ∈ minimalPrimes R := by
  let _ : Algebra R S := φ.toAlgebra
  have hφ_alg : (algebraMap R S).Flat := by
    -- Repackage the chosen ring map as the ambient algebra map so the standard going-down API
    -- applies without extra transport noise.
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have hcomap :
      Ideal.comap (algebraMap R S) r.1 ∈ minimalPrimes R := by
    let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hφ_alg
    refine ⟨⟨Ideal.minimalPrimes_isPrime r.2, bot_le⟩, ?_⟩
    intro J hJ hJ_le
    by_cases hEq : Ideal.comap (algebraMap R S) r.1 = J
    · exact hEq.le
    · let _ : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
      let _ : J.IsPrime := hJ.1
      let _ : r.1.IsPrime := Ideal.minimalPrimes_isPrime r.2
      let _ : r.1.LiesOver (Ideal.comap (algebraMap R S) r.1) := ⟨rfl⟩
      have hJ_lt : J < Ideal.comap (algebraMap R S) r.1 :=
        lt_of_le_of_ne hJ_le (Ne.symm hEq)
      -- Going down produces a smaller prime below `r`, contradicting minimality of `r`.
      obtain ⟨Q, hQ_lt, hQ_prime, _⟩ :=
        Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S) (Q := r.1) hJ_lt
      have hr_le_Q : r.1 ≤ Q :=
        r.2.2 ⟨hQ_prime, bot_le⟩ hQ_lt.le
      exact (hQ_lt.not_ge hr_le_Q).elim
  -- Translate back from the algebra-map presentation to the original ring-hom statement.
  simpa [RingHom.algebraMap_toAlgebra] using hcomap

-- Proof sketch: once `C` is a strict henselization of the canonical closed-point localization of
-- `A ⊗[k] B`, a minimal prime of `C` contracts to minimal primes of `A` and `B`.
/-- The contraction of a minimal prime of `C` along the left map `A → C` is a minimal prime
of `A`. -/
theorem strictHenselianTensorStrictHenselization_left_mem_minimalPrimes
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (r : minimalPrimes C) :
    Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1 ∈
      minimalPrimes A := by
  have htensorModule : Module.Flat A (A ⊗[k] B) := by
    -- Base change from the field `k` gives flatness of the left tensor-factor inclusion.
    simpa using (Module.Flat.baseChange (R := k) (S := A) (M := B))
  have htensor :
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom.Flat := by
    -- Re-express the tensor inclusion as the ambient algebra map of the base-changed algebra.
    have halgebraMap : (algebraMap A (A ⊗[k] B)).Flat :=
      RingHom.flat_algebraMap_iff.mpr htensorModule
    simpa [RingHom.algebraMap_toAlgebra] using halgebraMap
  have hlocalizationModule :
      Module.Flat (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB) :=
    IsLocalization.flat _ (strictHenselianTensorClosedPoint hκA hκB).asIdeal.primeCompl
  have hlocalization :
      (algebraMap (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB)).Flat :=
    RingHom.flat_algebraMap_iff.mpr hlocalizationModule
  have hstrict :
      (algebraMap (strictHenselianTensorClosedPointLocalization hκA hκB) C).Flat :=
    strictHenselizationMap_faithfullyFlat.flat
  have hcomp :
      (strictHenselianTensorStrictHenselizationLeftMap hκA hκB).Flat := by
    -- Compose the tensor, localization, and strict-henselization flat maps.
    simpa [strictHenselianTensorStrictHenselizationLeftMap] using
      RingHom.Flat.comp (RingHom.Flat.comp htensor hlocalization) hstrict
  -- The generic going-down contraction lemma now applies to the full left structural map.
  exact comap_mem_minimalPrimes_of_flat_minimalPrime
    (φ := strictHenselianTensorStrictHenselizationLeftMap hκA hκB) hcomp r

/-- The contraction of a minimal prime of `C` along the right map `B → C` is a minimal prime
of `B`. -/
theorem strictHenselianTensorStrictHenselization_right_mem_minimalPrimes
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (r : minimalPrimes C) :
    Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1 ∈
      minimalPrimes B := by
  have htensorModule : Module.Flat B (A ⊗[k] B) := by
    -- Base change from the field `k` gives flatness of the right tensor-factor inclusion.
    simpa using (Module.Flat.baseChange (R := k) (S := B) (M := A))
  have htensor :
      (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom.Flat := by
    -- Re-express the tensor inclusion as the ambient algebra map of the base-changed algebra.
    have halgebraMap : (algebraMap B (A ⊗[k] B)).Flat :=
      RingHom.flat_algebraMap_iff.mpr htensorModule
    simpa [RingHom.algebraMap_toAlgebra] using halgebraMap
  have hlocalizationModule :
      Module.Flat (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB) :=
    IsLocalization.flat _ (strictHenselianTensorClosedPoint hκA hκB).asIdeal.primeCompl
  have hlocalization :
      (algebraMap (A ⊗[k] B) (strictHenselianTensorClosedPointLocalization hκA hκB)).Flat :=
    RingHom.flat_algebraMap_iff.mpr hlocalizationModule
  have hstrict :
      (algebraMap (strictHenselianTensorClosedPointLocalization hκA hκB) C).Flat :=
    strictHenselizationMap_faithfullyFlat.flat
  have hcomp :
      (strictHenselianTensorStrictHenselizationRightMap hκA hκB).Flat := by
    -- Compose the tensor, localization, and strict-henselization flat maps.
    simpa [strictHenselianTensorStrictHenselizationRightMap] using
      RingHom.Flat.comp (RingHom.Flat.comp htensor hlocalization) hstrict
  -- The generic going-down contraction lemma now applies to the full right structural map.
  exact comap_mem_minimalPrimes_of_flat_minimalPrime
    (φ := strictHenselianTensorStrictHenselizationRightMap hκA hκB) hcomp r

/-- A minimal prime of the chosen strict henselization of the closed-point localization of
`A ⊗[k] B` determines a pair of contracted minimal primes in `A` and `B`. -/
abbrev strictHenselianTensorMinimalPrimePair
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (r : minimalPrimes C) :
    minimalPrimes A × minimalPrimes B :=
  ( ⟨ Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1
      , strictHenselianTensorStrictHenselization_left_mem_minimalPrimes hκA hκB r ⟩
  , ⟨ Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1
      , strictHenselianTensorStrictHenselization_right_mem_minimalPrimes hκA hκB r ⟩ )

/-- Helper for Lemma 15.108.4: the ideal of `C` attached to a pair of minimal primes of `A` and
`B`. This is the source-faithful fiber ideal obtained by quotienting along the two contractions.
-/
abbrev strictHenselianTensorPairIdeal
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) : Ideal C :=
  Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 +
    Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1

/-- Helper for Lemma 15.108.4: if a minimal prime of `C` contracts to `(p, q)`, then it contains
the corresponding pair ideal. -/
lemma strictHenselianTensorPairIdeal_le_of_pair_eq
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    {r : minimalPrimes C} {p : minimalPrimes A} {q : minimalPrimes B}
    (hpair : strictHenselianTensorMinimalPrimePair hκA hκB r = (p, q)) :
    strictHenselianTensorPairIdeal hκA hκB p q ≤ r.1 := by
  -- Read off the two contraction equalities from the pair equality, then map both factors into
  -- `r` and sum the resulting containments.
  have hleft :
      Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1 = p.1 := by
    exact congrArg Subtype.val (congrArg Prod.fst hpair)
  have hright :
      Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1 = q.1 := by
    exact congrArg Subtype.val (congrArg Prod.snd hpair)
  refine sup_le ?_ ?_
  · -- The left contracted minimal prime is exactly `p`, so its image lies in `r`.
    exact Ideal.map_le_iff_le_comap.mpr <| by simpa [hleft]
  · -- The same containment holds for the right contracted minimal prime.
    exact Ideal.map_le_iff_le_comap.mpr <| by simpa [hright]

/-- Helper for Lemma 15.108.4: a minimal prime of `C` containing `I` descends to a minimal prime
of the quotient `C ⧸ I`. -/
lemma strictHenselianTensor_map_mem_minimalPrimes_quotient_of_le
    {I : Ideal C} {r : minimalPrimes C} (hI : I ≤ r.1) :
    Ideal.map (Ideal.Quotient.mk I) r.1 ∈ minimalPrimes (C ⧸ I) := by
  -- First regard `r` as a minimal prime over the ideal `I`.
  have hr_over_I : r.1 ∈ I.minimalPrimes := by
    refine ⟨⟨Ideal.minimalPrimes_isPrime r.2, hI⟩, ?_⟩
    intro J hJ hJ_le
    exact r.2.2 ⟨hJ.1, bot_le⟩ hJ_le
  -- Then transport that minimal prime through the quotient map.
  have hr_map :
      Ideal.map (Ideal.Quotient.mk I) r.1 ∈
        (Ideal.map (Ideal.Quotient.mk I) I).minimalPrimes := by
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I]
    exact ⟨r.1, hr_over_I, rfl⟩
  simpa [Ideal.mk_ker] using hr_map

/-- Helper for Lemma 15.108.4: once each pair quotient `C / I_{p,q}` has a unique minimal prime,
the contraction map from minimal primes of `C` to pairs of minimal primes of `A` and `B` is
injective. -/
theorem strictHenselianTensorMinimalPrimePair_injective_of_pairQuotient_uniqueMinimalPrime
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (huniq :
      ∀ p : minimalPrimes A, ∀ q : minimalPrimes B,
        ∃! s : Ideal (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q),
          s ∈ minimalPrimes (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)) :
    Function.Injective
      (fun r : minimalPrimes C ↦ strictHenselianTensorMinimalPrimePair hκA hκB r) := by
  intro r₁ r₂ hpair
  let pq := strictHenselianTensorMinimalPrimePair hκA hκB r₁
  let I := strictHenselianTensorPairIdeal hκA hκB pq.1 pq.2
  -- Both minimal primes lie over the same pair ideal.
  have hI₁ : I ≤ r₁.1 := by
    exact strictHenselianTensorPairIdeal_le_of_pair_eq (hκA := hκA) (hκB := hκB) (r := r₁) rfl
  have hI₂ : I ≤ r₂.1 := by
    exact strictHenselianTensorPairIdeal_le_of_pair_eq (hκA := hκA) (hκB := hκB) (r := r₂) <| by
      simpa [pq] using hpair
  have hr₁ :
      Ideal.map (Ideal.Quotient.mk I) r₁.1 ∈ minimalPrimes (C ⧸ I) :=
    strictHenselianTensor_map_mem_minimalPrimes_quotient_of_le hI₁
  have hr₂ :
      Ideal.map (Ideal.Quotient.mk I) r₂.1 ∈ minimalPrimes (C ⧸ I) :=
    strictHenselianTensor_map_mem_minimalPrimes_quotient_of_le hI₂
  rcases huniq pq.1 pq.2 with ⟨s, hs, hs_unique⟩
  have hs₁ : Ideal.map (Ideal.Quotient.mk I) r₁.1 = s := hs_unique _ hr₁
  have hs₂ : Ideal.map (Ideal.Quotient.mk I) r₂.1 = s := hs_unique _ hr₂
  apply Subtype.ext
  -- Pull the quotient-ideal equality back along `Ideal.Quotient.mk`.
  have hmap :
      Ideal.map (Ideal.Quotient.mk I) r₁.1 =
        Ideal.map (Ideal.Quotient.mk I) r₂.1 := hs₁.trans hs₂.symm
  have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hmap
  simpa [Ideal.comap_map_mk hI₁, Ideal.comap_map_mk hI₂] using hcomap

/-- Helper for Lemma 15.108.4: a domain has exactly one minimal prime, namely `⊥`. -/
lemma existsUnique_minimalPrime_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R] :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  -- The zero ideal is prime in a domain, so it is the unique minimal prime.
  have hsingle : minimalPrimes R = ({⊥} : Set (Ideal R)) := by
    simpa [minimalPrimes] using
      (show (⊥ : Ideal R).minimalPrimes = ({⊥} : Set (Ideal R)) from
        Ideal.minimalPrimes_eq_subsingleton_self)
  refine ⟨⊥, ?_, ?_⟩
  · rw [hsingle]
    simp
  · intro p hp
    rw [hsingle] at hp
    simpa using hp

/-- Helper for Lemma 15.108.4: if a ring has a unique minimal prime, then every localization at a
prime ideal also has a unique minimal prime. -/
lemma existsUnique_minimalPrime_localizationAtPrime_of_existsUnique_minimalPrime
    {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime]
    (huniq : ∃! p : Ideal R, p ∈ minimalPrimes R) :
    ∃! q : Ideal (Localization.AtPrime P), q ∈ minimalPrimes (Localization.AtPrime P) := by
  let Rp := Localization.AtPrime P
  rcases huniq with ⟨p, hp, hp_unique⟩
  have hp_le_P : p ≤ P := by
    -- A unique minimal prime lies under every prime of the source ring.
    exact hp.2.2 ⟨inferInstance, bot_le⟩
  have hp_disjoint : Disjoint P.primeCompl p := by
    -- Elements inverted in the localization cannot lie in a prime below `P`.
    refine Set.disjoint_left.mpr ?_
    intro x hxP hxq
    exact hxP (hp_le_P hxq)
  let pRp : Ideal Rp := Ideal.map (algebraMap R Rp) p
  have hp_comap :
      Ideal.comap (algebraMap R Rp) pRp = p := by
    -- Localizing away from a prime preserves every smaller prime ideal exactly.
    simpa [Rp] using
      IsLocalization.comap_map_of_isPrime_disjoint
        P.primeCompl Rp (Ideal.minimalPrimes_isPrime hp) hp_disjoint
  have hpRp : pRp ∈ minimalPrimes Rp := by
    -- Minimal primes localize to minimal primes.
    have hpRp' :
        pRp ∈ (Ideal.map (algebraMap R Rp) (⊥ : Ideal R)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map P.primeCompl Rp (⊥ : Ideal R)]
      change Ideal.comap (algebraMap R Rp) pRp ∈ minimalPrimes R
      simpa [hp_comap]
    simpa [minimalPrimes, Ideal.map_bot] using hpRp'
  refine ⟨pRp, hpRp, ?_⟩
  intro q hq
  have hflat :
      (algebraMap R Rp).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr <| IsLocalization.flat Rp P.primeCompl
  let qmin : minimalPrimes Rp := ⟨q, hq⟩
  have hq_comap_min :
      Ideal.comap (algebraMap R Rp) q ∈ minimalPrimes R :=
    comap_mem_minimalPrimes_of_flat_minimalPrime
      (φ := algebraMap R Rp) hflat qmin
  have hq_comap_eq : Ideal.comap (algebraMap R Rp) q = p := hp_unique _ hq_comap_min
  -- Every localization prime is the extension of its contraction.
  calc
    q = Ideal.map (algebraMap R Rp) (Ideal.comap (algebraMap R Rp) q) := by
      simpa [Rp] using (IsLocalization.map_comap P.primeCompl Rp q).symm
    _ = pRp := by
      simp [pRp, hq_comap_eq]

/-- Helper for Lemma 15.108.4: over a separably closed field, the tensor product of two domains
has a unique minimal prime. -/
lemma existsUnique_minimalPrime_tensorProduct_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsSepClosed k] [IsDomain R] [IsDomain S] :
    ∃! p : Ideal (R ⊗[k] S), p ∈ minimalPrimes (R ⊗[k] S) := by
  -- First reduce each factor to its unique zero minimal prime, then invoke Lemma `10.47.2`.
  exact existsUnique_minimalPrime_tensorProduct
    (k := k)
    (R := R)
    (S := S)
    (existsUnique_minimalPrime_of_isDomain (R := R))
    (existsUnique_minimalPrime_of_isDomain (R := S))

/-- Helper for Lemma 15.108.4: after localizing the tensor product of two domains over a
separably closed field at any prime, the localized ring still has a unique minimal prime. -/
lemma existsUnique_minimalPrime_localizationAtPrime_tensorProduct_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsSepClosed k] [IsDomain R] [IsDomain S]
    (P : Ideal (R ⊗[k] S)) [P.IsPrime] :
    ∃! q : Ideal (Localization.AtPrime P), q ∈ minimalPrimes (Localization.AtPrime P) := by
  -- Apply the localization-preservation lemma to the unique-minimal-prime tensor product owner.
  exact
    existsUnique_minimalPrime_localizationAtPrime_of_existsUnique_minimalPrime
      (P := P) (existsUnique_minimalPrime_tensorProduct_of_isDomain (k := k) (R := R) (S := S))

/-- Helper for Lemma 15.108.4: the left structural map `A → C` kills `p` after passing to the
pair quotient `C / I_{p,q}`. -/
lemma strictHenselianTensor_pairIdeal_left_le_ker
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    p.1 ≤
      RingHom.ker
        (((Ideal.Quotient.mk (strictHenselianTensorPairIdeal hκA hκB p q)).comp
          (strictHenselianTensorStrictHenselizationLeftMap hκA hκB)) : A →+*
            C ⧸ strictHenselianTensorPairIdeal hκA hκB p q) := by
  -- The pair ideal contains the left image of `p`, so the quotient map annihilates `p`.
  intro x hx
  change (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) x ∈
    strictHenselianTensorPairIdeal hκA hκB p q
  have hmem :
      (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) x ∈
        Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 :=
    Ideal.mem_map_of_mem _ hx
  exact
    (show Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ≤
        strictHenselianTensorPairIdeal hκA hκB p q by
          simpa [strictHenselianTensorPairIdeal, Ideal.add_eq_sup] using
            (show
                Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ≤
                  Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ⊔
                    Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1
              from le_sup_left))
      hmem

/-- Helper for Lemma 15.108.4: the right structural map `B → C` kills `q` after passing to the
pair quotient `C / I_{p,q}`. -/
lemma strictHenselianTensor_pairIdeal_right_le_ker
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    q.1 ≤
      RingHom.ker
        (((Ideal.Quotient.mk (strictHenselianTensorPairIdeal hκA hκB p q)).comp
          (strictHenselianTensorStrictHenselizationRightMap hκA hκB)) : B →+*
            C ⧸ strictHenselianTensorPairIdeal hκA hκB p q) := by
  -- The pair ideal contains the right image of `q`, so the quotient map annihilates `q`.
  intro x hx
  change (strictHenselianTensorStrictHenselizationRightMap hκA hκB) x ∈
    strictHenselianTensorPairIdeal hκA hκB p q
  have hmem :
      (strictHenselianTensorStrictHenselizationRightMap hκA hκB) x ∈
        Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1 :=
    Ideal.mem_map_of_mem _ hx
  exact
    (show Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1 ≤
        strictHenselianTensorPairIdeal hκA hκB p q by
          simpa [strictHenselianTensorPairIdeal, Ideal.add_eq_sup] using
            (show
                Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1 ≤
                  Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ⊔
                    Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1
              from le_sup_right))
      hmem

/-- Helper for Lemma 15.108.4: the left quotient-domain map into `C / I_{p,q}` induced by the
structural map `A → C`. -/
abbrev strictHenselianTensorPairQuotientLeftMap
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    A ⧸ p.1 →+* C ⧸ strictHenselianTensorPairIdeal hκA hκB p q :=
  Ideal.Quotient.lift p.1
    (((Ideal.Quotient.mk (strictHenselianTensorPairIdeal hκA hκB p q)).comp
      (strictHenselianTensorStrictHenselizationLeftMap hκA hκB)) : A →+*
        C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)
    (strictHenselianTensor_pairIdeal_left_le_ker (hκA := hκA) (hκB := hκB) p q)

/-- Helper for Lemma 15.108.4: the right quotient-domain map into `C / I_{p,q}` induced by the
structural map `B → C`. -/
abbrev strictHenselianTensorPairQuotientRightMap
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    B ⧸ q.1 →+* C ⧸ strictHenselianTensorPairIdeal hκA hκB p q :=
  Ideal.Quotient.lift q.1
    (((Ideal.Quotient.mk (strictHenselianTensorPairIdeal hκA hκB p q)).comp
      (strictHenselianTensorStrictHenselizationRightMap hκA hκB)) : B →+*
        C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)
    (strictHenselianTensor_pairIdeal_right_le_ker (hκA := hκA) (hκB := hκB) p q)

/-- Helper for Lemma 15.108.4: the quotient `C / I_{p,q}` should admit a source-faithful
intermediate owner `D` through which both quotient-domain maps factor as composites of flat maps.
The intended `D` is the closed-point localization of the tensor product of the quotient domains,
and the remaining blocker is to construct this owner together with the displayed factorization
equalities. -/
lemma strictHenselianTensor_pairQuotient_has_flat_factorization
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra (A ⧸ p.1) D) (_ : Algebra (B ⧸ q.1) D)
      (_ : Algebra D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q))
      (_ : IsScalarTower (A ⧸ p.1) D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q))
      (_ : IsScalarTower (B ⧸ q.1) D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)),
      (algebraMap (A ⧸ p.1) D).Flat ∧
        (algebraMap (B ⧸ q.1) D).Flat ∧
        (algebraMap D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)).Flat ∧
        strictHenselianTensorPairQuotientLeftMap
            (hκA := hκA) (hκB := hκB) (C := C) p q =
          ((algebraMap D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)).comp
            (algebraMap (A ⧸ p.1) D)) ∧
        strictHenselianTensorPairQuotientRightMap
            (hκA := hκA) (hκB := hκB) (C := C) p q =
          ((algebraMap D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)).comp
            (algebraMap (B ⧸ q.1) D)) := by
  -- Route correction: package the source-faithful quotient/localization comparison as a single
  -- owner-level factorization theorem, so downstream flatness is just composition of flat maps.
  -- TODO: take `D` to be the closed-point localization of `((A ⧸ p.1) ⊗[k] (B ⧸ q.1))`, prove
  -- `C / I_{p,q}` is its strict henselization, and identify both quotient-domain maps with the
  -- composites through the canonical tensor inclusions and localization map.
  sorry

/-- Helper for Lemma 15.108.4: the induced quotient-domain maps to `C / I_{p,q}` are flat. This
is the remaining quotient-world bridge needed to contract minimal primes through the pair
quotient. -/
lemma strictHenselianTensor_pairQuotient_maps_flat
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    (strictHenselianTensorPairQuotientLeftMap (hκA := hκA) (hκB := hκB) (C := C) p q).Flat ∧
      (strictHenselianTensorPairQuotientRightMap (hκA := hκA) (hκB := hκB) (C := C) p q).Flat := by
  rcases strictHenselianTensor_pairQuotient_has_flat_factorization
      (hκA := hκA) (hκB := hκB) (C := C) p q with
    ⟨D, _, _, _, _, _, _, hleft_flat, hright_flat, hquot_flat, hleft_eq, hright_eq⟩
  constructor
  · -- Once the left quotient map factors through the intermediate owner `D`, flatness is the
    -- composite of the flat map from `A / p` into `D` and the flat comparison `D → C / I_{p,q}`.
    have hcomp :
        (((algebraMap D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)).comp
          (algebraMap (A ⧸ p.1) D))).Flat :=
      RingHom.Flat.comp hleft_flat hquot_flat
    simpa [hleft_eq] using hcomp
  · -- The same factorization argument applies to the right quotient-domain map.
    have hcomp :
        (((algebraMap D (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q)).comp
          (algebraMap (B ⧸ q.1) D))).Flat :=
      RingHom.Flat.comp hright_flat hquot_flat
    simpa [hright_eq] using hcomp

/-- Helper for Lemma 15.108.4: for a fixed pair `(p, q)`, the quotient `C / I_{p,q}` should be
shown to have a unique minimal prime by comparing it with the strict henselization of the
localized tensor product of the quotient domains. -/
lemma strictHenselianTensor_pair_quotient_existsUnique_minimalPrime
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    ∃! s : Ideal (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q),
      s ∈ minimalPrimes (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q) := by
  -- Route correction: now that the flat factorization is isolated above, the remaining work is the
  -- genuine source normalization step on the quotient-domain owner itself, not more contraction
  -- bookkeeping inside `C / I_{p,q}`.
  -- TODO: instantiate
  -- `existsUnique_minimalPrime_localizationAtPrime_tensorProduct_of_isDomain`
  -- on `((A ⧸ p.1) ⊗[k] (B ⧸ q.1))` using the quotient-domain local structures and the closed-point
  -- primality statement, then transport that unique minimal prime across the quotient
  -- strict-henselization comparison packaged by
  -- `strictHenselianTensor_pairQuotient_has_flat_factorization`.
  sorry

/-- Helper for Lemma 15.108.4: a prime ideal minimal over `I_{p,q}` should contract back to the
chosen pair `(p, q)` by passing to the quotient and using the induced flat maps from the quotient
domains. -/
lemma strictHenselianTensor_pairIdeal_minimalOver_contract_pair
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B)
    {r : Ideal C}
    (hr : r ∈ (strictHenselianTensorPairIdeal hκA hκB p q).minimalPrimes) :
    Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r = p.1 ∧
      Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r = q.1 := by
  let I := strictHenselianTensorPairIdeal hκA hκB p q
  let φL := strictHenselianTensorPairQuotientLeftMap (hκA := hκA) (hκB := hκB) (C := C) p q
  let φR := strictHenselianTensorPairQuotientRightMap (hκA := hκA) (hκB := hκB) (C := C) p q
  have hflat : φL.Flat ∧ φR.Flat :=
    strictHenselianTensor_pairQuotient_maps_flat (hκA := hκA) (hκB := hκB) (C := C) p q
  have hp_prime : p.1.IsPrime := Ideal.minimalPrimes_isPrime p.2
  have hq_prime : q.1.IsPrime := Ideal.minimalPrimes_isPrime q.2
  let _ : IsDomain (A ⧸ p.1) := Ideal.Quotient.isDomain p.1
  let _ : IsDomain (B ⧸ q.1) := Ideal.Quotient.isDomain q.1
  have hrbar_mem :
      Ideal.map (Ideal.Quotient.mk I) r ∈ minimalPrimes (C ⧸ I) := by
    have hr_map :
        Ideal.map (Ideal.Quotient.mk I) r ∈
          (Ideal.map (Ideal.Quotient.mk I) I).minimalPrimes := by
      rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I]
      exact ⟨r, hr, rfl⟩
    simpa [Ideal.mk_ker] using hr_map
  let rbar : minimalPrimes (C ⧸ I) := ⟨Ideal.map (Ideal.Quotient.mk I) r, hrbar_mem⟩
  have hleft_min :
      Ideal.comap φL rbar.1 ∈ minimalPrimes (A ⧸ p.1) :=
    comap_mem_minimalPrimes_of_flat_minimalPrime (φ := φL) hflat.1 rbar
  have hright_min :
      Ideal.comap φR rbar.1 ∈ minimalPrimes (B ⧸ q.1) :=
    comap_mem_minimalPrimes_of_flat_minimalPrime (φ := φR) hflat.2 rbar
  have hleft_zero :
      Ideal.comap φL rbar.1 = (⊥ : Ideal (A ⧸ p.1)) := by
    have hsingle :
        minimalPrimes (A ⧸ p.1) = ({⊥} : Set (Ideal (A ⧸ p.1))) := by
      simpa [minimalPrimes] using
        (show (⊥ : Ideal (A ⧸ p.1)).minimalPrimes = ({⊥} : Set (Ideal (A ⧸ p.1))) from
          Ideal.minimalPrimes_eq_subsingleton_self)
    rw [hsingle] at hleft_min
    simpa using hleft_min
  have hright_zero :
      Ideal.comap φR rbar.1 = (⊥ : Ideal (B ⧸ q.1)) := by
    have hsingle :
        minimalPrimes (B ⧸ q.1) = ({⊥} : Set (Ideal (B ⧸ q.1))) := by
      simpa [minimalPrimes] using
        (show (⊥ : Ideal (B ⧸ q.1)).minimalPrimes = ({⊥} : Set (Ideal (B ⧸ q.1))) from
          Ideal.minimalPrimes_eq_subsingleton_self)
    rw [hsingle] at hright_min
    simpa using hright_min
  have hleft_ge :
      p.1 ≤ Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r := by
    refine Ideal.map_le_iff_le_comap.mp ?_
    exact le_trans
      (show Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ≤ I by
        simpa [I, strictHenselianTensorPairIdeal, Ideal.add_eq_sup] using
          (show
              Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ≤
                Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ⊔
                  Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1
            from le_sup_left))
      hr.1.2
  have hright_ge :
      q.1 ≤ Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r := by
    refine Ideal.map_le_iff_le_comap.mp ?_
    exact le_trans
      (show Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1 ≤ I by
        simpa [I, strictHenselianTensorPairIdeal, Ideal.add_eq_sup] using
          (show
              Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1 ≤
                Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ⊔
                  Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1
            from le_sup_right))
      hr.1.2
  have hleft_le :
      Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r ≤ p.1 := by
    intro x hx
    have hxbar :
        Ideal.Quotient.mk p.1 x ∈ Ideal.comap φL rbar.1 := by
      change φL (Ideal.Quotient.mk p.1 x) ∈ rbar.1
      rw [φL, Ideal.Quotient.lift_mk]
      exact Ideal.mem_map_of_mem _ hx
    have hxzero : Ideal.Quotient.mk p.1 x = 0 := by
      exact show Ideal.Quotient.mk p.1 x ∈ (⊥ : Ideal (A ⧸ p.1)) by
        simpa [hleft_zero] using hxbar
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
  have hright_le :
      Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r ≤ q.1 := by
    intro x hx
    have hxbar :
        Ideal.Quotient.mk q.1 x ∈ Ideal.comap φR rbar.1 := by
      change φR (Ideal.Quotient.mk q.1 x) ∈ rbar.1
      rw [φR, Ideal.Quotient.lift_mk]
      exact Ideal.mem_map_of_mem _ hx
    have hxzero : Ideal.Quotient.mk q.1 x = 0 := by
      exact show Ideal.Quotient.mk q.1 x ∈ (⊥ : Ideal (B ⧸ q.1)) by
        simpa [hright_zero] using hxbar
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
  -- Compare both contractions by combining the obvious containments with the quotient-domain
  -- vanishing just proved.
  exact ⟨le_antisymm hleft_le hleft_ge, le_antisymm hright_le hright_ge⟩

/-- Helper for Lemma 15.108.4: if a minimal prime of `C` contains the pair ideal attached to
`(p, q)`, then its contracted pair is exactly `(p, q)`. -/
lemma strictHenselianTensorMinimalPrimePair_eq_of_pairIdeal_le
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    {r : minimalPrimes C} {p : minimalPrimes A} {q : minimalPrimes B}
    (hI : strictHenselianTensorPairIdeal hκA hκB p q ≤ r.1) :
    strictHenselianTensorMinimalPrimePair hκA hκB r = (p, q) := by
  -- Compare the left contractions using the minimality of the contracted prime of `r`.
  have hleft_le :
      p.1 ≤ Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1 := by
    refine Ideal.map_le_iff_le_comap.mp ?_
    exact le_trans (show Ideal.map (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) p.1 ≤
        strictHenselianTensorPairIdeal hκA hκB p q from le_sup_left) hI
  have hleft_eq :
      Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1 = p.1 := by
    have hleft_min :
        Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1 ∈
          minimalPrimes A :=
      strictHenselianTensorStrictHenselization_left_mem_minimalPrimes hκA hκB r
    have hleft_ge :
        Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r.1 ≤ p.1 :=
      hleft_min.2.2 ⟨Ideal.minimalPrimes_isPrime p.2, bot_le⟩ hleft_le
    exact le_antisymm hleft_ge hleft_le
  -- The same minimal-prime comparison identifies the right contractions.
  have hright_le :
      q.1 ≤ Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1 := by
    refine Ideal.map_le_iff_le_comap.mp ?_
    exact le_trans (show Ideal.map (strictHenselianTensorStrictHenselizationRightMap hκA hκB) q.1 ≤
        strictHenselianTensorPairIdeal hκA hκB p q from le_sup_right) hI
  have hright_eq :
      Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1 = q.1 := by
    have hright_min :
        Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1 ∈
          minimalPrimes B :=
      strictHenselianTensorStrictHenselization_right_mem_minimalPrimes hκA hκB r
    have hright_ge :
        Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r.1 ≤ q.1 :=
      hright_min.2.2 ⟨Ideal.minimalPrimes_isPrime q.2, bot_le⟩ hright_le
    exact le_antisymm hright_ge hright_le
  -- Package the two component equalities back into the pair equality.
  apply Prod.ext
  · apply Subtype.ext
    exact hleft_eq
  · apply Subtype.ext
    exact hright_eq

/-- Helper for Lemma 15.108.4: a prime ideal that is minimal above `I_{p,q}` is already a minimal
prime of `C` once its contractions to `A` and `B` are exactly `p` and `q`. -/
lemma strictHenselianTensor_pairIdealMinimalOver_isMinimalPrime
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B)
    {r : Ideal C}
    (hr : r ∈ (strictHenselianTensorPairIdeal hκA hκB p q).minimalPrimes)
    (hleft :
      Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r = p.1)
    (hright :
      Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r = q.1) :
    r ∈ minimalPrimes C := by
  -- Any smaller prime has the same left and right contractions, hence still contains `I_{p,q}`.
  refine ⟨hr.1.1, ?_⟩
  intro J hJ hJ_le
  have hleft_le :
      Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) J ≤ p.1 := by
    simpa [hleft] using
      Ideal.comap_mono (f := strictHenselianTensorStrictHenselizationLeftMap hκA hκB) hJ_le
  have hleft_eq :
      Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) J = p.1 := by
    have hJ_left_prime :
        (Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) J).IsPrime :=
      Ideal.comap_isPrime _ hJ.1
    have hp_le :
        p.1 ≤ Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) J :=
      p.2.2 ⟨hJ_left_prime, bot_le⟩ hleft_le
    exact le_antisymm hleft_le hp_le
  have hright_le :
      Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) J ≤ q.1 := by
    simpa [hright] using
      Ideal.comap_mono (f := strictHenselianTensorStrictHenselizationRightMap hκA hκB) hJ_le
  have hright_eq :
      Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) J = q.1 := by
    have hJ_right_prime :
        (Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) J).IsPrime :=
      Ideal.comap_isPrime _ hJ.1
    have hq_le :
        q.1 ≤ Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) J :=
      q.2.2 ⟨hJ_right_prime, bot_le⟩ hright_le
    exact le_antisymm hright_le hq_le
  have hpair_le :
      strictHenselianTensorPairIdeal hκA hκB p q ≤ J := by
    refine sup_le ?_ ?_
    · exact Ideal.map_le_iff_le_comap.mpr <| by simpa [hleft_eq]
    · exact Ideal.map_le_iff_le_comap.mpr <| by simpa [hright_eq]
  -- Minimality over `I_{p,q}` then forces the original prime `r` to lie inside `J`.
  exact hr.2 ⟨hJ.1, hpair_le⟩ hJ_le

/-- Helper for Lemma 15.108.4: once the quotient `C / I_{p,q}` has a unique minimal prime and
every prime minimal over `I_{p,q}` contracts back to `(p, q)`, there is a unique minimal prime of
`C` containing `I_{p,q}`. -/
lemma strictHenselianTensor_pairIdeal_existsUnique_minimalPrime_of_quotient
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B)
    (hquot :
      ∃! s : Ideal (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q),
        s ∈ minimalPrimes (C ⧸ strictHenselianTensorPairIdeal hκA hκB p q))
    (hcontract :
      ∀ {r : Ideal C},
        r ∈ (strictHenselianTensorPairIdeal hκA hκB p q).minimalPrimes →
          Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r = p.1 ∧
            Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r = q.1) :
    ∃! r : Ideal C, r ∈ minimalPrimes C ∧
      strictHenselianTensorPairIdeal hκA hκB p q ≤ r := by
  classical
  let I := strictHenselianTensorPairIdeal hκA hκB p q
  rcases hquot with ⟨s, hs, hs_unique⟩
  have hs_over : s ∈ (Ideal.map (Ideal.Quotient.mk I) I).minimalPrimes := by
    simpa [Ideal.mk_ker] using hs
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I] at hs_over
  rcases hs_over with ⟨r, hr_over, hr_map⟩
  have hr_contract := hcontract hr_over
  have hr_min :
      r ∈ minimalPrimes C :=
    strictHenselianTensor_pairIdealMinimalOver_isMinimalPrime
      (hκA := hκA) (hκB := hκB) p q hr_over hr_contract.1 hr_contract.2
  refine ⟨r, ⟨hr_min, hr_over.1.2⟩, ?_⟩
  intro r' hr'
  have hr'_quot :
      Ideal.map (Ideal.Quotient.mk I) r' ∈ minimalPrimes (C ⧸ I) :=
    strictHenselianTensor_map_mem_minimalPrimes_quotient_of_le hr'.2
  have hs_r' : Ideal.map (Ideal.Quotient.mk I) r' = s := hs_unique _ hr'_quot
  have hmap :
      Ideal.map (Ideal.Quotient.mk I) r = Ideal.map (Ideal.Quotient.mk I) r' :=
    hr_map.trans hs_r'.symm
  have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hmap
  simpa [Ideal.comap_map_mk hr_over.1.2, Ideal.comap_map_mk hr'.2] using hcomap

/-- Helper for Lemma 15.108.4: for each pair `(p, q)` of minimal primes of `A` and `B`, there is
exactly one minimal prime of `C` containing the corresponding pair ideal. -/
lemma strictHenselianTensor_pairIdeal_existsUnique_minimalPrime
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C]
    (p : minimalPrimes A) (q : minimalPrimes B) :
    ∃! r : Ideal C, r ∈ minimalPrimes C ∧
      strictHenselianTensorPairIdeal hκA hκB p q ≤ r := by
  let I := strictHenselianTensorPairIdeal hκA hκB p q
  -- Route correction: the remaining job is now split cleanly. It is enough to prove
  -- (1) `C ⧸ I` has a unique minimal prime and (2) every prime minimal over `I` contracts to
  -- exactly `(p, q)`, because the lifting lemma above then converts that quotient uniqueness into
  -- the required unique minimal prime of `C`.
  have hreduce :
      (∃! s : Ideal (C ⧸ I), s ∈ minimalPrimes (C ⧸ I)) ∧
        (∀ {r : Ideal C}, r ∈ I.minimalPrimes →
          Ideal.comap (strictHenselianTensorStrictHenselizationLeftMap hκA hκB) r = p.1 ∧
            Ideal.comap (strictHenselianTensorStrictHenselizationRightMap hκA hκB) r = q.1) := by
    -- Reuse the dedicated quotient-uniqueness and contraction helpers so the remaining blocker is
    -- the exact quotient comparison from the source proof, not the packaging at this call site.
    refine ⟨?_, ?_⟩
    · exact
        strictHenselianTensor_pair_quotient_existsUnique_minimalPrime
          (hκA := hκA) (hκB := hκB) (C := C) p q
    · intro r hr
      exact
        strictHenselianTensor_pairIdeal_minimalOver_contract_pair
          (hκA := hκA) (hκB := hκB) (C := C) p q hr
  rcases hreduce with ⟨hquot, hcontract⟩
  exact strictHenselianTensor_pairIdeal_existsUnique_minimalPrime_of_quotient
    (hκA := hκA) (hκB := hκB) p q hquot (fun {r} hr ↦ hcontract hr)

-- Proof sketch: contract a minimal prime of `C` along the flat maps from the localized tensor
-- product to `A` and `B` to get minimal primes of the two factors. For surjectivity, reduce to
-- the quotients by chosen minimal primes of `A` and `B`, use strict henselianity of those
-- quotients, normalize the resulting local domains, and compare with the strict henselization via
-- the normal local domain obtained from the localized tensor product of the normalizations.
/-- Lemma 15.108.4: if `A` and `B` are strictly henselian local `k`-algebras with residue fields
identified with `k` as `k`-algebras, and `C` is a chosen strict
henselization of the canonical localization of `A ⊗[k] B` at `m_A ⊗ B + A ⊗ m_B`, then
contraction along the canonical maps `A → C` and `B → C` gives a bijection between the minimal
primes of `C` and pairs of minimal primes of `A` and `B`. -/
@[stacks 06DU]
theorem strictHenselianTensorStrictHenselization_bijOn_minimalPrimePairs
    [IsStrictHenselizationOf (strictHenselianTensorClosedPointLocalization hκA hκB) C] :
    Function.Bijective
      (fun r : minimalPrimes C ↦ strictHenselianTensorMinimalPrimePair hκA hκB r) := by
  classical
  refine ⟨?_, ?_⟩
  · intro r₁ r₂ hpair
    let pq := strictHenselianTensorMinimalPrimePair hκA hκB r₁
    let I := strictHenselianTensorPairIdeal hκA hκB pq.1 pq.2
    rcases strictHenselianTensor_pairIdeal_existsUnique_minimalPrime
        (hκA := hκA) (hκB := hκB) (C := C) pq.1 pq.2 with
      ⟨r, hr, hr_unique⟩
    -- Both minimal primes lie above the same pair ideal, so uniqueness over `I_{p,q}` identifies
    -- them already as ideals of `C`.
    have hr₁ : r₁.1 ∈ minimalPrimes C ∧ I ≤ r₁.1 := by
      refine ⟨r₁.2, ?_⟩
      exact strictHenselianTensorPairIdeal_le_of_pair_eq
        (hκA := hκA) (hκB := hκB) (r := r₁) rfl
    have hr₂ : r₂.1 ∈ minimalPrimes C ∧ I ≤ r₂.1 := by
      refine ⟨r₂.2, ?_⟩
      exact strictHenselianTensorPairIdeal_le_of_pair_eq
        (hκA := hκA) (hκB := hκB) (r := r₂) <| by
          simpa [pq] using hpair
    apply Subtype.ext
    calc
      r₁.1 = r := (hr_unique _ hr₁).symm
      _ = r₂.1 := hr_unique _ hr₂
  · rintro ⟨p, q⟩
    rcases strictHenselianTensor_pairIdeal_existsUnique_minimalPrime
        (hκA := hκA) (hκB := hκB) (C := C) p q with
      ⟨r, hr, -⟩
    refine ⟨⟨r, hr.1⟩, ?_⟩
    -- The unique minimal prime above `I_{p,q}` contracts back to the chosen pair.
    exact strictHenselianTensorMinimalPrimePair_eq_of_pairIdeal_le
      (hκA := hκA) (hκB := hκB) (r := ⟨r, hr.1⟩) hr.2

end

end StrictHenselization

end
