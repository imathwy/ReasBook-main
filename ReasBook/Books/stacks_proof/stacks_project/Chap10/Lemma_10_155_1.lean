import Mathlib
import Mathlib.RingTheory.Henselian
import stacks_proof.stacks_project.Chap10.Lemma_10_143_5
import stacks_proof.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing
open scoped TensorProduct

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-
Domain-style sampling:
- primary domain: henselian local rings and henselization maps of local rings;
- sampled owner declarations of the same kind:
  `HenselianLocalRing`,
  `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
- best owner abstraction: there is no upstream bundled henselization owner in mathlib, so the
  source-facing owner here should be the class `IsHenselizationOf R S`, assembled from the
  canonical owners for henselianity, locality, and filtered-colimit-of-étale presentation;
- primitive data: the henselian local target, the local structural map, the filtered-colimit-of-
  étale presentation, the maximal-ideal image equality, and bijectivity on residue fields;
- derived API: the canonical residue-field equivalence induced by the structural map.

Source/core/bridge triage:
- `source-facing`: `IsHenselizationOf` and `exists_henselization`;
- `core/canonical`: `HenselianLocalRing`, `IsLocalHom`, and `RingHom.IsFilteredColimitOfEtale`;
- `bridge/view`: `IsHenselizationOf.residueFieldEquiv`.
-/
/-- An `R`-algebra `S` is a henselization of the local ring `R` if `R → S` is a local map, `S` is
henselian, `S` is a filtered colimit of étale `R`-algebras, the maximal ideal of `S` is the image
of the maximal ideal of `R`, and the induced residue-field map is bijective. -/
class IsHenselizationOf : Prop extends HenselianLocalRing S, IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap R S)
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S
  residueField_bijective :
    Function.Bijective (ResidueField.map (algebraMap R S))

namespace IsHenselizationOf

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type u} [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- The canonical residue-field isomorphism induced by a henselization. -/
noncomputable def residueFieldEquiv : ResidueField R ≃+* ResidueField S :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R S))
    IsHenselizationOf.residueField_bijective

end IsHenselizationOf

/-- Helper for Chap10 Lemma 10 155 1: a closed étale neighborhood of the closed point of a
local ring `R` consists of an étale `R`-algebra, a prime over `maximalIdeal R`, and the condition
that the corresponding residue-field map is bijective. -/
structure ClosedEtaleNeighborhood where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [etale : Algebra.Etale R carrier]
  point : Ideal carrier
  [point_isPrime : point.IsPrime]
  point_under_maximal : point.under R = maximalIdeal R
  residueFieldMap_bijective :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) point (algebraMap R carrier)
        point_under_maximal.symm)

attribute [instance] ClosedEtaleNeighborhood.commRing
attribute [instance] ClosedEtaleNeighborhood.algebra
attribute [instance] ClosedEtaleNeighborhood.etale
attribute [instance] ClosedEtaleNeighborhood.point_isPrime

namespace ClosedEtaleNeighborhood

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Chap10 Lemma 10 155 1: the chosen point of a closed étale neighborhood lies over
the closed point of the base. -/
lemma point_under_eq_maximal (A : ClosedEtaleNeighborhood R) :
    A.point.under R = maximalIdeal R := by
  -- Proof comment: this is one of the two closed-point invariants stored in the source object.
  exact A.point_under_maximal

/-- Helper for Chap10 Lemma 10 155 1: the chosen point of a closed étale neighborhood has
unchanged residue field over the closed point of the base. -/
lemma residueFieldMap_bijective_of_closedPoint (A : ClosedEtaleNeighborhood R) :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
        (point_under_eq_maximal A).symm) := by
  -- Proof comment: unfold the projection only once and expose it under a stable lemma name.
  exact A.residueFieldMap_bijective

/-- Helper for Chap10 Lemma 10 155 1: the residue map from a closed étale neighborhood back to
the base residue field, obtained by inverting the stored residue-field isomorphism. -/
noncomputable def toBaseResidueField (A : ClosedEtaleNeighborhood R) :
    A.carrier →+* (maximalIdeal R).ResidueField :=
  ((RingEquiv.ofBijective
    (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
      (point_under_eq_maximal A).symm)
    (residueFieldMap_bijective_of_closedPoint A)).symm.toRingHom).comp
      (algebraMap A.carrier A.point.ResidueField)

/-- Helper for Chap10 Lemma 10 155 1: the inverse-to-base residue map restricts to the canonical
map from `R` to its residue field. -/
lemma toBaseResidueField_comp_algebraMap (A : ClosedEtaleNeighborhood R) :
    (toBaseResidueField A).comp (algebraMap R A.carrier) =
      algebraMap R (maximalIdeal R).ResidueField := by
  -- Proof comment: push both maps through the residue-field equivalence attached to `A`, where
  -- they become the same map into `A.point.ResidueField`.
  let e : (maximalIdeal R).ResidueField ≃+* A.point.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
        (point_under_eq_maximal A).symm)
      (residueFieldMap_bijective_of_closedPoint A)
  ext r
  apply e.injective
  simpa [toBaseResidueField, e, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]

/-- Helper for Chap10 Lemma 10 155 1: the inverse-to-base residue map cuts out exactly the
chosen closed point. -/
lemma ker_toBaseResidueField (A : ClosedEtaleNeighborhood R) :
    RingHom.ker (toBaseResidueField A) = A.point := by
  -- Proof comment: composing with an injective residue-field equivalence does not change the
  -- kernel, so the claim reduces to the canonical kernel of `A.carrier → A.point.ResidueField`.
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    have hzero :
        algebraMap A.carrier A.point.ResidueField x = 0 := by
      have hres :
          (RingEquiv.ofBijective
            (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
              (point_under_eq_maximal A).symm)
            (residueFieldMap_bijective_of_closedPoint A)).symm
              (algebraMap A.carrier A.point.ResidueField x) =
            (RingEquiv.ofBijective
              (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
                (point_under_eq_maximal A).symm)
              (residueFieldMap_bijective_of_closedPoint A)).symm 0 := by
        simpa [toBaseResidueField, RingHom.mem_ker] using hx
      exact (RingEquiv.ofBijective
        (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
          (point_under_eq_maximal A).symm)
        (residueFieldMap_bijective_of_closedPoint A)).symm.injective hres
    exact Ideal.algebraMap_residueField_eq_zero.mp hzero
  · intro hx
    rw [RingHom.mem_ker]
    simp [toBaseResidueField, Ideal.algebraMap_residueField_eq_zero.mpr hx]

/-- Helper for Chap10 Lemma 10 155 1: the inverse-to-base residue map as an `R`-algebra map. -/
noncomputable def toBaseResidueFieldAlgHom (A : ClosedEtaleNeighborhood R) :
    A.carrier →ₐ[R] (maximalIdeal R).ResidueField where
  toRingHom := toBaseResidueField A
  commutes' r :=
    -- Proof comment: algebra-linearity is exactly the compatibility of the residue map with
    -- the structural map from `R`.
    congrArg (fun f : R →+* (maximalIdeal R).ResidueField ↦ f r)
      (toBaseResidueField_comp_algebraMap A)

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product residue map attached to two closed
étale neighborhoods. -/
noncomputable def tensorResidueMap (A B : ClosedEtaleNeighborhood R) :
    ((A.carrier) ⊗[R] (B.carrier)) →ₐ[R] (maximalIdeal R).ResidueField :=
  Algebra.TensorProduct.lift (toBaseResidueFieldAlgHom A) (toBaseResidueFieldAlgHom B)
    fun _ _ ↦ .all _ _

/-- Helper for Chap10 Lemma 10 155 1: the tensor residue map restricts to the first
inverse-to-base residue map. -/
lemma tensorResidueMap_comp_includeLeft (A B : ClosedEtaleNeighborhood R) :
    (tensorResidueMap A B).comp
      (Algebra.TensorProduct.includeLeft : A.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier)) =
      toBaseResidueFieldAlgHom A := by
  -- Proof comment: this is the left computation rule for the algebra tensor-product lift.
  simp [tensorResidueMap]

/-- Helper for Chap10 Lemma 10 155 1: the tensor residue map restricts to the second
inverse-to-base residue map. -/
lemma tensorResidueMap_comp_includeRight (A B : ClosedEtaleNeighborhood R) :
    (tensorResidueMap A B).comp
      (Algebra.TensorProduct.includeRight : B.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier)) =
      toBaseResidueFieldAlgHom B := by
  -- Proof comment: this is the right computation rule for the algebra tensor-product lift.
  simp [tensorResidueMap]

/-- Helper for Chap10 Lemma 10 155 1: the closed point on the tensor-product common refinement
candidate, defined as the kernel of the concrete tensor residue map. -/
noncomputable abbrev tensorPoint (A B : ClosedEtaleNeighborhood R) :
    Ideal ((A.carrier) ⊗[R] (B.carrier)) :=
  RingHom.ker ((tensorResidueMap A B).toRingHom)

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product point contracts to the first chosen
closed point. -/
lemma tensorPoint_comap_left (A B : ClosedEtaleNeighborhood R) :
    Ideal.comap
      ((Algebra.TensorProduct.includeLeft :
        A.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier)).toRingHom)
      (tensorPoint A B) = A.point := by
  -- Proof comment: contraction of a kernel is the kernel of the composite, and the left
  -- tensor-lift computation reduces that kernel to `ker_toBaseResidueField`.
  rw [tensorPoint, RingHom.comap_ker]
  change RingHom.ker
      (((tensorResidueMap A B).comp
        (Algebra.TensorProduct.includeLeft :
          A.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier))).toRingHom) = A.point
  rw [tensorResidueMap_comp_includeLeft]
  exact ker_toBaseResidueField A

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product point contracts to the second chosen
closed point. -/
lemma tensorPoint_comap_right (A B : ClosedEtaleNeighborhood R) :
    Ideal.comap
      ((Algebra.TensorProduct.includeRight :
        B.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier)).toRingHom)
      (tensorPoint A B) = B.point := by
  -- Proof comment: the same kernel-composite argument, now using the right tensor inclusion.
  rw [tensorPoint, RingHom.comap_ker]
  change RingHom.ker
      (((tensorResidueMap A B).comp
        (Algebra.TensorProduct.includeRight :
          B.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier))).toRingHom) = B.point
  rw [tensorResidueMap_comp_includeRight]
  exact ker_toBaseResidueField B

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product point is prime because its residue map
lands in a field. -/
lemma tensorPoint_isPrime (A B : ClosedEtaleNeighborhood R) :
    (tensorPoint A B).IsPrime := by
  -- Proof comment: the tensor point is a ring-hom kernel with field codomain.
  exact RingHom.ker_isPrime ((tensorResidueMap A B).toRingHom)

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product point carries its canonical prime
instance for residue-field constructions. -/
instance instTensorPointIsPrime (A B : ClosedEtaleNeighborhood R) :
    (tensorPoint A B).IsPrime :=
  tensorPoint_isPrime A B

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product point lies over the closed point of the
base. -/
lemma tensorPoint_under_maximal (A B : ClosedEtaleNeighborhood R) :
    (tensorPoint A B).under R = maximalIdeal R := by
  -- Proof comment: contract the tensor kernel through the left tensor inclusion, then use the
  -- stored closed-point equality for `A`.
  calc
    (tensorPoint A B).under R =
        Ideal.comap (algebraMap R A.carrier)
          (Ideal.comap
            (Algebra.TensorProduct.includeLeft :
              A.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier)).toRingHom
            (tensorPoint A B)) := by
      rw [Ideal.under_def, Ideal.comap_comap]
      rfl
    _ = Ideal.comap (algebraMap R A.carrier) A.point := by
      rw [tensorPoint_comap_left]
    _ = maximalIdeal R := by
      exact A.point_under_maximal

/-- Helper for Chap10 Lemma 10 155 1: the inverse-to-base residue map is surjective. -/
lemma toBaseResidueField_surjective (A : ClosedEtaleNeighborhood R) :
    Function.Surjective (toBaseResidueField A) := by
  -- Proof comment: the canonical map from a local ring to its residue field is surjective, and
  -- the inverse-to-base residue map agrees with it after precomposition from `R`.
  intro y
  obtain ⟨r, hr⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R) y
  refine ⟨algebraMap R A.carrier r, ?_⟩
  have h := congrArg (fun f : R →+* (maximalIdeal R).ResidueField ↦ f r)
    (toBaseResidueField_comp_algebraMap A)
  exact h.trans hr

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product residue map is surjective. -/
lemma tensorResidueMap_surjective (A B : ClosedEtaleNeighborhood R) :
    Function.Surjective (tensorResidueMap A B) := by
  -- Proof comment: the tensor residue map is already surjective on the left tensor factor.
  intro y
  obtain ⟨x, hx⟩ := toBaseResidueField_surjective A y
  refine
    ⟨(Algebra.TensorProduct.includeLeft :
      A.carrier →ₐ[R] (A.carrier) ⊗[R] (B.carrier)) x, ?_⟩
  have h := congrArg (fun f : A.carrier →ₐ[R] (maximalIdeal R).ResidueField ↦ f x)
    (tensorResidueMap_comp_includeLeft A B)
  exact h.trans hx

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product point is maximal. -/
lemma tensorPoint_isMaximal (A B : ClosedEtaleNeighborhood R) :
    (tensorPoint A B).IsMaximal := by
  -- Proof comment: a surjective map to a field has maximal kernel.
  exact RingHom.ker_isMaximal_of_surjective ((tensorResidueMap A B).toRingHom)
    (tensorResidueMap_surjective A B)

/-- Helper for Chap10 Lemma 10 155 1: the tensor product of two closed étale neighborhood
carriers is still étale over the base. -/
lemma tensorProduct_etale (A B : ClosedEtaleNeighborhood R) :
    Algebra.Etale R ((A.carrier) ⊗[R] (B.carrier)) := by
  -- Proof comment: view the tensor product as the base change of `B` to `A`, then compose with
  -- the étale structure map from `R` to `A`.
  exact Algebra.Etale.comp R A.carrier ((A.carrier) ⊗[R] (B.carrier))

/-- Helper for Chap10 Lemma 10 155 1: the tensor-product point has the same residue field as
the closed point of the base. -/
lemma tensorPoint_residueFieldMap_bijective (A B : ClosedEtaleNeighborhood R) :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) (tensorPoint A B)
        (algebraMap R ((A.carrier) ⊗[R] (B.carrier)))
        (tensorPoint_under_maximal A B).symm) := by
  -- Proof comment: injectivity is automatic for a residue-field map; for surjectivity, lift a
  -- residue class to the tensor product, compare its tensor-residue value with a base residue
  -- representative, and use the kernel description of `tensorPoint`.
  constructor
  · exact RingHom.injective _
  · intro y
    letI : (tensorPoint A B).IsMaximal := tensorPoint_isMaximal A B
    obtain ⟨t, ht⟩ := Ideal.algebraMap_residueField_surjective (tensorPoint A B) y
    obtain ⟨r, hr⟩ :=
      Ideal.algebraMap_residueField_surjective (maximalIdeal R) ((tensorResidueMap A B) t)
    refine ⟨algebraMap R (maximalIdeal R).ResidueField r, ?_⟩
    have hmem :
        algebraMap R ((A.carrier) ⊗[R] (B.carrier)) r - t ∈ tensorPoint A B := by
      rw [tensorPoint, RingHom.mem_ker]
      have hcomm :
          (tensorResidueMap A B)
            (algebraMap R ((A.carrier) ⊗[R] (B.carrier)) r) =
            algebraMap R (maximalIdeal R).ResidueField r := by
        exact (tensorResidueMap A B).commutes r
      rw [map_sub]
      have heq :
          (tensorResidueMap A B)
              (algebraMap R ((A.carrier) ⊗[R] (B.carrier)) r) =
            (tensorResidueMap A B) t := by
        simpa [Algebra.TensorProduct.includeLeft_apply] using hcomm.trans hr
      exact sub_eq_zero.mpr heq
    have heq :
        algebraMap ((A.carrier) ⊗[R] (B.carrier)) (tensorPoint A B).ResidueField
            (algebraMap R ((A.carrier) ⊗[R] (B.carrier)) r) =
          algebraMap ((A.carrier) ⊗[R] (B.carrier)) (tensorPoint A B).ResidueField t := by
      rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
      exact hmem
    calc
      Ideal.ResidueField.map (maximalIdeal R) (tensorPoint A B)
          (algebraMap R ((A.carrier) ⊗[R] (B.carrier)))
          (tensorPoint_under_maximal A B).symm
          (algebraMap R (maximalIdeal R).ResidueField r) =
          algebraMap ((A.carrier) ⊗[R] (B.carrier)) (tensorPoint A B).ResidueField
            (algebraMap R ((A.carrier) ⊗[R] (B.carrier)) r) := by
        rw [Ideal.ResidueField.map_algebraMap]
      _ = algebraMap ((A.carrier) ⊗[R] (B.carrier)) (tensorPoint A B).ResidueField t := heq
      _ = y := ht

/-- Helper for Chap10 Lemma 10 155 1: the tensor product of two closed étale neighborhoods is
a closed étale neighborhood with point cut out by the common residue map. -/
noncomputable def tensorNeighborhood (A B : ClosedEtaleNeighborhood R) :
    ClosedEtaleNeighborhood R where
  carrier := (A.carrier) ⊗[R] (B.carrier)
  commRing := inferInstance
  algebra := inferInstance
  etale := tensorProduct_etale A B
  point := tensorPoint A B
  point_isPrime := tensorPoint_isPrime A B
  point_under_maximal := tensorPoint_under_maximal A B
  residueFieldMap_bijective := tensorPoint_residueFieldMap_bijective A B

/-- Helper for Chap10 Lemma 10 155 1: the closed point of `R` lies over itself for the identity
`R`-algebra. -/
lemma point_under_base : (maximalIdeal R).under R = maximalIdeal R := by
  -- Proof comment: the contraction along the identity algebra map is the original ideal.
  simp [Ideal.under_def]

/-- Helper for Chap10 Lemma 10 155 1: the residue-field map of the identity closed
neighborhood is the identity. -/
lemma residueFieldMap_id_base :
    Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal R) (algebraMap R R)
        point_under_base.symm = RingHom.id (Ideal.ResidueField (maximalIdeal R)) := by
  -- Proof comment: compare maps out of the prime residue field on the algebra-map generators.
  apply Ideal.ResidueField.ringHom_ext
  ext x
  simp [Ideal.ResidueField.map_algebraMap]

/-- Helper for Chap10 Lemma 10 155 1: the residue-field map of the identity closed
neighborhood is bijective. -/
lemma residueFieldMap_bijective_base :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal R) (algebraMap R R)
        point_under_base.symm) := by
  -- Proof comment: rewrite the induced map to the identity and use bijectivity of `id`.
  rw [residueFieldMap_id_base]
  exact Function.bijective_id

/-- Helper for Chap10 Lemma 10 155 1: the base ring itself is a closed étale neighborhood of
its closed point. -/
protected def base (R : Type u) [CommRing R] [IsLocalRing R] :
    ClosedEtaleNeighborhood R where
  carrier := R
  commRing := inferInstance
  algebra := inferInstance
  etale := inferInstance
  point := maximalIdeal R
  point_isPrime := inferInstance
  point_under_maximal := point_under_base
  residueFieldMap_bijective := residueFieldMap_bijective_base

/-- Helper for Chap10 Lemma 10 155 1: the category of closed étale neighborhoods is nonempty. -/
instance instNonempty : Nonempty (ClosedEtaleNeighborhood R) :=
  -- Proof comment: the identity neighborhood supplies the initial existence needed for
  -- filteredness.
  ⟨ClosedEtaleNeighborhood.base R⟩

/-- Helper for Chap10 Lemma 10 155 1: the localized stage attached to a closed étale
neighborhood is the localization of its carrier at the chosen closed point. -/
abbrev localStage (A : ClosedEtaleNeighborhood R) : Type u :=
  Localization.AtPrime A.point

/-- Helper for Chap10 Lemma 10 155 1: the localized stage is a local ring. -/
lemma localStage_isLocalRing (A : ClosedEtaleNeighborhood R) : IsLocalRing A.localStage := by
  -- Proof comment: this is the canonical local-ring structure on a localization at a prime.
  infer_instance

/-- Helper for Chap10 Lemma 10 155 1: the localized stage of a closed étale neighborhood is
formally étale over the base. -/
lemma localStage_formallyEtale (A : ClosedEtaleNeighborhood R) :
    Algebra.FormallyEtale R A.localStage := by
  -- Proof comment: the carrier is globally étale over `R`, hence every prime localization lies in
  -- the étale locus; unfolding `IsEtaleAt` gives formal étaleness of this local stage.
  have hLocus :
      Algebra.etaleLocus R A.carrier = Set.univ :=
    (Algebra.etaleLocus_eq_univ_iff_etale (R := R) (A := A.carrier)).2 inferInstance
  have hmem :
      (⟨A.point, inferInstance⟩ : PrimeSpectrum A.carrier) ∈
        Algebra.etaleLocus R A.carrier := by
    rw [hLocus]
    exact Set.mem_univ _
  exact hmem

/-- Helper for Chap10 Lemma 10 155 1: the maximal ideal of the localized stage contracts to the
chosen point of the original étale neighborhood. -/
lemma localStage_comap_maximalIdeal (A : ClosedEtaleNeighborhood R) :
    Ideal.comap (algebraMap A.carrier A.localStage) (maximalIdeal A.localStage) =
      A.point := by
  -- Proof comment: use the owner lemma for localization at a prime in exactly its native shape.
  exact Localization.AtPrime.comap_maximalIdeal

/-- Helper for Chap10 Lemma 10 155 1: the chosen point maps to the maximal ideal of the localized
stage. -/
lemma localStage_map_point_eq_maximalIdeal (A : ClosedEtaleNeighborhood R) :
    Ideal.map (algebraMap A.carrier A.localStage) A.point = maximalIdeal A.localStage := by
  -- Proof comment: the image/comap closed-point statement is built into the at-prime API.
  exact Localization.AtPrime.map_eq_maximalIdeal

/-- Helper for Chap10 Lemma 10 155 1: after localizing a closed étale neighborhood at its
chosen point, the image of the base maximal ideal is the maximal ideal of the localized stage. -/
lemma localStage_map_maximalIdeal_of_closedPoint (A : ClosedEtaleNeighborhood R) :
    Ideal.map (algebraMap R A.localStage) (maximalIdeal R) = maximalIdeal A.localStage := by
  -- Proof comment: use the earlier étale-neighborhood criterion with the trivial basic open,
  -- then rewrite the point lying over the base closed point.
  have hEt : ∃ g : A.carrier, g ∉ A.point ∧ Algebra.Etale R (Localization.Away g) := by
    refine ⟨1, ?_, ?_⟩
    · exact (show A.point.IsPrime from inferInstance).one_notMem
    · infer_instance
  simpa [localStage, point_under_eq_maximal A] using
    map_eq_maximalIdeal_of_exists_etale_away (R := R) (S := A.carrier) A.point hEt

/-- Helper for Chap10 Lemma 10 155 1: localizing a closed étale neighborhood at its chosen
point does not change that point's residue field. -/
lemma localStage_residueFieldMap_bijective (A : ClosedEtaleNeighborhood R) :
    Function.Bijective
      (Ideal.ResidueField.map A.point (maximalIdeal A.localStage)
        (algebraMap A.carrier A.localStage) (localStage_comap_maximalIdeal A).symm) := by
  -- Proof comment: the localization map is surjective on stalks, hence it induces a residue-field
  -- bijection at the prime that survives as the maximal ideal of the localized stage.
  exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    (RingHom.surjectiveOnStalks_of_isLocalization A.point.primeCompl A.localStage)
    A.point (maximalIdeal A.localStage) (localStage_comap_maximalIdeal A).symm

/-- Helper for Chap10 Lemma 10 155 1: the structural map from the base to the localized stage is
a local homomorphism. -/
lemma localStage_isLocalHom (A : ClosedEtaleNeighborhood R) :
    IsLocalHom (algebraMap R A.localStage) := by
  -- Proof comment: identify the maximal-ideal contraction through the two algebra maps and then
  -- use the local-hom TFAE criterion.
  refine ((local_hom_TFAE (algebraMap R A.localStage)).out 4 0).mp ?_
  calc
    Ideal.comap (algebraMap R A.localStage) (maximalIdeal A.localStage) =
        Ideal.comap (algebraMap R A.carrier)
          (Ideal.comap (algebraMap A.carrier A.localStage) (maximalIdeal A.localStage)) := by
      rw [Ideal.comap_comap]
      rfl
    _ = Ideal.comap (algebraMap R A.carrier) A.point := by
      rw [localStage_comap_maximalIdeal]
    _ = maximalIdeal R := by
      exact A.point_under_maximal

/-- Helper for Chap10 Lemma 10 155 1: morphisms of closed étale neighborhoods are `R`-algebra
maps preserving the chosen closed point. -/
structure Hom (A B : ClosedEtaleNeighborhood R) where
  toAlgHom : A.carrier →ₐ[R] B.carrier
  map_point : A.point = Ideal.comap toAlgHom.toRingHom B.point

/-- Helper for Chap10 Lemma 10 155 1: two neighborhood morphisms are equal when their underlying
`R`-algebra maps are equal. -/
@[ext]
lemma Hom.ext {A B : ClosedEtaleNeighborhood R} {f g : Hom A B}
    (h : f.toAlgHom = g.toAlgHom) : f = g := by
  -- Proof comment: the point-preservation field is proof-irrelevant once the algebra map agrees.
  cases f with
  | mk fhom fpoint =>
    cases g with
    | mk ghom gpoint =>
      cases h
      rfl

/-- Helper for Chap10 Lemma 10 155 1: the identity algebra map preserves the chosen point. -/
lemma Hom.id_map_point (A : ClosedEtaleNeighborhood R) :
    A.point = Ideal.comap (AlgHom.id R A.carrier).toRingHom A.point := by
  -- Proof comment: the identity map does not change ideals under comap.
  simp

/-- Helper for Chap10 Lemma 10 155 1: the identity morphism of a closed étale neighborhood. -/
protected def Hom.id (A : ClosedEtaleNeighborhood R) : Hom A A where
  toAlgHom := AlgHom.id R A.carrier
  map_point := Hom.id_map_point A

/-- Helper for Chap10 Lemma 10 155 1: the structural map from the base neighborhood to any
closed étale neighborhood preserves closed points. -/
lemma Hom.baseTo_map_point (A : ClosedEtaleNeighborhood R) :
    (ClosedEtaleNeighborhood.base R).point =
      Ideal.comap (Algebra.ofId R A.carrier).toRingHom A.point := by
  -- Proof comment: this is the stored equality saying that `A.point` contracts to
  -- `maximalIdeal R`.
  exact A.point_under_maximal.symm

/-- Helper for Chap10 Lemma 10 155 1: the canonical morphism from the base neighborhood to a
closed étale neighborhood. -/
protected def Hom.baseTo (A : ClosedEtaleNeighborhood R) :
    Hom (ClosedEtaleNeighborhood.base R) A where
  toAlgHom := Algebra.ofId R A.carrier
  map_point := Hom.baseTo_map_point A

/-- Helper for Chap10 Lemma 10 155 1: the left tensor inclusion preserves the chosen closed
point. -/
lemma Hom.toTensorLeft_map_point (A B : ClosedEtaleNeighborhood R) :
    A.point =
      Ideal.comap
        (Algebra.TensorProduct.includeLeft :
          A.carrier →ₐ[R] (tensorNeighborhood A B).carrier).toRingHom
        (tensorNeighborhood A B).point := by
  -- Proof comment: the point on the tensor neighborhood was defined so its contraction along
  -- the left inclusion is the original point of `A`.
  exact (tensorPoint_comap_left A B).symm

/-- Helper for Chap10 Lemma 10 155 1: the canonical morphism from the first factor to the tensor
common refinement. -/
noncomputable def Hom.toTensorLeft (A B : ClosedEtaleNeighborhood R) :
    Hom A (tensorNeighborhood A B) where
  toAlgHom := Algebra.TensorProduct.includeLeft
  map_point := Hom.toTensorLeft_map_point A B

/-- Helper for Chap10 Lemma 10 155 1: the right tensor inclusion preserves the chosen closed
point. -/
lemma Hom.toTensorRight_map_point (A B : ClosedEtaleNeighborhood R) :
    B.point =
      Ideal.comap
        (Algebra.TensorProduct.includeRight :
          B.carrier →ₐ[R] (tensorNeighborhood A B).carrier).toRingHom
        (tensorNeighborhood A B).point := by
  -- Proof comment: the point on the tensor neighborhood was defined so its contraction along
  -- the right inclusion is the original point of `B`.
  exact (tensorPoint_comap_right A B).symm

/-- Helper for Chap10 Lemma 10 155 1: the canonical morphism from the second factor to the
tensor common refinement. -/
noncomputable def Hom.toTensorRight (A B : ClosedEtaleNeighborhood R) :
    Hom B (tensorNeighborhood A B) where
  toAlgHom := Algebra.TensorProduct.includeRight
  map_point := Hom.toTensorRight_map_point A B

/-- Helper for Chap10 Lemma 10 155 1: every closed étale neighborhood receives a morphism from
the base neighborhood. -/
lemma nonempty_baseTo (A : ClosedEtaleNeighborhood R) :
    Nonempty (Hom (ClosedEtaleNeighborhood.base R) A) := by
  -- Proof comment: package the canonical structural morphism as categorical nonemptiness.
  exact ⟨Hom.baseTo A⟩

/-- Helper for Chap10 Lemma 10 155 1: the composite of point-preserving algebra maps again
preserves the chosen point. -/
lemma Hom.comp_map_point {A B C : ClosedEtaleNeighborhood R} (f : Hom A B) (g : Hom B C) :
    A.point = Ideal.comap (g.toAlgHom.comp f.toAlgHom).toRingHom C.point := by
  -- Proof comment: rewrite the source point through `f`, then through `g`, and combine the two
  -- ideal comaps into the comap of the composite map.
  calc
    A.point = Ideal.comap f.toAlgHom.toRingHom B.point := f.map_point
    _ = Ideal.comap f.toAlgHom.toRingHom (Ideal.comap g.toAlgHom.toRingHom C.point) := by
      rw [g.map_point]
    _ = Ideal.comap (g.toAlgHom.comp f.toAlgHom).toRingHom C.point := by
      rw [Ideal.comap_comap]
      rfl

/-- Helper for Chap10 Lemma 10 155 1: composition of morphisms of closed étale neighborhoods. -/
protected def Hom.comp {A B C : ClosedEtaleNeighborhood R} (f : Hom A B) (g : Hom B C) :
    Hom A C where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  map_point := Hom.comp_map_point f g

/-- Helper for Chap10 Lemma 10 155 1: left identity law for neighborhood morphisms. -/
lemma Hom.id_comp {A B : ClosedEtaleNeighborhood R} (f : Hom A B) :
    Hom.comp (Hom.id A) f = f := by
  -- Proof comment: reduce the categorical law to the corresponding algebra-map equality.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 155 1: right identity law for neighborhood morphisms. -/
lemma Hom.comp_id {A B : ClosedEtaleNeighborhood R} (f : Hom A B) :
    Hom.comp f (Hom.id B) = f := by
  -- Proof comment: reduce the categorical law to the corresponding algebra-map equality.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 155 1: associativity of neighborhood morphism composition. -/
lemma Hom.assoc {A B C D : ClosedEtaleNeighborhood R} (f : Hom A B) (g : Hom B C)
    (h : Hom C D) : Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  -- Proof comment: associativity is inherited directly from composition of algebra maps.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 155 1: closed étale neighborhoods form the indexing category for
the localized-stage diagram. -/
instance instCategory : Category (ClosedEtaleNeighborhood R) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Helper for Chap10 Lemma 10 155 1: any two closed étale neighborhoods have a common tensor
refinement. -/
lemma commonRefinement (A B : ClosedEtaleNeighborhood R) :
    ∃ C : ClosedEtaleNeighborhood R, Nonempty (A ⟶ C) ∧ Nonempty (B ⟶ C) := by
  -- Proof comment: package the tensor neighborhood and its two canonical inclusion morphisms
  -- as the object-cocone required for filteredness.
  refine ⟨tensorNeighborhood A B, ?_, ?_⟩
  · exact ⟨Hom.toTensorLeft A B⟩
  · exact ⟨Hom.toTensorRight A B⟩

/-- Helper for Chap10 Lemma 10 155 1: the base neighborhood and any closed étale neighborhood
have a common refinement, namely that neighborhood itself. -/
lemma base_commonRefinement (A : ClosedEtaleNeighborhood R) :
    ∃ C : ClosedEtaleNeighborhood R,
      Nonempty (ClosedEtaleNeighborhood.base R ⟶ C) ∧ Nonempty (A ⟶ C) := by
  -- Proof comment: use the structural map from the base and the identity map on `A`.
  refine ⟨A, ?_, ?_⟩
  · exact nonempty_baseTo A
  · exact ⟨𝟙 A⟩

/-- Helper for Chap10 Lemma 10 155 1: the prime of the principal localization induced by a
point avoiding the inverted element. -/
abbrev awayPoint (A : ClosedEtaleNeighborhood R) (s : A.carrier) (_hs : s ∉ A.point) :
    Ideal (Localization.Away s) :=
  Ideal.map (algebraMap A.carrier (Localization.Away s)) A.point

/-- Helper for Chap10 Lemma 10 155 1: avoiding the point is the disjointness condition for
localization at powers. -/
lemma powers_disjoint_point_of_notMem (A : ClosedEtaleNeighborhood R) {s : A.carrier}
    (hs : s ∉ A.point) :
    Disjoint (Submonoid.powers s : Set A.carrier) (A.point : Set A.carrier) := by
  -- Proof comment: radicality of a prime ideal converts avoidance of `s` into disjointness from
  -- every positive power of `s`.
  exact (Ideal.disjoint_powers_iff_notMem s (Ideal.IsPrime.isRadical inferInstance)).2 hs

/-- Helper for Chap10 Lemma 10 155 1: the induced ideal in a principal localization remains
prime. -/
lemma awayPoint_isPrime (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    (awayPoint A s hs).IsPrime := by
  -- Proof comment: a prime disjoint from the inverted powers survives under localization.
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) (Localization.Away s)
    A.point (show A.point.IsPrime from inferInstance) (powers_disjoint_point_of_notMem A hs)

/-- Helper for Chap10 Lemma 10 155 1: the away point has its canonical prime instance. -/
instance instAwayPointIsPrime (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    (awayPoint A s hs).IsPrime :=
  awayPoint_isPrime A s hs

/-- Helper for Chap10 Lemma 10 155 1: contraction of the induced principal-localization point
recovers the original point. -/
lemma awayPoint_comap (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    Ideal.comap (algebraMap A.carrier (Localization.Away s)) (awayPoint A s hs) =
      A.point := by
  -- Proof comment: localization-comap is exact for a prime disjoint from the inverted powers.
  exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers s) (Localization.Away s)
    (show A.point.IsPrime from inferInstance) (powers_disjoint_point_of_notMem A hs)

/-- Helper for Chap10 Lemma 10 155 1: the away point still lies over the closed point of the
base. -/
lemma away_point_under_maximal (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    (awayPoint A s hs).under R = maximalIdeal R := by
  -- Proof comment: contract first from the principal localization to `A`, then use the stored
  -- closed-point equality for `A`.
  calc
    (awayPoint A s hs).under R =
        Ideal.comap (algebraMap R A.carrier)
          (Ideal.comap (algebraMap A.carrier (Localization.Away s)) (awayPoint A s hs)) := by
      rw [Ideal.under_def, Ideal.comap_comap]
      rfl
    _ = Ideal.comap (algebraMap R A.carrier) A.point := by
      rw [awayPoint_comap]
    _ = maximalIdeal R := by
      exact A.point_under_maximal

/-- Helper for Chap10 Lemma 10 155 1: principal localization away from a point element does not
change that residue field. -/
lemma awayResidueFieldMap_bijective (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    Function.Bijective
      (Ideal.ResidueField.map A.point (awayPoint A s hs)
        (algebraMap A.carrier (Localization.Away s)) (awayPoint_comap A s hs).symm) := by
  -- Proof comment: localization maps are surjective on stalks, hence induce residue-field
  -- bijections at surviving primes.
  exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers s) (Localization.Away s))
    A.point (awayPoint A s hs) (awayPoint_comap A s hs).symm

/-- Helper for Chap10 Lemma 10 155 1: the base-to-away residue-field map factors through the
original neighborhood. -/
lemma away_residueFieldMap_eq_comp (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    Ideal.ResidueField.map (maximalIdeal R) (awayPoint A s hs)
        (algebraMap R (Localization.Away s)) (away_point_under_maximal A s hs).symm =
      (Ideal.ResidueField.map A.point (awayPoint A s hs)
          (algebraMap A.carrier (Localization.Away s)) (awayPoint_comap A s hs).symm).comp
        (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
          A.point_under_maximal.symm) := by
  -- Proof comment: both maps are determined by the residue classes of base-ring elements.
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro r
  simp [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap,
    IsScalarTower.algebraMap_apply R A.carrier (Localization.Away s)]

/-- Helper for Chap10 Lemma 10 155 1: the principal-open neighborhood has unchanged residue
field over the base. -/
lemma away_residueFieldMap_bijective (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) (awayPoint A s hs)
        (algebraMap R (Localization.Away s)) (away_point_under_maximal A s hs).symm) := by
  -- Proof comment: rewrite the base map as a composite of two known residue-field bijections.
  rw [away_residueFieldMap_eq_comp]
  exact (awayResidueFieldMap_bijective A s hs).comp
    (residueFieldMap_bijective_of_closedPoint A)

/-- Helper for Chap10 Lemma 10 155 1: the principal localization of a closed étale neighborhood
is étale over the base. -/
lemma away_etale (A : ClosedEtaleNeighborhood R) (s : A.carrier) :
    Algebra.Etale R (Localization.Away s) := by
  -- Proof comment: principal localization is étale over `A`, and étaleness composes with the
  -- étale structure map from `R`.
  infer_instance

/-- Helper for Chap10 Lemma 10 155 1: a principal-open refinement of a closed étale
neighborhood. -/
protected noncomputable def away (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    ClosedEtaleNeighborhood R where
  carrier := Localization.Away s
  commRing := inferInstance
  algebra := inferInstance
  etale := away_etale A s
  point := awayPoint A s hs
  point_isPrime := inferInstance
  point_under_maximal := away_point_under_maximal A s hs
  residueFieldMap_bijective := away_residueFieldMap_bijective A s hs

/-- Helper for Chap10 Lemma 10 155 1: the canonical localization map preserves the chosen
point. -/
lemma Hom.toAway_map_point (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    A.point = Ideal.comap (IsScalarTower.toAlgHom R A.carrier (Localization.Away s)).toRingHom
      (ClosedEtaleNeighborhood.away A s hs).point := by
  -- Proof comment: this is exactly the contraction computation for the principal-localization
  -- point.
  exact (awayPoint_comap A s hs).symm

/-- Helper for Chap10 Lemma 10 155 1: the canonical morphism to the principal-open
refinement. -/
noncomputable def Hom.toAway (A : ClosedEtaleNeighborhood R) (s : A.carrier)
    (hs : s ∉ A.point) :
    Hom A (ClosedEtaleNeighborhood.away A s hs) where
  toAlgHom := IsScalarTower.toAlgHom R A.carrier (Localization.Away s)
  map_point := Hom.toAway_map_point A s hs

/-- Helper for Chap10 Lemma 10 155 1: a morphism of closed étale neighborhoods induces a local
`R`-algebra map between the corresponding localized stages. -/
noncomputable def Hom.localStageMap {A B : ClosedEtaleNeighborhood R} (f : Hom A B) :
    A.localStage →ₐ[R] B.localStage :=
  Localization.localAlgHom A.point B.point f.toAlgHom f.map_point

/-- Helper for Chap10 Lemma 10 155 1: a morphism-induced map between localized stages is a
local homomorphism. -/
lemma Hom.localStageMap_isLocalHom {A B : ClosedEtaleNeighborhood R} (f : Hom A B) :
    IsLocalHom f.localStageMap.toRingHom := by
  -- Proof comment: the localized-stage map is exactly mathlib's local homomorphism between
  -- localizations at prime ideals.
  dsimp [Hom.localStageMap]
  exact Localization.isLocalHom_localRingHom A.point B.point f.toAlgHom.toRingHom f.map_point

/-- Helper for Chap10 Lemma 10 155 1: the localized-stage map induced by an identity
neighborhood morphism is the identity algebra map. -/
lemma Hom.localStageMap_id (A : ClosedEtaleNeighborhood R) :
    (Hom.id A).localStageMap = AlgHom.id R A.localStage := by
  -- Proof comment: localization maps are determined by their values on the original carrier.
  ext x
  exact Localization.localRingHom_to_map A.point A.point (AlgHom.id R A.carrier).toRingHom
    (Hom.id_map_point A) x

/-- Helper for Chap10 Lemma 10 155 1: induced maps on localized stages respect composition of
neighborhood morphisms. -/
lemma Hom.localStageMap_comp {A B C : ClosedEtaleNeighborhood R} (f : Hom A B) (g : Hom B C) :
    (Hom.comp f g).localStageMap = g.localStageMap.comp f.localStageMap := by
  -- Proof comment: compare both maps after precomposition with the localization map out of the
  -- source carrier, then use the defining computation rule for `Localization.localRingHom`.
  ext x
  have hfmap :=
    Localization.localRingHom_to_map A.point B.point f.toAlgHom.toRingHom f.map_point x
  have hgmap :=
    Localization.localRingHom_to_map B.point C.point g.toAlgHom.toRingHom g.map_point
      (f.toAlgHom x)
  calc
    (Localization.localRingHom A.point C.point (Hom.comp f g).toAlgHom.toRingHom
        (Hom.comp_map_point f g))
        ((Algebra.algHom R A.carrier (Localization.AtPrime A.point)) x) =
        algebraMap C.carrier (Localization.AtPrime C.point) ((g.toAlgHom.comp f.toAlgHom) x) := by
      exact Localization.localRingHom_to_map A.point C.point
        (g.toAlgHom.comp f.toAlgHom).toRingHom (Hom.comp_map_point f g) x
    _ = algebraMap C.carrier (Localization.AtPrime C.point) (g.toAlgHom (f.toAlgHom x)) := rfl
    _ = (Localization.localRingHom B.point C.point g.toAlgHom.toRingHom g.map_point)
        (algebraMap B.carrier (Localization.AtPrime B.point) (f.toAlgHom x)) := hgmap.symm
    _ = (Localization.localRingHom B.point C.point g.toAlgHom.toRingHom g.map_point)
        ((Localization.localRingHom A.point B.point f.toAlgHom.toRingHom f.map_point)
          ((Algebra.algHom R A.carrier (Localization.AtPrime A.point)) x)) := by
      have hsource :
          (Algebra.algHom R A.carrier (Localization.AtPrime A.point)) x =
            algebraMap A.carrier (Localization.AtPrime A.point) x := rfl
      rw [hsource, hfmap]
      rfl

/-- Helper for Chap10 Lemma 10 155 1: the localized-stage functor sends identity morphisms to
identity morphisms in `CommAlgCat R`. -/
lemma localStageDiagram_map_id (A : ClosedEtaleNeighborhood R) :
    CommAlgCat.ofHom (Hom.id A).localStageMap = 𝟙 (CommAlgCat.of R A.localStage) := by
  -- Proof comment: pass the identity computation for localized-stage algebra maps through
  -- `CommAlgCat.ofHom`.
  simp [Hom.localStageMap_id]

/-- Helper for Chap10 Lemma 10 155 1: the localized-stage functor sends composition of
neighborhood morphisms to composition in `CommAlgCat R`. -/
lemma localStageDiagram_map_comp {A B C : ClosedEtaleNeighborhood R} (f : Hom A B) (g : Hom B C) :
    CommAlgCat.ofHom (Hom.comp f g).localStageMap =
      CommAlgCat.ofHom f.localStageMap ≫ CommAlgCat.ofHom g.localStageMap := by
  -- Proof comment: pass the composition computation for localized-stage algebra maps through
  -- `CommAlgCat.ofHom`.
  simp [Hom.localStageMap_comp]

/-- Helper for Chap10 Lemma 10 155 1: the diagram of localized closed étale neighborhoods in
commutative `R`-algebras. -/
noncomputable def localStageDiagram : ClosedEtaleNeighborhood R ⥤ CommAlgCat R where
  obj A := CommAlgCat.of R A.localStage
  map f := CommAlgCat.ofHom f.localStageMap
  map_id := localStageDiagram_map_id
  map_comp := localStageDiagram_map_comp

/-- Helper for Chap10 Lemma 10 155 1: a morphism of closed étale neighborhoods is compatible
with the inverse maps to the base residue field. -/
lemma Hom.toBaseResidueField_comp {A B : ClosedEtaleNeighborhood R} (f : Hom A B) :
    (toBaseResidueField B).comp f.toAlgHom.toRingHom = toBaseResidueField A := by
  -- Proof comment: compare the induced map on residue fields with the two stored residue-field
  -- isomorphisms from the base closed point.
  let eA : (maximalIdeal R).ResidueField ≃+* A.point.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map (maximalIdeal R) A.point (algebraMap R A.carrier)
        (point_under_eq_maximal A).symm)
      (residueFieldMap_bijective_of_closedPoint A)
  let eB : (maximalIdeal R).ResidueField ≃+* B.point.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map (maximalIdeal R) B.point (algebraMap R B.carrier)
        (point_under_eq_maximal B).symm)
      (residueFieldMap_bijective_of_closedPoint B)
  let φ : A.point.ResidueField →+* B.point.ResidueField :=
    Ideal.ResidueField.map A.point B.point f.toAlgHom.toRingHom f.map_point
  have hφe : φ.comp eA.toRingHom = eB.toRingHom := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp [φ, eA, eB, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  have hφ : φ = eB.toRingHom.comp eA.symm.toRingHom := by
    apply RingHom.ext
    intro x
    have hx : x = eA (eA.symm x) := by
      simp
    rw [hx]
    simpa [RingHom.comp_apply] using DFunLike.congr_fun hφe (eA.symm x)
  have hφsymm : eB.symm.toRingHom.comp φ = eA.symm.toRingHom := by
    rw [hφ]
    apply RingHom.ext
    intro x
    simp [RingHom.comp_apply]
  -- Proof comment: after the residue-field comparison, evaluate both maps on representatives
  -- from the source neighborhood.
  apply RingHom.ext
  intro a
  calc
    (toBaseResidueField B).comp f.toAlgHom.toRingHom a =
        eB.symm (algebraMap B.carrier B.point.ResidueField (f.toAlgHom.toRingHom a)) := by
      rfl
    _ = eB.symm (φ (algebraMap A.carrier A.point.ResidueField a)) := by
      rw [Ideal.ResidueField.map_algebraMap]
    _ = eA.symm (algebraMap A.carrier A.point.ResidueField a) := by
      exact DFunLike.congr_fun hφsymm (algebraMap A.carrier A.point.ResidueField a)
    _ = toBaseResidueField A a := by
      rfl

/-- Helper for Chap10 Lemma 10 155 1: the algebra-map form of residue-field compatibility for
morphisms of closed étale neighborhoods. -/
lemma Hom.toBaseResidueFieldAlgHom_comp {A B : ClosedEtaleNeighborhood R} (f : Hom A B) :
    (toBaseResidueFieldAlgHom B).comp f.toAlgHom = toBaseResidueFieldAlgHom A := by
  -- Proof comment: the algebra-map statement is the ring-map compatibility with the stored
  -- `R`-algebra structures restored.
  apply AlgHom.coe_ringHom_injective
  exact Hom.toBaseResidueField_comp f

/-- Helper for Chap10 Lemma 10 155 1: the canonical element cutting out the equality locus of
two morphisms from a formally unramified neighborhood. -/
noncomputable def equalizerElement {A B : ClosedEtaleNeighborhood R} (f g : Hom A B) :
    B.carrier :=
  (Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom (fun _ _ ↦ .all _ _))
    (Algebra.FormallyUnramified.elem R A.carrier)

/-- Helper for Chap10 Lemma 10 155 1: applying the same residue map on both tensor factors is
the residue map after multiplication. -/
lemma tensorLift_toBaseResidueField_eq_lmul (A : ClosedEtaleNeighborhood R) :
    Algebra.TensorProduct.lift (toBaseResidueFieldAlgHom A) (toBaseResidueFieldAlgHom A)
      (fun _ _ ↦ .all _ _) =
      (toBaseResidueFieldAlgHom A).comp (Algebra.TensorProduct.lmul' R) := by
  -- Proof comment: the tensor-product universal property reduces the comparison to pure tensors.
  ext x
  · simp
  · simp

/-- Helper for Chap10 Lemma 10 155 1: the equalizer element has residue `1` at the chosen
closed point of the target neighborhood. -/
lemma equalizerElement_toBaseResidueField {A B : ClosedEtaleNeighborhood R}
    (f g : Hom A B) :
    toBaseResidueField B (equalizerElement f g) = 1 := by
  -- Proof comment: residue compatibility turns the two target maps into the same source residue
  -- map, so the unramified tensor element multiplies to `1`.
  let hB := toBaseResidueFieldAlgHom B
  let hA := toBaseResidueFieldAlgHom A
  have hcomp :
      hB.comp (Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom (fun _ _ ↦ .all _ _)) =
        Algebra.TensorProduct.lift hA hA (fun _ _ ↦ .all _ _) := by
    ext x
    · simpa [hB, hA, AlgHom.comp_apply] using
        DFunLike.congr_fun (Hom.toBaseResidueFieldAlgHom_comp f) x
    · simpa [hB, hA, AlgHom.comp_apply] using
        DFunLike.congr_fun (Hom.toBaseResidueFieldAlgHom_comp g) x
  calc
    toBaseResidueField B (equalizerElement f g) =
        hB ((Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom (fun _ _ ↦ .all _ _))
          (Algebra.FormallyUnramified.elem R A.carrier)) := by
      rfl
    _ = (Algebra.TensorProduct.lift hA hA (fun _ _ ↦ .all _ _))
          (Algebra.FormallyUnramified.elem R A.carrier) := by
      exact DFunLike.congr_fun hcomp (Algebra.FormallyUnramified.elem R A.carrier)
    _ = ((toBaseResidueFieldAlgHom A).comp (Algebra.TensorProduct.lmul' R))
          (Algebra.FormallyUnramified.elem R A.carrier) := by
      rw [tensorLift_toBaseResidueField_eq_lmul]
    _ = 1 := by
      simp [Algebra.FormallyUnramified.lmul_elem]

/-- Helper for Chap10 Lemma 10 155 1: the equality-locus denominator avoids the target closed
point. -/
lemma equalizerElement_notMem {A B : ClosedEtaleNeighborhood R} (f g : Hom A B) :
    equalizerElement f g ∉ B.point := by
  -- Proof comment: membership in the point would force zero residue, contradicting that the
  -- equalizer element has residue `1`.
  intro hmem
  have hker : equalizerElement f g ∈ RingHom.ker (toBaseResidueField B) := by
    rw [ker_toBaseResidueField]
    exact hmem
  have hzero : toBaseResidueField B (equalizerElement f g) = 0 :=
    RingHom.mem_ker.mp hker
  rw [equalizerElement_toBaseResidueField f g] at hzero
  exact one_ne_zero hzero

/-- Helper for Chap10 Lemma 10 155 1: multiplying by the equality-locus denominator kills the
difference of two parallel neighborhood morphisms. -/
lemma map_sub_mul_equalizerElement {A B : ClosedEtaleNeighborhood R} (f g : Hom A B)
    (a : A.carrier) :
    (f.toAlgHom a - g.toAlgHom a) * equalizerElement f g = 0 := by
  -- Proof comment: map the formally unramified identity
  -- `(1 ⊗ a) * e = (a ⊗ 1) * e` through the two target morphisms.
  let L : A.carrier ⊗[R] A.carrier →ₐ[R] B.carrier :=
    Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom (fun _ _ ↦ .all _ _)
  have h :=
    congrArg L (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) (S := A.carrier) a)
  simpa [L, equalizerElement, Algebra.TensorProduct.lift_tmul, sub_mul] using
    sub_eq_zero.mpr h.symm

/-- Helper for Chap10 Lemma 10 155 1: an element belongs to the submonoid generated by its
own powers. -/
lemma self_mem_powers {A : Type u} [Monoid A] (s : A) : s ∈ Submonoid.powers s := by
  -- Proof comment: the first power of `s` is `s` itself.
  exact (Submonoid.mem_powers_iff s s).mpr ⟨1, pow_one s⟩

/-- Helper for Chap10 Lemma 10 155 1: parallel morphisms of closed étale neighborhoods become
equal after a principal-open refinement. -/
lemma equalizerRefinement {A B : ClosedEtaleNeighborhood R} (f g : Hom A B) :
    ∃ C : ClosedEtaleNeighborhood R, ∃ h : B ⟶ C, f ≫ h = g ≫ h := by
  -- Proof comment: invert the unramified equality-locus denominator, then use the localization
  -- zero criterion to identify the two localized composites.
  let s : B.carrier := equalizerElement f g
  have hs : s ∉ B.point := equalizerElement_notMem f g
  refine ⟨ClosedEtaleNeighborhood.away B s hs, Hom.toAway B s hs, ?_⟩
  apply Hom.ext
  apply AlgHom.ext
  intro a
  dsimp [CategoryStruct.comp, instCategory, Hom.comp, Hom.toAway]
  let M : Submonoid B.carrier := Submonoid.powers s
  have hzero : algebraMap B.carrier (Localization.Away s) (f.toAlgHom a - g.toAlgHom a) = 0 := by
    rw [IsLocalization.map_eq_zero_iff M (Localization.Away s)]
    have hs_pow : s ∈ M := by
      exact self_mem_powers s
    refine ⟨⟨s, hs_pow⟩, ?_⟩
    simpa [M, mul_comm] using map_sub_mul_equalizerElement f g a
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- Helper for Chap10 Lemma 10 155 1: closed étale neighborhoods form a filtered indexing
category. -/
instance instIsFiltered : IsFiltered (ClosedEtaleNeighborhood R) where
  nonempty := instNonempty
  cocone_objs A B := by
    -- Proof comment: tensor products give a common refinement for any pair of objects.
    obtain ⟨C, hA, hB⟩ := commonRefinement A B
    obtain ⟨f⟩ := hA
    obtain ⟨g⟩ := hB
    refine ⟨C, f, g, ?_⟩
    trivial
  cocone_maps := by
    -- Proof comment: the principal open above equalizes any parallel pair of morphisms.
    intro A B f g
    exact equalizerRefinement f g

end ClosedEtaleNeighborhood

-- Proof sketch: define `Rʰ` as the filtered colimit of étale local `R`-algebras whose residue
-- field over `ResidueField R` is unchanged. The filtered-colimit-of-étale property is built into
-- the construction, the local and maximal-ideal statements come from the unique prime over the
-- closed point, the residue-field map is the canonical colimit identification, and henselianity
-- follows by descending a monic polynomial with a simple residue-field root to some étale stage
-- and lifting that root there.
/-- Lemma 10.155.1: every local ring admits a henselization `R → Rʰ`, namely a local map to a
henselian local ring that is a filtered colimit of étale `R`-algebras, whose maximal ideal is the
image of `maximalIdeal R`, and whose residue field agrees with `ResidueField R`. -/
@[stacks 04GN]
theorem exists_henselization :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh), IsHenselizationOf R Rh := by
  -- Proof comment: the intended construction is the filtered colimit of closed étale
  -- neighborhoods of the closed point of `R`. The tensor and principal-open API above now
  -- supplies common refinements, equalizer refinements, and filteredness of the indexing category.
  -- Route correction: a localized-at-prime stage is formally étale, but not generally finite
  -- presented, so the ind-étale field must be built from principal-open étale stages cofinal in
  -- each localization rather than by claiming that `A.localStage` itself is an étale stage.
  -- TODO: construct the closed-étale-neighborhood filtered colimit package, prove its local,
  -- maximal-ideal, residue-field, ind-étale, and henselianity fields, then assemble
  -- `IsHenselizationOf`; avoid the formally available terminal-ring typeclass loop, since it
  -- contradicts the nontrivial local-ring meaning of henselization.
  sorry

end
