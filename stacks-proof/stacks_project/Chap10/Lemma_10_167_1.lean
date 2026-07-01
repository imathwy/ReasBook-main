import Mathlib
import stacks_project.Chap10.Definition_10_104_6
import stacks_project.Chap10.Definition_10_135_5
import stacks_project.Chap10.Lemma_10_135_3
import stacks_project.Chap10.Lemma_10_135_9
import stacks_project.Chap10.Lemma_10_135_11
import stacks_project.Chap10.Lemma_10_136_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {L : Type w} [Field L] [Algebra k L]

/-- Helper for Lemma 10.167.1: if one of the two field extensions over `k` is essentially finite
type, then the tensor product is a local complete intersection over the other field and hence is
Cohen-Macaulay. -/
private theorem cohenMacaulayRing_tensorProduct_of_essFiniteType_on_either_side
    (hfin : Algebra.EssFiniteType k K ∨ Algebra.EssFiniteType k L) :
    CohenMacaulayRing (K ⊗[k] L) := by
  cases hfin with
  | inl hK =>
      let _ : Algebra.EssFiniteType k K := hK
      have hPrime :
          ∀ q : PrimeSpectrum K,
            IsCompleteIntersectionOver.{u, v, v} k (Localization.AtPrime q.asIdeal) := by
        intro q
        let _ : Algebra.EssFiniteType k (Localization.AtPrime q.asIdeal) := inferInstance
        let _ : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := inferInstance
        infer_instance
      have hCIK : IsLocalCompleteIntersection k K := by
        have hTFAE :
            List.TFAE
              [ IsLocalCompleteIntersection k K
              , ∀ q : PrimeSpectrum K,
                  IsCompleteIntersectionOver.{u, v, v} k (Localization.AtPrime q.asIdeal)
              , ∀ m : MaximalSpectrum K,
                  IsCompleteIntersectionOver.{u, v, v} k (Localization.AtPrime m.asIdeal)
              ] :=
          isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings
        exact (hTFAE.out 1 0 rfl rfl).mp hPrime
      have hCILK : IsLocalCompleteIntersection L (L ⊗[k] K) :=
        (isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension
          (k := k) (K := L) (S := K)).mp hCIK
      have hCIKL : IsLocalCompleteIntersection L (K ⊗[k] L) := by
        have eComm : (L ⊗[k] K) ≃ₐ[L] (K ⊗[k] L) := by
          refine
            { toRingEquiv := (Algebra.TensorProduct.comm k L K).toRingEquiv
              commutes' := ?_ }
          intro x
          rw [Algebra.TensorProduct.algebraMap_apply]
          rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
          rfl
        simpa using
          Algebra.IsLocalCompleteIntersection.of_algEquiv hCILK eComm
      exact cohenMacaulayRing_of_isLocalCompleteIntersection hCIKL
  | inr hL =>
      let _ : Algebra.EssFiniteType k L := hL
      have hPrime :
          ∀ q : PrimeSpectrum L,
            IsCompleteIntersectionOver.{u, w, w} k (Localization.AtPrime q.asIdeal) := by
        intro q
        let _ : Algebra.EssFiniteType k (Localization.AtPrime q.asIdeal) := inferInstance
        let _ : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := inferInstance
        infer_instance
      have hCIL : IsLocalCompleteIntersection k L := by
        have hTFAE :
            List.TFAE
              [ IsLocalCompleteIntersection k L
              , ∀ q : PrimeSpectrum L,
                  IsCompleteIntersectionOver.{u, w, w} k (Localization.AtPrime q.asIdeal)
              , ∀ m : MaximalSpectrum L,
                  IsCompleteIntersectionOver.{u, w, w} k (Localization.AtPrime m.asIdeal)
              ] :=
          isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings
        exact (hTFAE.out 1 0 rfl rfl).mp hPrime
      have hCIKL : IsLocalCompleteIntersection K (K ⊗[k] L) :=
        (isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension
          (k := k) (K := K) (S := L)).mp hCIL
      exact cohenMacaulayRing_of_isLocalCompleteIntersection hCIKL

/-- Lemma 10.167.1, canonical base-change form: if `k` is a field, `L / k` is a field extension,
and `K / k` is a finitely generated field extension recorded by `Algebra.EssFiniteType`, then
`K ⊗[k] L` is a Noetherian Cohen-Macaulay ring. This is the owner-aligned form used when the
finitely generated side is fixed in advance. -/
theorem cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension
    [Algebra.EssFiniteType k K] :
    CohenMacaulayRing (K ⊗[k] L) := by
  exact cohenMacaulayRing_tensorProduct_of_essFiniteType_on_either_side (k := k) (K := K) (L := L)
    (Or.inl inferInstance)

/-- Lemma 10.167.1, source-facing symmetric form: if `k` is a field and `K / k`, `L / k` are
field extensions such that one of them is finitely generated over `k`, recorded canonically by
`Algebra.EssFiniteType`, then `K ⊗[k] L` is a Noetherian Cohen-Macaulay ring. -/
theorem cohenMacaulayRing_tensorProduct_of_fieldExtensions_of_finitelyGeneratedFieldExtension
    (hfin : Algebra.EssFiniteType k K ∨ Algebra.EssFiniteType k L) :
    CohenMacaulayRing (K ⊗[k] L) := by
  exact cohenMacaulayRing_tensorProduct_of_essFiniteType_on_either_side
    (k := k) (K := K) (L := L) hfin

end
