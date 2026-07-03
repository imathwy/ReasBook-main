import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_167_1 (from Chap10) -/
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

/-! ### Lemma_10_167_2 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {S : Type w} [CommRing S] [Algebra k S] [IsNoetherianRing S]

local notation "S_K" => K ⊗[k] S

/- Domain-style sampling:
- primary domain: Cohen-Macaulay local rings under tensor base change along a finitely generated
  field extension;
- sampled owner declarations of the same kind:
  `Algebra.EssFiniteType` from Definition `9.6.6`,
  `isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension` from Lemma `10.31.8`,
  `cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension` from Lemma `10.167.1`,
  `cohenMacaulayRing_iff_source_and_closedFiber` from Lemma `10.163.3`;
- best owner abstraction: the field-extension hypothesis belongs on the canonical owner
  `Algebra.EssFiniteType k K`, while the Cohen-Macaulay condition itself belongs directly on the
  local self-module owner `Module.CohenMacaulay`;
- primitive data: only the upstairs prime `qK` of `K ⊗[k] S`;
- derived API: Noetherianity of `S_K`, the local flatness of the induced map on localizations, and
  the Cohen-Macaulayness of the closed fiber over the canonical contraction `qK.under S`.

Source/core/bridge triage:
* `source-facing`: the Stacks lemma comparing the local rings at an upstairs prime and its
  downstairs contraction;
* `core/canonical`: `Algebra.EssFiniteType k K` and `Module.CohenMacaulay` on the localized
  self-modules;
* `bridge/view`: the induced localization map
  `Localization.AtPrime (qK.under S) → Localization.AtPrime qK` and the closed-fiber comparison
  with `K ⊗[k] (qK.under S).ResidueField`.

This file therefore should not keep a parallel finite-type field-extension hypothesis or a local
duplicate of the tensor-product Noetherianity theorem. Once `qK` is fixed, the downstairs prime is
canonically `qK.under S`, so separate public data `q` and `qK.LiesOver q` would be redundant.
-/

-- The tensor product ring is Noetherian by the chapter owner theorem for finitely generated field
-- extensions, already formulated on `Algebra.EssFiniteType`.
local instance tensorProduct_isNoetherianRing : IsNoetherianRing S_K :=
  isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension

-- Proof sketch: the local map `S_(q_K ∩ S) → (K ⊗[k] S)_{q_K}` is flat because it is obtained from the
-- flat base-change map `S → K ⊗[k] S` by localization. Its closed fiber is a localization of
-- `κ(q_K ∩ S) ⊗[k] K`, which is Cohen-Macaulay by Lemma `10.167.1`. Apply Lemma `10.163.3` to
-- this flat local map and the Cohen-Macaulay closed fiber.
/-- Lemma 10.167.2: for a field `k`, a Noetherian `k`-algebra `S`, a finitely generated field
extension `K / k`, recorded canonically by `Algebra.EssFiniteType k K`, and a prime `q_K` of
`K ⊗[k] S`, the local ring `S_(q_K ∩ S)` is Cohen-Macaulay if and only if
`(K ⊗[k] S)_{q_K}` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_localizationAtPrime_under_iff_tensorProduct_localizationAtPrime
    (qK : Ideal S_K) [qK.IsPrime] :
    Module.CohenMacaulay (Localization.AtPrime (qK.under S)) (Localization.AtPrime (qK.under S)) ↔
      Module.CohenMacaulay (Localization.AtPrime qK) (Localization.AtPrime qK) := sorry

end
