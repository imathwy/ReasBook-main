import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_116_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_135_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_135_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- Domain-style sampling pass.

Primary domain: local complete intersections under tensor base change along a field extension.

Sampled owner declarations:
* `IsLocalCompleteIntersection`;
* `IsCompleteIntersectionOver`;
* `isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings`;
* `isCompleteIntersectionOver_atPrime_iff_of_tensorProduct_fieldExtension`.

Best owner abstraction: the source-facing owner stays `IsLocalCompleteIntersection k S`, while the
canonical local-ring owner is primewise `IsCompleteIntersectionOver`. The tensor-product prime
contraction and lifting data are bridge/view support only and should not be repackaged.

Primitive vs. derived:
* primitive data: the field extension `K / k` and the `k`-algebra `S`;
* derived API: finite presentation and finite type from either local complete-intersection owner,
  together with the primewise local-ring characterization and the upstairs/downstairs comparison
  at a prime.

Source/core/bridge triage:
* `source-facing`: the theorem below on `IsLocalCompleteIntersection`;
* `core/canonical`: `IsLocalCompleteIntersection` together with primewise
  `IsCompleteIntersectionOver`;
* `bridge/view`: `PrimeSpectrum.comap iSK` and the choice of a prime of `S_K` over a given prime
  of `S`.
-/

-- Proof sketch: combine the local characterization of local complete intersections from Lemma
-- `10.135.9` with the local complete-intersection comparison after field extension from Lemma
-- `10.135.10`. In each direction, the finite-presentation and finite-type hypotheses needed by the
-- bridge lemmas are recovered internally from the corresponding local complete-intersection owner.
-- The forward direction is obtained by applying the local statement at every prime of `K ⊗[k] S`;
-- the reverse direction is checked at maximal ideals of `S` by choosing a prime of the tensor
-- product above each maximal ideal and descending the complete-intersection property.
/-- Lemma 10.135.11: for a field extension `K / k` and a `k`-algebra `S`, `S` is a local complete
intersection over `k` if and only if the base change `K ⊗[k] S` is a local complete intersection
over `K`. -/
theorem isLocalCompleteIntersection_iff_of_tensorProduct_fieldExtension :
    IsLocalCompleteIntersection k S ↔ IsLocalCompleteIntersection K S_K := by
  have hTFAE_S :
      List.TFAE
        [ IsLocalCompleteIntersection k S
        , ∀ q : PrimeSpectrum S,
            IsCompleteIntersectionOver.{u, w, w} k (Localization.AtPrime q.asIdeal)
        , ∀ m : MaximalSpectrum S,
            IsCompleteIntersectionOver.{u, w, w} k (Localization.AtPrime m.asIdeal)
        ] :=
    isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings
  have hTFAE_SK :
      List.TFAE
        [ IsLocalCompleteIntersection K S_K
        , ∀ qK : PrimeSpectrum S_K,
            IsCompleteIntersectionOver.{v, max v w, max v w} K
              (Localization.AtPrime qK.asIdeal)
        , ∀ mK : MaximalSpectrum S_K,
            IsCompleteIntersectionOver.{v, max v w, max v w} K
              (Localization.AtPrime mK.asIdeal)
        ] :=
    isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings
  have hPrimeBridge [Algebra.FiniteType k S] (qK : PrimeSpectrum S_K) :
      let q := PrimeSpectrum.comap iSK qK
      IsCompleteIntersectionOver.{u, w, w} k (Localization.AtPrime q.asIdeal) ↔
        IsCompleteIntersectionOver.{v, max v w, max v w} K
          (Localization.AtPrime qK.asIdeal) :=
    isCompleteIntersectionOver_atPrime_iff_of_tensorProduct_fieldExtension qK
  have hExistsPrimeOver [Algebra.FiniteType k S] :
      ∀ q : PrimeSpectrum S,
        ∃ qK : PrimeSpectrum S_K,
          PrimeSpectrum.comap iSK qK = q ∧ relativeDimensionAt S S_K qK = 0 :=
    exists_primeSpectrum_tensorProduct_fieldExtension_with_relativeDimensionAt_eq_zero
  constructor
  · intro hS
    letI : IsLocalCompleteIntersection k S := hS
    letI : Algebra.FinitePresentation k S := inferInstance
    letI : Algebra.FiniteType k S := inferInstance
    have hPrime :
        ∀ q : PrimeSpectrum S,
          IsCompleteIntersectionOver.{u, w, w} k (Localization.AtPrime q.asIdeal) :=
      (hTFAE_S.out 0 1 rfl rfl).mp hS
    exact
      (hTFAE_SK.out 1 0 rfl rfl).mp <| fun qK ↦ by
      simpa using
        (hPrimeBridge qK).mp (hPrime (PrimeSpectrum.comap iSK qK))
  · intro hSK
    have hPrimeK :
        ∀ qK : PrimeSpectrum S_K,
          IsCompleteIntersectionOver.{v, max v w, max v w} K
            (Localization.AtPrime qK.asIdeal) :=
      (hTFAE_SK.out 0 1 rfl rfl).mp hSK
    letI : IsLocalCompleteIntersection K S_K := hSK
    letI : Algebra.FinitePresentation K S_K := inferInstance
    letI : Algebra.FinitePresentation k S :=
      by
        simpa using
          Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat K
    letI : Algebra.FiniteType k S := inferInstance
    exact
      (hTFAE_S.out 1 0 rfl rfl).mp <| fun q ↦ by
      obtain ⟨qK, hqK, _⟩ := hExistsPrimeOver q
      subst q
      exact (hPrimeBridge qK).mpr (hPrimeK qK)

end
