import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_135_11 (from Chap10) -/
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

/-! ### Lemma_10_135_12 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

open IsLocalRing
open RingTheory

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsRegularLocalRing R] [Module.Flat R S]

/- Domain-style sampling pass.

Primary domain: flat local maps of local rings, their canonical closed fibers, and regular
sequence generation of ideals.

Sampled owner declarations:
* `RingHom.KernelIsGeneratedByRegularSequence`;
* `Ideal.IsGeneratedByRegularSequence`;
* `Ideal.Fiber`;
* `Ideal.ker_quotientMap_mk`.

Best owner abstraction: `RingHom.KernelIsGeneratedByRegularSequence` is the primitive owner for
regular-sequence generation, `Ideal.IsGeneratedByRegularSequence` is the ideal-level bridge via the
quotient map, and the closed fiber should live on `Ideal.Fiber (maximalIdeal R) S` rather than on
an ad hoc quotient-map wrapper.

Primitive vs. derived:
* primitive data: the ideals `I ⊂ R`, `J ⊂ S`, the flat local quotient map `R ⧸ I → S ⧸ J`, and
  the closed-fiber ideal `Ideal.map (algebraMap S ClosedFiber) J`;
* derived API: identifying the latter with the kernel of the induced quotient map on closed
  fibers.

Source/core/bridge triage:
* `source-facing`: Lemma `10.135.12` itself;
* `core/canonical`: `Ideal.Fiber`, `Ideal.IsGeneratedByRegularSequence`,
  `RingHom.KernelIsGeneratedByRegularSequence`;
* `bridge/view`: the quotient-map kernel description supplied by `Ideal.ker_quotientMap_mk`.
-/

-- Proof sketch: use the regular-sequence presentation of `J / 𝔪_R J` on the closed fibre and
-- Lemma `10.99.3` to lift it to part of a regular sequence generating `J`. Then compare the
-- resulting quotient presentation of `B = S / J` with the flat quotient `R / I → S / J`, use
-- faithful flatness to identify the remaining generators with a generating set of `I`, and apply
-- Lemma `10.135.6` to conclude that `I` is generated by a regular sequence.
/-- Lemma 10.135.12: if `R → S` is a flat local homomorphism of local rings, `R` and the closed
fibre `S / 𝔪_RS` are regular local rings, `J ⊂ S` and its image in the closed fibre are generated
by regular sequences, and the induced quotient map `R ⧸ I → S ⧸ J` is flat, then `I` is generated
by a regular sequence. -/
theorem kernelIsGeneratedByRegularSequence_of_flat_local_quotient_square_of_regular_closedFiber
    (I : Ideal R) (J : Ideal S) (hIJ : I ≤ Ideal.comap (algebraMap R S) J)
    (hclosedFiber : IsRegularLocalRing ClosedFiber)
    (hJ : J.IsGeneratedByRegularSequence)
    (hJbar : (Ideal.map (algebraMap S ClosedFiber) J).IsGeneratedByRegularSequence)
    (hflatAB : (Ideal.quotientMap J (algebraMap R S) hIJ).Flat) :
    I.IsGeneratedByRegularSequence := sorry

end
