import Mathlib
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Lemma_10_137_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

section

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S]
variable [Algebra k K] [Algebra k S] [FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- Domain-style sampling pass:

Primary domain: smoothness at a prime under tensor base change along a field extension.

Sampled owner declarations:
* `Algebra.SmoothAtPrime`;
* `Algebra.smoothAtPrime_iff_isSmoothAt`;
* `Algebra.IsSmoothAt`;
* `Algebra.smoothLocus_baseChange_preimage_eq`;
* `Algebra.smoothLocus`.

Best owner abstraction: the source-facing owner in this chapter is `SmoothAtPrime`; the canonical
local owner remains `IsSmoothAt`, and the global base-change theorem for the owner set
`smoothLocus` already exists upstream. This file should therefore state the primewise
field-extension invariance theorem using `SmoothAtPrime`, with `IsSmoothAt` kept only as a
companion bridge.

Primitive vs. derived:
* primitive data: the field extension `K / k`, the finite-type `k`-algebra `S`, and the upstairs
  prime `qK : PrimeSpectrum S_K`;
* derived API: the contracted prime `q := PrimeSpectrum.comap iSK qK`, the finite-presentation
  instances coming from finite type over fields, and the bridge to the canonical predicate
  `IsSmoothAt`.

Source/core/bridge triage:
* `source-facing`: the pointwise field-extension invariance statement at a prime;
* `core/canonical`: `SmoothAtPrime`, `IsSmoothAt`, and the owner locus `smoothLocus`;
* `bridge/view`: contraction along `iSK`, obtained by specializing
  `smoothLocus_baseChange_preimage_eq` and `smoothAtPrime_iff_isSmoothAt`.
-/

-- Proof sketch: this is the field-extension specialization of the smooth-locus base-change
-- theorem from Lemma `10.137.17`. Since finite type over a field implies finite presentation, one
-- rewrites both source-facing smoothness predicates via `smoothAtPrime_iff_isSmoothAt`, then
-- identifies both sides with membership in the corresponding smooth locus; the prime of `S`
-- corresponding to `qK` is obtained by contraction along `includeRight`.
/-- Lemma 10.137.18: for a field extension `K / k`, a finite-type `k`-algebra `S`, and a prime
`qK` of `K ⊗[k] S`, letting `q` be the corresponding prime of `S`, the algebra `S` is smooth over
`k` at `q` in the source-facing Stacks sense if and only if `K ⊗[k] S` is smooth over `K` at
`qK`. -/
@[stacks 02UQ]
theorem smoothAtPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    SmoothAtPrime k S q ↔ SmoothAtPrime K S_K qK := by
  letI : FinitePresentation k S :=
    FinitePresentation.of_finiteType.mp inferInstance
  letI : FiniteType K S_K := FiniteType.baseChange K
  letI : FinitePresentation K S_K :=
    FinitePresentation.of_finiteType.mp inferInstance
  let q := PrimeSpectrum.comap iSK qK
  change SmoothAtPrime k S q ↔ SmoothAtPrime K S_K qK
  rw [smoothAtPrime_iff_isSmoothAt k S q, smoothAtPrime_iff_isSmoothAt K S_K qK]
  change
      qK ∈ PrimeSpectrum.comap ((includeRight : S →ₐ[k] S_K).toRingHom) ⁻¹' smoothLocus k S ↔
        qK ∈ smoothLocus K S_K
  have hsmooth :
      PrimeSpectrum.comap ((includeRight : S →ₐ[k] S_K).toRingHom) ⁻¹' smoothLocus k S =
        smoothLocus K S_K :=
    smoothLocus_baseChange_preimage_eq
  rw [hsmooth]

-- Proof sketch: this is the canonical local-owner reformulation of Lemma `10.137.18`, obtained
-- by rewriting both source-facing smoothness predicates using `smoothAtPrime_iff_isSmoothAt`.
/-- Companion bridge for Lemma `10.137.18`: after rewriting `SmoothAtPrime` through the canonical
predicate `IsSmoothAt`, field extension along `K / k` preserves smoothness at the corresponding
prime ideals. -/
theorem isSmoothAt_iff_isSmoothAt_tensor_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    IsSmoothAt k q.asIdeal ↔ IsSmoothAt K qK.asIdeal := by
  letI : FinitePresentation k S :=
    FinitePresentation.of_finiteType.mp inferInstance
  letI : FiniteType K S_K := FiniteType.baseChange K
  letI : FinitePresentation K S_K :=
    FinitePresentation.of_finiteType.mp inferInstance
  let q := PrimeSpectrum.comap iSK qK
  change IsSmoothAt k q.asIdeal ↔ IsSmoothAt K qK.asIdeal
  simpa [q] using
    (smoothAtPrime_iff_isSmoothAt k S q).symm.trans
      ((smoothAtPrime_iff_of_tensorProduct_fieldExtension qK).trans
        (smoothAtPrime_iff_isSmoothAt K S_K qK))

end

end Algebra
