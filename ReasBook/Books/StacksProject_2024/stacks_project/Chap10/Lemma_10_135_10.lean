import Mathlib
import StacksProject_2024.Chap10.Definition_10_135_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- Domain-style sampling pass.

Primary domain: local complete intersections under tensor base change along a field extension.

Sampled owner declarations:
* `IsCompleteIntersectionOver`;
* `completeIntersectionOver_atPrime_tfae`;
* `cohenMacaulay_localizationAtPrime_iff_of_tensorProduct_fieldExtension`;
* `Algebra.isSmoothAt_iff_isSmoothAt_tensor_fieldExtension`.

Best owner abstraction: the public statement should stay directly on the canonical local owner
`IsCompleteIntersectionOver` for the localized rings. The contraction `PrimeSpectrum.comap iSK qK`
is bridge/view data induced by the tensor-product owner map `iSK`; it should not be repackaged as
an extra local `abbrev`.

Primitive vs. derived:
* primitive data: the finite type `k`-algebra `S`, the extension field `K`, and the upstairs prime
  `qK : PrimeSpectrum S_K`;
* derived API: the downstairs prime `PrimeSpectrum.comap iSK qK` and the local-ring comparison
  theorem below.

Source/core/bridge triage:
* `source-facing`: invariance of the complete-intersection condition on the local rings at a prime
  under the base change `S ↦ K ⊗[k] S`;
* `core/canonical`: `IsCompleteIntersectionOver` on the two local rings;
* `bridge/view`: the contraction `PrimeSpectrum.comap iSK qK`.
-/

-- Proof sketch: use Lemma `10.135.8` to characterize complete intersections at a prime by the
-- presentation-theoretic criterion of Lemma `10.135.4`. After base change from `k` to `K`, the
-- relevant codimension is unchanged by Lemma `10.116.6`, and the minimal number of generators of
-- the localized defining ideal is preserved by the residue-field comparison and Nakayama's lemma.
/-- Lemma 10.135.10: for a field extension `K / k`, a finite type `k`-algebra `S`, and a prime
`qK` of `K ⊗[k] S` with corresponding prime `q` of `S`, the local ring `S_q` is a complete
intersection over `k` if and only if the local ring `(K ⊗[k] S)_{qK}` is a complete intersection
over `K`. -/
theorem isCompleteIntersectionOver_atPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      IsCompleteIntersectionOver K (Localization.AtPrime qK.asIdeal) := sorry

end
