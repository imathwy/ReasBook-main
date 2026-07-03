import Mathlib
import stacks_project.Chap10.Definition_10_104_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- 
Domain-style sampling:
- primary domain: Cohen-Macaulay local rings under tensor base change along a field extension;
- sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.LocallyCohenMacaulay`,
  `primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension`,
  `flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial`;
- best owner abstraction: the local Cohen-Macaulay owner `Module.CohenMacaulay` on the localized
  self-modules downstairs and upstairs;
- primitive data: the finite type `k`-algebra `S` and the upstairs prime
  `qK : PrimeSpectrum S_K`; the downstairs prime is the canonical contraction
  `PrimeSpectrum.comap iSK qK`;
- derived API: the local dimension comparison from Lemma `10.116.6` and the flat-locus
  description from Lemma `10.130.1`, which support the proof but should not be repackaged as a
  second public owner here.

Source/core/bridge triage:
* `source-facing`: invariance of the Cohen-Macaulay condition for the local rings at the canonical
  contracted/lying-over pair of primes under the tensor base change `S ↦ K ⊗[k] S`;
* `core/canonical`: `Module.CohenMacaulay` on `Localization.AtPrime q.asIdeal` and
  `Localization.AtPrime qK.asIdeal`;
* `bridge/view`: the tensor-product map `iSK` and the induced contraction
  `PrimeSpectrum.comap iSK qK`.

The public statement should therefore stay directly on `Module.CohenMacaulay`; adding a separate
ring-level alias here would only duplicate the chapter owner abstraction.
-/

-- Proof sketch: after replacing `S` by a localization away from `q`, use Noether normalization to
-- choose a finite injective map `k[x₁, …, x_d] → S`. Base change this map to `K[x₁, …, x_d] →
-- K ⊗[k] S`, use Lemma `10.116.6` to identify the relevant relative dimensions, and apply Lemma
-- `10.130.1` to reduce both Cohen-Macaulay conditions to flatness of the two vertical maps in the
-- normalization square. Since the bottom horizontal map is flat, the two flatness conditions are
-- equivalent.
/-- Lemma 10.130.6: for a field extension `K / k`, a finite type `k`-algebra `S`, a prime
`qK : Spec(K ⊗[k] S)`, and its contraction `q := PrimeSpectrum.comap iSK qK`, the local ring
`S_q` is Cohen-Macaulay if and only if the local ring `(K ⊗[k] S)_{qK}` is Cohen-Macaulay. -/
theorem cohenMacaulay_localizationAtPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) ↔
      Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
        (Localization.AtPrime qK.asIdeal) := sorry

end
