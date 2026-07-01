import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [FinitePresentation R S] [Module.Flat R R']

/- 
Domain-style sampling:
- primary domain: base change on `PrimeSpectrum` for the canonical smooth locus of a finitely
  presented ring map;
- sampled owner declarations of the same kind:
  `Algebra.smoothLocus`,
  `Algebra.smoothLocus_eq_compl_support_inter`,
  `Algebra.smoothLocus_comap_of_isLocalization`,
  `relativeDimensionAt_le_preimage_eq_baseChange`,
  `cohenMacaulayFiberLocus_baseChange_preimage_eq`;
- best owner abstraction: the canonical owner is `smoothLocus R S`; this file should state the
  base-change result directly for that owner rather than through a parallel set-builder or local
  wrapper;
- primitive data: the finitely presented map `R → S`, the flat base change `R → R'`, and the
  induced map `Spec(R' ⊗[R] S) → Spec(S)`;
- derived API: the inverse-image equality for the smooth locus under `PrimeSpectrum.comap
  includeRight.toRingHom`.

Source/core/bridge triage:
* `source-facing`: the smooth locus of a ring map;
* `core/canonical`: `Algebra.smoothLocus` and its local description via `IsSmoothAt`;
* `bridge/view`: inverse image along `PrimeSpectrum.comap includeRight.toRingHom`.
-/

-- Proof sketch: identify `smoothLocus` with the locus where the localized cotangent homology
-- vanishes and the localized Kähler differentials are free. Flat base change gives the forward
-- implication by `Algebra.tensorH1CotangentOfFlat` and preservation of freeness/projectivity.
-- For the reverse implication, localize at a prime `q'` of `R' ⊗[R] S`; since `S_q → S'_{q'}`
-- is faithfully flat, vanishing of localized `H¹(L)` descends along faithful flatness, and
-- finite-projectivity of localized Kähler differentials descends by Lemma `10.78.6`. Then apply
-- the local smoothness criterion of Lemma `10.137.11`.
/-- Lemma 10.137.17: for a finitely presented ring map `R → S` and a flat base change `R → R'`,
if `S' = R' ⊗[R] S`, then the smooth locus of `R' → S'` is the inverse image of the smooth locus
of `R → S` under the induced map `Spec(S') → Spec(S)`. -/
theorem smoothLocus_baseChange_preimage_eq :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        smoothLocus R S =
      smoothLocus R' (R' ⊗[R] S) := sorry

end Algebra
