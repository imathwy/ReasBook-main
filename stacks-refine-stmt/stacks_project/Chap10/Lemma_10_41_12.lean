import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

namespace Module

/- Domain triage:
* primary domain: support of finite modules on prime spectra, together with lifting of
  generalizations along the induced support map;
* core/canonical owners: `Module.support S N` for the subset of `Spec S` and `GeneralizingMap`
  for the topological lifting property;
* sampled canonical declarations:
  `Module.support`,
  `Module.mem_support_iff_nontrivial_residueField_tensorProduct`,
  `Module.support_subset_preimage_comap`,
  and `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`;
* layer: `bridge/view`, since the source theorem is about the canonical map from the support of
  `N` to `Spec R`, not about introducing a new owner object.

Primitive-vs-derived split:
* primitive data: the finite `S`-module `N`, its `R`-flatness, and the canonical subset
  `Module.support S N`;
* derived API: the induced map `Module.support S N → PrimeSpectrum R`, written canonically as the
  composite of the subtype inclusion with `PrimeSpectrum.comap (algebraMap R S)`.
-/
/-- Lemma 10.41.12: if `N` is a finite `S`-module that is flat over `R`, then generalizations
lift along the support map `support S N → Spec R` induced by
`PrimeSpectrum.comap (algebraMap R S)`. Equivalently, if `p ⤳ p'` in `Spec R` and
`q' ∈ support S N` lies over `p'`, then there exists `q ∈ support S N` with `q ⤳ q'`
lying over `p`. -/
theorem generalizingMap_support_comap_of_flat :
    GeneralizingMap (comap (algebraMap R S) ∘ ((↑) : support S N → PrimeSpectrum S)) := by
  -- Proof sketch: rewrite membership in the support of a finite flat module using the nonvanishing
  -- of its fibers. Given a generalization `p ⤳ p'` in `Spec R` below a point
  -- `q' ∈ Module.support S N`, use the fiber criterion for finite support and flat base change to
  -- deduce that the fiber over `p` is also nonzero. Choosing a prime in the support of that fiber
  -- below `q'` produces the required lift `q ∈ Module.support S N` over `p`.
  sorry

end Module

end
