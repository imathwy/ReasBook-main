import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-
Domain-style sampling:
- primary domain: the canonical presentation of Kähler differentials;
- sampled owner declarations:
  `KaehlerDifferential.kerTotal`,
  `KaehlerDifferential.kerTotal_eq`,
  `KaehlerDifferential.quotKerTotalEquiv`,
  `KaehlerDifferential.linearCombination_surjective`;
- owner abstraction: `KaehlerDifferential.kerTotal R S`.

Source/core/bridge triage:
- `source-facing`: the textbook additive, Leibniz, and base-ring relations for `Ω[S⁄R]`;
- `core/canonical`: the relation submodule `KaehlerDifferential.kerTotal R S` and its quotient
  presentation;
- this file is a recall-only bridge to that owner API, not a second owner.
-/

/- 17.28.2.1: the textbook additive, Leibniz, and base-ring relations presenting
`Ω[S⁄R]` are already packaged canonically by `KaehlerDifferential.kerTotal R S`. -/
recall KaehlerDifferential.kerTotal

/- Companion recall: the canonical presentation map
`Finsupp.linearCombination S (KaehlerDifferential.D R S) : (S →₀ S) →ₗ[S] Ω[S⁄R]`
has kernel exactly `KaehlerDifferential.kerTotal R S`. -/
recall KaehlerDifferential.kerTotal_eq

/- Companion recall: quotienting the free module `S →₀ S` by that canonical relation submodule
recovers `Ω[S⁄R]`. -/
recall KaehlerDifferential.quotKerTotalEquiv

/- Companion recall: the canonical presentation map is surjective. -/
recall KaehlerDifferential.linearCombination_surjective

end
