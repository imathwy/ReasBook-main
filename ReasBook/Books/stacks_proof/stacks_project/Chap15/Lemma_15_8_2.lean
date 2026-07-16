import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap15.Definition_15_8_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 15.8.2:
- primary domain: determinantal/Fitting ideals attached to finite free presentations of modules
  over a commutative ring;
- sampled declarations:
  `Matrix.minorIdeal`,
  `presentationFittingIdeal`,
  `presentationFittingIdeal_eq_of_surjective`,
  `fittingIdeal_eq_presentationFittingIdeal`;
- best owner abstraction: `presentationFittingIdeal`; the matrix-minor construction is the lower
  owner layer, and the intrinsic module-level `fittingIdeal` is derived downstream from the
  presentation-independence statement;
- primitive data: a finite free presentation `π : (Fin n → R) →ₗ[R] M`;
- derived API: independence of `presentationFittingIdeal` from the chosen surjective presentation,
  and the induced intrinsic `fittingIdeal`.

Source/core/bridge triage:
- `source-facing`: the presentation-level Fitting ideal and its invariance under changing the
  chosen finite free presentation;
- `core/canonical`: `presentationFittingIdeal`;
- `bridge/view`: `fittingIdeal_eq_presentationFittingIdeal`.

Lemma 15.8.2 is recall-shaped in this chapter: the owner declaration and the presentation
independence theorem already live in `Definition_15_8_3`, so this file should reuse them directly
rather than restating parallel local copies. -/
/- The presentation-level Fitting-ideal owner is `presentationFittingIdeal`. -/
recall presentationFittingIdeal

/- Lemma 15.8.2: the presentation-level Fitting ideal is independent of the chosen surjective
finite free presentation. -/
recall presentationFittingIdeal_eq_of_surjective
