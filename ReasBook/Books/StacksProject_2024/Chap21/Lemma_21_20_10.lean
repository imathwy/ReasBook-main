import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_31_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 21.20.10:
- primary domain: K-injective cochain complexes under exact additive adjunctions between abelian
  categories;
- inspected owner declarations:
  `CochainComplex.IsKInjective`,
  `Functor.mapHomologicalComplex`,
  `CategoryTheory.exactFunctor`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstraction:
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`.

Source/core/bridge triage:
- `source-facing`: for a flat morphism of ringed sites, the direct-image functor on module sheaves
  sends K-injective cochain complexes to K-injective cochain complexes;
- `core/canonical`: a right adjoint to an exact additive left adjoint preserves K-injective
  cochain complexes;
- `bridge/view`: this item, because after abstracting away the ringed-site realization, the only
  primitive data are the adjunction `f^* ⊣ f_*` and exactness of `f^*`.

Primitive data are therefore just the exact additive left adjoint and its right adjoint; the
K-injectivity conclusion is derived API from the canonical Chapter 13 owner theorem. The former
local declaration was only a renamed shell with the same interface, so the refined file is a
direct recall of the owner declaration.
-/

/- Lemma 21.20.10: the flat ringed-site statement is exactly the Chapter 13 theorem that a right
adjoint to an exact additive left adjoint preserves K-injective cochain complexes. -/
recall right_adjoint_preserves_isKInjective_of_exact_left_adjoint
