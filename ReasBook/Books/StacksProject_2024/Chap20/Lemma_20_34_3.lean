import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_31_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 20.34.3:
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
- `source-facing`: for a closed immersion `i : Z → X`, the sections-with-support functor
  `\mathcal H_Z` sends K-injective complexes of `\mathcal O_X`-modules to K-injective complexes of
  `\mathcal O_X|_Z`-modules;
- `core/canonical`: a right adjoint to an exact additive left adjoint preserves K-injective
  cochain complexes;
- `bridge/view`: this item, because after abstracting away the ringed-space realization, the only
  primitive data are the adjunction `i_* ⊣ \mathcal H_Z` and exactness of `i_*`.

Primitive data are therefore just the exact additive left adjoint and its right adjoint; the
K-injectivity of the mapped complex is derived API from the canonical Chapter 13 owner theorem.
Keeping a second theorem here with the same interface would be a duplicate local wrapper, so the
refined file is a direct recall of the owner declaration.
-/

/- Lemma 20.34.3: the closed-subset statement is exactly the Chapter 13 theorem saying that a
right adjoint to an exact additive left adjoint preserves K-injective cochain complexes. -/
recall right_adjoint_preserves_isKInjective_of_exact_left_adjoint
