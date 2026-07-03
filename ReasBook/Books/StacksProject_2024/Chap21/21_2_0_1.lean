import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.«20_2_0_3»

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 21.2.0.1:
- primary domain: sheaf cohomology on a site, computed from a chosen injective resolution by
  applying the sections functor over a fixed object;
- sampled owner API:
  `CategoryTheory.Sheaf.H'`,
  `sheafSections`,
  `InjectiveResolution`,
  `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- best owner abstraction:
  `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- primitive data: a site `(C, J)`, a sheaf `F`, an object `U : C`, an index `i : ℕ`, and a chosen
  injective resolution `I : InjectiveResolution F`;
- derived API: the canonical isomorphism identifying `F.H' i U` with the degree-`i` homology of
  the sections complex of `I`.

Source/core/bridge triage:
- `source-facing`: the computation of `H^i(U, F)` by the homology of the sections complex of an
  injective resolution;
- `core/canonical`:
  `CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution`;
- `bridge/view`: this numbered item is only a reuse of that existing chapter-level theorem.

This file adds no new mathematical data beyond the canonical owner theorem already present in
Chapter 20, so the refined entry should recall that owner directly instead of keeping a parallel
local theorem name. -/

/- 21.2.0.1: for an object `U` of the site and an injective resolution `I` of an abelian sheaf
`F`, the cohomology object `H^i(U, F)` is canonically isomorphic to the `i`-th homology of the
sections complex `Γ(U, I^\bullet)`. -/
recall CategoryTheory.Sheaf.cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution
