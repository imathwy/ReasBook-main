import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap17.Lemma_17_31_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.28.7:
- primary domain: stalks of sheaves of relative differentials on a topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_stalkIso`,
  `CommRingCat.KaehlerDifferential`,
  `TopCat.Presheaf.stalkFunctor`;
- best owner abstraction: the source-facing sheaf owner `Ω(φ)`, with the stalk comparison already
  exposed canonically by `TopCat.Sheaf.relativeDifferentials_stalkIso`;
- primitive data: none beyond that owner comparison;
- derived API: this file is recall-only.

Source/core/bridge triage:
- `source-facing`: the textbook stalk formula `(Ω_{O₂/O₁})_x ≅ Ω_{(O₂)_x/(O₁)_x}`;
- `core/canonical`: `Ω(φ)` and the canonical bridge
  `TopCat.Sheaf.relativeDifferentials_stalkIso`;
- `bridge/view`: this file simply recalls that exact comparison in the relative-differentials
  vocabulary, rather than keeping a parallel local wrapper. -/

/- Lemma 17.28.7: the stalk of `Ω(φ)` at `x` is canonically isomorphic to the Kähler
differential module of the induced morphism on stalk rings. This is exactly the owner comparison
`TopCat.Sheaf.relativeDifferentials_stalkIso`; no second local wrapper is needed. -/
recall TopCat.Sheaf.relativeDifferentials_stalkIso

end TopCat.Sheaf
