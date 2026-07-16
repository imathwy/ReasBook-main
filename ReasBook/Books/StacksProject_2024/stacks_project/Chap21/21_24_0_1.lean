import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Lemma_13_29_3

namespace CategoryTheory

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 21.24.0.1:
- primary domain: lower truncation resolution systems of complexes in `Mod(𝒪)` on a ringed site;
- sampled owner declarations:
  `CategoryTheory.LowerTruncationResolutionSystem`,
  `CategoryTheory.LowerTruncationResolutionSystem.intoLimit`,
  `CategoryTheory.LowerTruncationResolutionSystem.intoLimit_comp_π`;
- best owner abstraction: the Chapter 13 owner `LowerTruncationResolutionSystem`, whose derived
  API already supplies the canonical cone to the inverse system and the induced morphism to its
  limit;
- primitive data versus derived API: the primitive data are only the chosen lower truncation
  resolution system `S`, while the cone and the comparison morphism to the inverse limit are
  derived owner API and should not survive as a second Chapter 21 wrapper.

Layer triage:
- `source-facing`: the canonical morphism `F^• ⟶ lim I_n^•`
  attached to a chosen lower truncation injective system;
- `core/canonical`: `LowerTruncationResolutionSystem.intoLimit`;
- `bridge/view`: this numbered item is a direct recall of that owner in the Chapter 21 ringed-site
  setting, rather than a second local specialization wrapper.
-/

/- 21.24.0.1: the canonical morphism from `F^•` to the inverse limit of a chosen
lower truncation injective resolution system is the owner map
`LowerTruncationResolutionSystem.intoLimit`. -/
recall LowerTruncationResolutionSystem.intoLimit

/- Companion recall: composing the canonical map with the `n`th limit projection recovers the
stage comparison map. -/
recall LowerTruncationResolutionSystem.intoLimit_comp_π

end CategoryTheory
