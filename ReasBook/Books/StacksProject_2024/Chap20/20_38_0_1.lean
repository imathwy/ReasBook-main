import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_29_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})

/- Domain-style sampling for 20.38.0.1:
- primary domain: lower truncation resolution systems of cochain complexes in an abelian category,
  specialized here to `(RingedSpace.Modules X)`;
- sampled owner declarations:
  `LowerTruncationResolutionSystem`,
  `LowerTruncationResolutionSystem.cone`,
  `LowerTruncationResolutionSystem.intoLimit`,
  `LowerTruncationResolutionSystem.intoLimit_comp_π`;
- best owner abstraction: the Chapter 13 owner `LowerTruncationResolutionSystem`, whose derived API
  already supplies the canonical cone to the inverse system and the induced morphism to its limit;
- primitive data versus derived API: the primitive data are only the chosen resolution system
  `S`; the cone and the comparison morphism to the inverse limit are derived owner API and should
  not survive as a second Chapter 20 wrapper.

Layer triage:
- `source-facing`: the canonical morphism `\mathcal F^\bullet \to \varprojlim_n \mathcal I_n^\bullet`
  attached to a chosen lower truncation injective system;
- `core/canonical`: `LowerTruncationResolutionSystem.intoLimit`;
- `bridge/view`: this numbered item is now a direct recall of that owner, specialized to
  `(RingedSpace.Modules X)`.
-/

/- 20.38.0.1: the canonical morphism `\mathcal F^\bullet \to \mathcal I^\bullet` into the
inverse-limit complex attached to a chosen lower truncation resolution system is the owner map
`LowerTruncationResolutionSystem.intoLimit`. -/
recall LowerTruncationResolutionSystem.intoLimit

/- Companion recall: composing the canonical map with the `n`th limit projection recovers the
stage comparison map. -/
recall LowerTruncationResolutionSystem.intoLimit_comp_π

end

end AlgebraicGeometry.RingedSpace
