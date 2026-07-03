import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap13.Lemma_13_29_3
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/- Domain-style sampling for 21.24.0.1:
- primary domain: lower truncation resolution systems of complexes in `Mod(𝒪)` on a ringed site;
- sampled owner declarations:
  `LowerTruncationResolutionSystem`,
  `LowerTruncationResolutionSystem.cone`,
  `LowerTruncationResolutionSystem.intoLimit`,
  `LowerTruncationResolutionSystem.intoLimit_comp_π`;
- best owner abstraction: the Chapter 13 owner `LowerTruncationResolutionSystem`;
- primitive data versus derived API: the primitive data are the chosen lower truncation resolution
  system `S`, while the cone and the induced map to `lim S.diagram` are derived owner API.

Layer triage:
- `source-facing`: the canonical comparison `\mathcal F^\bullet \to \varprojlim_n \mathcal I_n^\bullet`;
- `core/canonical`: `LowerTruncationResolutionSystem.intoLimit`;
- `bridge/view`: this file is a direct specialization recall for `Mod(𝒪)`.
-/

/- 21.24.0.1: the canonical morphism from `\mathcal F^\bullet` to the inverse limit of a chosen
lower truncation injective resolution system is the owner map
`LowerTruncationResolutionSystem.intoLimit`. -/
recall LowerTruncationResolutionSystem.intoLimit

/- Companion recall: its composites with the limit projections recover the stage comparison maps.
-/
recall LowerTruncationResolutionSystem.intoLimit_comp_π

end

end CategoryTheory
