import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap17.Definition_17_31_6
import StacksProject_2024.stacks_project.Chap18.«18_35_0_2»

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]

/- Domain-style sampling for 18.35.0.1:
- primary domain: canonical presentations of sheaves of commutative `\mathcal A`-algebras by the
  free commutative-ring sheaf on the underlying sheaf of sets;
- sampled owner declarations:
  `Sheaf.composeAndSheafify J CommRingCat.free`,
  `Sheaf.adjunction J CommRingCat.adj`,
  `presentationMap`;
- best owner abstraction: the source-facing owner is
  `presentationMap 𝒜 𝒝 : 𝒜[𝒝] ⟶ 𝒝.right`;
- primitive data: the base sheaf of rings `𝒜`, the `𝒜`-algebra sheaf `𝒝 : Under 𝒜`, the free
  commutative-ring sheaf on the underlying sheaf of sets of `𝒝`, and the induced map from the
  free-forgetful adjunction;
- derived API: none is needed here beyond direct recall of the chapter owner.

Source/core/bridge triage:
- `source-facing`: the canonical presentation morphism `\mathcal A[\mathcal B] \to \mathcal B`;
- `core/canonical`: the free-ring/sheaf adjunction `Sheaf.adjunction J CommRingCat.adj` together
  with the relative-free `\mathcal A`-algebra construction encoded in the owner notation
  `𝒜[𝒝]`;
- `bridge/view`: none; this file is recall-only for the owner morphism itself.

This file is therefore recall-only: the chapter owner already lives in `18.35.0.2`, so no parallel
local presentation map should remain here. -/

/- 18.35.0.1: for a sheaf of commutative rings `\mathcal A` on a site and a sheaf of
`\mathcal A`-algebras `\mathcal B`, the canonical presentation morphism
`\mathcal A[\mathcal B] \to \mathcal B` is the chapter owner `presentationMap`. -/
recall presentationMap

end SheafOfModules.RingedSite
