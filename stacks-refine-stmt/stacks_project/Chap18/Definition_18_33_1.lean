import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap17.Definition_17_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RelativeDerivation

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (O₁ O₂ : Sheaf J CommRingCat)
variable (φ : O₁ ⟶ O₂)
variable (F : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂))

/- Domain-style sampling for Definition 18.33.1:
- primary domain: relative derivations of sheaves/presheaves of modules over a morphism of sheaves
  of commutative rings;
- sampled owner declarations:
  `PresheafOfModules.Derivation'`,
  `SheafOfModules.RelativeDerivation`,
  `PresheafOfModules.Derivation'.app`,
  `RelativeDerivation.postcomp`;
- owner abstraction: `PresheafOfModules.Derivation'`;
- primitive data: the additive sectionwise map together with vanishing on the image of `O₁` and the
  Leibniz rule;
- derived API: the sheaf-level bridge `SheafOfModules.RelativeDerivation` with notation
  `Der[φ ; F]`.

Source/core/bridge triage:
- `core/canonical`: `PresheafOfModules.Derivation'`;
- `bridge/view`: `SheafOfModules.RelativeDerivation φ F` and the notation `Der[φ ; F]`;
- this file is a canonical recall of the sheaf-level bridge, not a second owner declaration. -/

/- Definition 18.33.1: for a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a site and
an `O₂`-module sheaf `F`, the type `Der[φ ; F]` is the canonical notion of a
`φ`-derivation `O₂ → F`, i.e. an additive map on local sections that vanishes on the image of
`O₁` and satisfies the Leibniz rule; this is the Lean realization of
`Der_{O₁}(O₂, F)`. -/
#check Der[φ ; F]

/- Companion recall: the upstream canonical owner is `PresheafOfModules.Derivation'`, and
`Der[φ ; F]` is its sheaf-level source-facing specialization from
`stacks_project/Items/Chap17/Definition_17_28_1.lean`. -/
recall PresheafOfModules.Derivation'
