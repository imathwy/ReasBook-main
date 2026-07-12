import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap17.Definition_17_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RelativeDerivation

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (O₁ O₂ : Sheaf J CommRingCat.{max u v})
variable (φ : O₁ ⟶ O₂)
variable (F : SheafOfModules (ringSheaf J O₂))

/- Domain-style sampling for Definition 18.33.1:
- primary domain: relative derivations of sheaves/presheaves of modules over a morphism of sheaves
  of commutative rings;
- sampled owner declarations:
  `PresheafOfModules.Derivation'`,
  `SheafOfModules.RelativeDerivation`,
  `PresheafOfModules.Derivation'.app`,
  `PresheafOfModules.Derivation.postcomp`;
- owner abstraction: `PresheafOfModules.Derivation'`;
- primitive data: the additive sectionwise map together with vanishing on the image of `O₁` and the
  Leibniz rule;
- derived API: the sheaf-level bridge `SheafOfModules.RelativeDerivation` with notation
  `Der[φ ; F]` and the canonical owner method `PresheafOfModules.Derivation.postcomp`.

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

/- Companion recall: the exact project-level owner used here is
`SheafOfModules.RelativeDerivation`, and it is implemented as the sheaf-level specialization of the
canonical presheaf owner `PresheafOfModules.Derivation'` from
`stacks_project/Items/Chap17/Definition_17_28_1.lean`. -/
#check SheafOfModules.RelativeDerivation

/- Underlying owner recall: `SheafOfModules.RelativeDerivation` is the sheaf-level bridge to the
canonical presheaf owner. -/
#check PresheafOfModules.Derivation'
