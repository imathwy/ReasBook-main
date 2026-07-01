import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O₁ O₂ : Sheaf J CommRingCat}
variable (φ : O₁ ⟶ O₂)
variable (F : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂))

/-- The sheaf-level type of `φ`-derivations `O₂ → F`. This is the source-facing specialization of
the canonical owner `PresheafOfModules.Derivation'`; in the notation of the Stacks Project, it
realizes `Der_{O₁}(O₂, F)` while keeping the structural morphism `φ : O₁ ⟶ O₂` explicit. -/
abbrev RelativeDerivation : Type _ :=
  F.val.Derivation' φ.hom

end SheafOfModules

namespace RelativeDerivation

scoped notation "Der[" φ " ; " F "]" => SheafOfModules.RelativeDerivation φ F

end RelativeDerivation

/-- Postcomposition of a sheaf-level relative derivation by a morphism of sheaves of modules. -/
abbrev RelativeDerivation.postcomp
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {O₁ O₂ : Sheaf J CommRingCat} {φ : O₁ ⟶ O₂}
    {R : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂)}
    {F : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O₂)}
    (d : SheafOfModules.RelativeDerivation φ R) (α : R ⟶ F) :
    SheafOfModules.RelativeDerivation φ F :=
  d.postcomp α.val

open scoped RelativeDerivation

variable {X : TopCat.{u}}
variable (O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X)
variable (φ : O₁ ⟶ O₂)
variable (F : SheafOfModules ((sheafCompose (Opens.grothendieckTopology X)
  (forget₂ CommRingCat RingCat)).obj O₂))

/- Domain-style sampling for Definition 17.28.1:
- primary domain: relative derivations of presheaves/sheaves of modules over a sheaf of rings;
- sampled owner declarations:
  `PresheafOfModules.Derivation'`,
  `SheafOfModules.RelativeDerivation`,
  `PresheafOfModules.Derivation'.app`,
  `PresheafOfModules.DifferentialsConstruction.derivation'`,
  `PresheafOfModules.Derivation'.Universal.mk`;
- owner abstraction: `PresheafOfModules.Derivation'`;
- primitive data: the additive map on local sections, together with vanishing on the image of
  `O₁` and the Leibniz rule;
- derived API: the sheaf-level bridge `SheafOfModules.RelativeDerivation` with notation
  `Der[φ ; F]`, evaluation on opens via `Derivation'.app`, the sheaf-level bridge
  `RelativeDerivation.postcomp`, and the universal
  structure used to define relative differentials.

Source/core/bridge triage:
- `core/canonical`: `PresheafOfModules.Derivation'`;
- `bridge/view`: `SheafOfModules.RelativeDerivation φ F` and the notation `Der[φ ; F]`;
- this item is the source-facing sheaf-level specialization of the canonical owner, not a second
  root owner. -/

/- Definition 17.28.1: for a topological space `X`, a morphism `φ : O₁ ⟶ O₂` of sheaves of
commutative rings on `X`, and an `O₂`-module sheaf `F`, the source-facing type
`Der[φ ; F]` is the sheaf-level specialization of the canonical owner
`PresheafOfModules.Derivation'` that realizes
`Der_{O₁}(O₂, F)`. -/
#check Der[φ ; F]

/- Companion recall: the owner of relative derivations on presheaves of modules is
`PresheafOfModules.Derivation'`. -/
recall PresheafOfModules.Derivation'
