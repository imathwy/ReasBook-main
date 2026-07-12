import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Global_sections_module_owners_core

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedGlobalSections RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for 20.14.1.1:
- primary domain: derived global sections and derived pushforward for `𝒪_X`-modules on
  ringed spaces;
- sampled owner declarations:
  `globalSectionsRing`,
  `moduleGlobalSectionsFunctor`,
  `moduleDerivedGlobalSections`,
  `modulePushforwardToDerived`,
  `modulePushforwardToDerived_hasRightDerivedFunctor`,
  `moduleDerivedPushforwardComparison`,
  `moduleDerivedGlobalSectionsMap`;
- best owner abstraction:
  `source-facing`: the Stacks item recording that `RΓ(X,-)` and `Rf_*` are the total right derived
  functors of the clean underived global-sections and pushforward owners, together with the
  universal comparison morphism attached to `φ : 𝒢 ⟶ f_* ℱ`;
  `core/canonical`: the clean Chapter 20 owners `globalSectionsRing`,
    `moduleGlobalSectionsFunctor`, `moduleDerivedGlobalSections`,
    `modulePushforwardToDerived`, `modulePushforwardToDerived_hasRightDerivedFunctor`,
    `moduleDerivedPushforwardComparison`, `moduleDerivedGlobalSectionsMap`, and the scoped
    notations `RΓ(X)` and `R(f)_*`;
  `bridge/view`: this numbered file is a source-label bridge from the clean underived owners to the
    Chapter 20 derived owners and their source-facing comparison morphisms.

This file therefore keeps the clean underived recalls, recalls the Chapter 20 owners
`RΓ(X)` and `R(f)_*`, and uses the canonical comparison maps
`moduleDerivedPushforwardComparison` and `moduleDerivedGlobalSectionsMap` on the source-facing
surface. The generic `Functor.totalRightDerived` and `Functor.totalRightDerivedUnit`
constructions remain encapsulated in `Global_sections_module_owners_core`. -/

section

variable (X : RingedSpace.{u})

/- 20.14.1.1: the ring of global sections of the structure sheaf is the coefficient ring for
module-valued derived global sections. -/
recall globalSectionsRing

/- 20.14.1.1: underived global sections of `𝒪_X`-modules are evaluation at the terminal open,
valued in modules over `Γ(X, 𝒪_X)`. -/
recall moduleGlobalSectionsFunctor

/- 20.14.1.1: the source-facing `RΓ(X,-)` is the Chapter 20 owner for the total right derived
functor of underived global sections. -/
#check RΓ(X)

end

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(f _*).Additive]

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "singleX" => DerivedCategory.singleFunctor ModX (0 : ℤ)
local notation "singleY" => DerivedCategory.singleFunctor ModY (0 : ℤ)

/- 20.14.1.1: the clean underived input for derived pushforward is cochain-level pushforward
followed by localization. -/
recall modulePushforwardToDerived

/- 20.14.1.1: this clean underived owner admits the Chapter 20 derived pushforward functor,
written on the source-facing surface as `R(f)_*`. -/
#check (R(f)_* : DerivedCategory ModX ⥤ DerivedCategory ModY)

/- 20.14.1.1: the cochain-level pushforward owner carries the canonical Chapter 20
right-derived-functor witness. -/
recall modulePushforwardToDerived_hasRightDerivedFunctor

/- 20.14.1.1: the source-facing comparison map `𝒢[0] ⟶ Rf_*(ℱ[0])` attached to
`φ : 𝒢 ⟶ f_* ℱ` is the canonical Chapter 20 comparison owner, with target written using
the notation `R(f)_*`. -/
recall moduleDerivedPushforwardComparison

#check
  (fun (𝒢 : ModY) (ℱ : ModX) (φ : 𝒢 ⟶ (f _*).obj ℱ) ↦
    (moduleDerivedPushforwardComparison f 𝒢 ℱ φ :
      (singleY).obj 𝒢 ⟶ (R(f)_*).obj ((singleX).obj ℱ)))

/- 20.14.1.1: applying `RΓ(Y,-)` to the canonical comparison owner yields the induced map on
derived global sections. -/
recall moduleDerivedGlobalSectionsMap

#check
  (fun (𝒢 : ModY) (ℱ : ModX) (φ : 𝒢 ⟶ (f _*).obj ℱ) ↦
    (moduleDerivedGlobalSectionsMap f 𝒢 ℱ φ :
      (RΓ(Y)).obj ((singleY).obj 𝒢) ⟶
        (RΓ(Y)).obj ((R(f)_*).obj ((singleX).obj ℱ))))

end

end AlgebraicGeometry.RingedSpace

end
