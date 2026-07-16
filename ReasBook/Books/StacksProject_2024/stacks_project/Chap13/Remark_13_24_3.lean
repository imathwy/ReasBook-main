import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap06.Definition_6_6_1
import StacksProject_2024.stacks_project.Chap06.Definition_6_10_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_23_4
import StacksProject_2024.stacks_project.Chap19.Lemma_19_5_1
import StacksProject_2024.stacks_project.Chap19.Proposition_19_8_5

-- Declarations for this item will be appended below by the statement pipeline.

open CochainComplex
open CategoryTheory.GrothendieckTopology
open scoped AlgebraicGeometry

universe w v u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling:
- primary domain: enough injectives in abelian categories of modules, sheaves of modules, and
  presheaves of modules, together with the immediate Chapter 13 resolution-functor consequence;
- sampled owner declarations:
  `EnoughInjectives`,
  `modulesOnRingedSite_hasEnoughInjectives`,
  `RingedSpace.Modules`,
  `presheafOfModules_hasFunctorialInjectiveEmbeddings`,
  `exists_resolutionFunctorOne`;
- best owner abstraction: the common owner for this remark is `EnoughInjectives`; it is available
  directly for ringed spaces and ringed sites, and for modules and presheaves it is obtained
  canonically from stronger upstream functorial-injective-embedding instances;
- primitive data: the upstream `EnoughInjectives` instances/theorems on `RingedSpace.Modules X`,
  `Mod(𝒪)`, and `ModuleCat R`, together with the owner-level instance
  `presheafOfModules_hasFunctorialInjectiveEmbeddings 𝒪` for a general presheaf of rings
  `𝒪 : Cᵒᵖ ⥤ RingCat`;
- derived API here: the specialized `ResolutionFunctorOne` existence statements, with optional
  homotopy-resolution companions.

Source/core/bridge triage:
- `source-facing`: the availability of enough injectives in the listed categories;
- `core/canonical`: `EnoughInjectives`;
- `bridge/view`: the immediate Chapter 13 theorem `exists_resolutionFunctorOne`, with
  `exists_homotopyResolutionFunctor` kept only as a companion specialization. -/

section SheafOnRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{w})

/- Remark 13.24.3, ringed-space case: the canonical upstream owner is the enough-injectives
instance on `RingedSpace.Modules X`. -/
#check
  (modulesOnRingedSite_hasEnoughInjectives (AlgebraicGeometry.RingedSpace.ringCatSheaf X) :
    EnoughInjectives X.Modules)

/- Immediate Chapter 13 consequence for a ringed space: bounded-below complexes of
`𝒪_X`-modules admit a resolution functor 1. -/
#check
  (exists_resolutionFunctorOne :
    Nonempty (ResolutionFunctorOne X.Modules))

/- Downstream companion: the corresponding homotopy resolution functor also exists. -/
#check
  (exists_homotopyResolutionFunctor :
    Nonempty (HomotopyResolutionFunctor X.Modules))

end SheafOnRingedSpace

section SheafOnRingedSite

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{max u v})

/- Remark 13.24.3, ringed-site case: Theorem 19.8.4 supplies the canonical enough-injectives
owner on `Mod(𝒪)`. -/
recall modulesOnRingedSite_hasEnoughInjectives
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) : EnoughInjectives (Mod(𝒪))

/- Immediate Chapter 13 consequence for a ringed site. -/
#check
  (exists_resolutionFunctorOne :
    Nonempty (ResolutionFunctorOne (Mod(𝒪))))

/- Downstream companion. -/
#check
  (exists_homotopyResolutionFunctor :
    Nonempty (HomotopyResolutionFunctor (Mod(𝒪))))

end SheafOnRingedSite

section ModuleCat

variable (R : Type u) [Ring R]

/- Remark 13.24.3, module case: enough injectives are available, via the standard module-category
instance. -/
recall ModuleCat.enoughInjectives (R : Type u) [Ring R] :
    EnoughInjectives (ModuleCat R)

/- Immediate Chapter 13 consequence for modules. -/
#check
  (exists_resolutionFunctorOne :
    Nonempty (ResolutionFunctorOne (ModuleCat R)))

/- Downstream companion. -/
#check
  (exists_homotopyResolutionFunctor :
    Nonempty (HomotopyResolutionFunctor (ModuleCat R)))

end ModuleCat

section PresheafOfModules

variable {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v})

/- Remark 13.24.3, presheaf case: Proposition 19.8.5 is already stated for an arbitrary presheaf
of rings `𝒪 : Cᵒᵖ ⥤ RingCat`, so the remark should stay at that owner level rather than
specializing prematurely to a ringed-space model. The Chapter 12 bridge then supplies
`EnoughInjectives (PMod(𝒪))`. -/
#check
  (presheafOfModules_hasFunctorialInjectiveEmbeddings 𝒪 :
    HasFunctorialInjectiveEmbeddings (PMod(𝒪)))

#synth EnoughInjectives (PMod(𝒪))

/- Immediate Chapter 13 consequence for presheaves of modules. -/
#check
  (exists_resolutionFunctorOne :
    Nonempty (ResolutionFunctorOne (PMod(𝒪))))

/- Downstream companion. -/
#check
  (exists_homotopyResolutionFunctor :
    Nonempty (HomotopyResolutionFunctor (PMod(𝒪))))

end PresheafOfModules

end

end CategoryTheory
