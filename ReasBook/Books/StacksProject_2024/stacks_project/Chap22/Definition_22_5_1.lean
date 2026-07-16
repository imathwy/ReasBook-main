import StacksProject_2024.stacks_project.Chap22.DGModuleModel

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomologicalComplex

universe u

namespace CategoryTheory

section

variable {A : Type u} [Ring A]
variable {M N : ModuleCat.DGMod A}
variable (f g : M ⟶ N)

/- Source/core/bridge triage:
- `source-facing`: morphisms of differential graded `A`-modules are homotopic;
- `core/canonical`: the cochain-complex homotopy type `Homotopy f g`;
- `bridge/view`: the Chapter 22 dg-module owner `ModuleCat.DGMod A` together with the induced
  homotopy relation `homotopic (ModuleCat A) (up ℤ) f g`.
-/

/- Definition 22.5.1: for morphisms `f, g : M ⟶ N` of differential graded `A`-modules, the
canonical owner notion of a homotopy is the cochain-complex homotopy type `Homotopy f g`. -/
#check (Homotopy f g)

/- Companion recall: the source-facing proposition that `f` and `g` are homotopic is the
existing relation `homotopic (ModuleCat A) (up ℤ) f g`. -/
#check (homotopic (ModuleCat A) (up ℤ) f g)

end

end CategoryTheory
