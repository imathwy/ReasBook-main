import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import StacksProject_2024.stacks_project.Chap13.Lemma_13_33_7
import StacksProject_2024.stacks_project.Chap22.DGModuleModel
import StacksProject_2024.stacks_project.Chap22.ModuleCatHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory

noncomputable section

universe u

section

variable {A : Type u} [Ring A]

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} A) :=
  AB5OfSize_shrink (ModuleCat.{u} A)

local instance : CountableAB4 (ModuleCat.{u} A) := by
  let _ : HasFiniteBiproducts (ModuleCat.{u} A) := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_countableAB5 (ModuleCat.{u} A)

local instance : HasExactColimitsOfShape ℕ (ModuleCat.{u} A) := by
  infer_instance

/- Source/core/bridge triage:
- `source-facing`: Lemma 22.23.2 for the derived category `D(A, d)` of differential graded
  `A`-modules;
- `core/canonical`: `CategoryTheory.termwise_colimit_is_homotopy_colimit`;
- `bridge/view`: the Chapter 22 dg-module owner `ModuleCat.DGMod A`, together with the named
  instance
  `ModuleCat.hasDerivedCategory`.

This item adds no new homotopy-colimit owner beyond the Chapter 13 theorem. The correct public
surface is therefore the source-facing specialization to differential graded `A`-modules, not a
second theorem with extra coproduct or colimit hypotheses. -/

/-- Lemma 22.23.2: let `(A, d)` be a differential graded algebra and let `Mₙ` be a sequential
system of differential graded `A`-modules. Then the derived colimit `hocolim Mₙ` in `D(A, d)` is
represented by the ordinary colimit dg module. In the current Chapter 22 Lean model, this is the
specialization of `termwise_colimit_is_homotopy_colimit` to `ModuleCat.DGMod A`. -/
@[stacks 0CRL]
  theorem derivedCategoryDgModules_homotopyColimit_colimit
      (M : ℕ ⥤ ModuleCat.DGMod A) :
      IsHomotopyColimitOf
        (M ⋙ (Q : ModuleCat.DGMod A ⥤ DerivedCategory (ModuleCat.{u} A)))
        (Q.obj (colimit M)) := by
  simpa using
    termwise_colimit_is_homotopy_colimit M

end
