import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import StacksProject_2024.stacks_project.Chap22.DGModuleModel

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

section

variable (A : Type u) [Ring A]

/- Source/core/bridge triage:
- `source-facing`: the Stacks statement that `K(Mod_(A,d))`, with its natural translation
  functors and distinguished triangles, is pre-triangulated;
- `core/canonical`: the Chapter 22 owner `ModuleCat.KDGMod A` together with the canonical instance
  `Pretriangulated (ModuleCat.KDGMod A)`;
- `bridge/view`: the canonical translation-functor and distinguished-triangle owners
  `shiftFunctor (ModuleCat.KDGMod A)` and `distTriang (ModuleCat.KDGMod A)`.

This item is recall-only: the source introduces no new structure beyond the existing
pretriangulated instance on `ModuleCat.KDGMod A`, so the refined file keeps the canonical recall
surface and its immediate companion owners. -/

/- Lemma 22.10.1: Let `(A, d)` be a differential graded algebra. The homotopy category
`K(Mod_(A,d))` with its natural translation functors and distinguished triangles is a
pre-triangulated category. In the current Chapter 22 formalization of differential graded
`A`-modules by cochain complexes of `A`-modules, this is the canonical `Pretriangulated`
instance on `ModuleCat.KDGMod A`. -/
#check (inferInstance : Pretriangulated (ModuleCat.KDGMod A))

/- Companion recall: the natural translation functors on this homotopy category are the standard
integer-indexed shift functors. -/
#check (shiftFunctor (ModuleCat.KDGMod A))

/- Companion recall: the distinguished triangles on `ModuleCat.KDGMod A` are the canonical
project-facing owner `distTriang`, used by the mapping-cone and degreewise-split short-exact-
sequence API. -/
#check (distTriang (ModuleCat.KDGMod A))

end
