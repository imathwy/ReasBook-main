import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import StacksProject_2024.Chap22.DGModuleModel

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v

section

variable {A : Type u} [Ring A]
variable {J : Type v} [Category J]

/- Source/core/bridge triage:
- `source-facing`: the three assertions of Lemma 22.4.2 that `Mod_{(A, d)}` is abelian and has
  arbitrary limits and colimits;
- `core/canonical`: the existing `Abelian` instance and the shape-wise
  `HasLimitsOfShape J` / `HasColimitsOfShape J` instances on `ModuleCat.DGMod A`;
- `bridge/view`: the Chapter 22 support owner `ModuleCat.DGMod A` for differential graded
  `A`-modules, implemented as cochain complexes.
-/

/- Lemma 22.4.2
In the current Chapter 22 Lean model, differential graded modules are represented by the support
owner `ModuleCat.DGMod A` of cochain complexes of `A`-modules. The source lemma is therefore
formalized as a recall of the existing abelian instance and the existing shape-wise arbitrary
limit/colimit instances on this canonical owner. -/

/- Lemma 22.4.2 (1): the category `Mod_{(A, d)}` is abelian; in the canonical cochain-complex
model, this is the existing `Abelian` instance on `ModuleCat.DGMod A`. -/
#check (inferInstance : Abelian (ModuleCat.DGMod A))

/- Lemma 22.4.2 (2): the category `Mod_{(A, d)}` has arbitrary limits; on the canonical Lean
owner side, this means that for every diagram shape `J`, `ModuleCat.DGMod A` carries the existing
`HasLimitsOfShape J` instance. -/
#check (inferInstance : HasLimitsOfShape J (ModuleCat.DGMod A))

/- Lemma 22.4.2 (3): the category `Mod_{(A, d)}` has arbitrary colimits; on the canonical Lean
owner side, this means that for every diagram shape `J`, `ModuleCat.DGMod A` carries the existing
`HasColimitsOfShape J` instance. -/
#check (inferInstance : HasColimitsOfShape J (ModuleCat.DGMod A))

end
