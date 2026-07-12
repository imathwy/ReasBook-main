import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap21.Lemma_21_12_4

open CategoryTheory
open CategoryTheory.Abelian

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.5.1:
- primary domain: sheaf cohomology and `Ext` for sheaves of modules over a ringed-space
  structure sheaf;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `RingedSpace.ringCatSheaf`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`,
  `SheafOfModules.unit`;
- best owner abstraction: the general comparison theorem
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- primitive data: a coefficient sheaf `𝒪 : Sheaf _ RingCat` and a module sheaf
  `ℱ : SheafOfModules 𝒪`;
- derived API here: the ringed-space specialization `𝒪 := RingedSpace.ringCatSheaf X` and the
  degree-`1` specialization.

Source/core/bridge triage:
- `source-facing`: the ringed-space statement identifying `H¹(X, F_ab)` with
  `Ext¹_{Mod(𝒪_X)}(𝒪_X, F)`;
- `core/canonical`: `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: specializing the coefficient sheaf to `RingedSpace.ringCatSheaf X` and the
  cohomological degree to `1`.

This file adds no new mathematical owner beyond that canonical comparison theorem, so the refined
item should use the owner theorem directly rather than keep a duplicate named specialization.
-/

/- Lemma 20.5.1 is the ringed-space specialization of the canonical comparison theorem between the
global cohomology of the underlying abelian sheaf and the module-valued Ext groups. -/
recall underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology

section

variable {X : RingedSpace.{u}}
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasExt.{u} X.Modules]
variable (ℱ : X.Modules)

/- Source-facing specialization of Lemma 20.5.1: for a ringed space `X` and an `𝒪_X`-module `F`,
the canonical comparison theorem in degree `1` identifies `H¹(X, F_ab)` with
`Ext¹_{Mod(𝒪_X)}(𝒪_X, F)`. -/
#check
  underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology ℱ 1

end

end AlgebraicGeometry.RingedSpace
