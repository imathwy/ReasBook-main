import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_5_1 (from Chap20) -/
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.5.1:
- primary domain: sheaf cohomology and `Ext` for sheaves of modules over a ringed-space
  structure sheaf;
- sampled owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`,
  `SheafOfModules.unitHomEquiv`;
- best owner abstraction: the general comparison theorem
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- primitive data: a coefficient sheaf `𝒪 : Sheaf _ RingCat` and a module sheaf
  `ℱ : SheafOfModules 𝒪`;
- derived API here: the ringed-space specialization `𝒪 := (RingedSpace.ringCatSheaf X)` and the degree-`1`
  instance.

Source/core/bridge triage:
- `source-facing`: the ringed-space statement identifying `H¹(X, F_ab)` with
  `Ext¹_{Mod(𝒪_X)}(𝒪_X, F)`;
- `core/canonical`: `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: specializing the coefficient sheaf to `(RingedSpace.ringCatSheaf X)` and the cohomological
  degree to `1`.

This file adds no new mathematical owner beyond that canonical comparison theorem, so the refined
item should use the owner theorem directly rather than keep a duplicate named specialization.
-/

/- Lemma 20.5.1 is the ringed-space specialization of the canonical comparison theorem between the
global cohomology of the underlying abelian sheaf and the module-valued Ext groups. -/
recall underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology

section

variable {X : RingedSpace.{u}}
variable [HasExt (TopCat.Sheaf AddCommGrpCat.{u} X)] [HasExt (RingedSpace.Modules X)]
variable (F : (RingedSpace.Modules X))

/- Source-facing specialization: for a ringed space `X` and an `\mathcal O_X`-module `F`, the
degree-`1` case identifies `H¹(X, F_ab)` with
`Ext¹_{\mathrm{Mod}(\mathcal O_X)}(\mathcal O_X, F)`. -/
#check (underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology F 1 :
  AddCommGrpCat.of (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj F).H 1) =
    (Abelian.extFunctorObj (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) 1).obj F)

end

end AlgebraicGeometry.RingedSpace
