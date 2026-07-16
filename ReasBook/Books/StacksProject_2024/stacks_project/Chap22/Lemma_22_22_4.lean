import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_4
import StacksProject_2024.stacks_project.Chap22.ModuleCatHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DA" => DerivedCategory (ModuleCat A)

variable (J : Type u)
variable (M : J → DGMod)

/- Source/core/bridge triage:
- `source-facing`: Lemma 22.22.4 for `D(A, d)`, the derived category of differential graded
  `A`-modules;
- `core/canonical`: the generic Chapter 19 owners
  `CategoryTheory.derivedCategory_hasCoproductsOfShape`,
  `CategoryTheory.derivedCategory_Q_preserves_coproduct`,
  `CategoryTheory.derivedCategory_hasProductsOfShape`, and
  `CategoryTheory.derivedCategory_Q_preserves_product_of_ab4Star`;
- `bridge/view`: the specialization from the Grothendieck abelian category `ModuleCat A` to the
  Chapter 22 DG-module model `DGMod`.

The Chapter 19 owners currently remain proof-incomplete, so this file records the source item as a
source-faithful recall/check surface rather than exporting duplicate Chapter 22 wrapper instances
or preservation theorems whose public data would inherit upstream `sorryAx` taint. The canonical
derived-category instance for `ModuleCat A` is reused from the Chapter 22 support owner
`ModuleCat.hasDerivedCategory`. -/

/- Lemma 22.22.4 (1): for a differential graded algebra `(A, d)`, the derived category `D(A, d)`
has arbitrary direct sums. In the current Lean model this is the generic Chapter 19 owner
`CategoryTheory.derivedCategory_hasCoproductsOfShape`, specialized to `ModuleCat A`. -/
recall CategoryTheory.derivedCategory_hasCoproductsOfShape
set_option linter.hashCommand false in
#check (CategoryTheory.derivedCategory_hasCoproductsOfShape : HasCoproductsOfShape J DA)

/- Lemma 22.22.4 (2): direct sums in `D(A, d)` are obtained by taking direct sums of differential
graded modules. For a family `M` of representative cochain complexes, the localization functor
`DerivedCategory.Q : DGMod ⥤ DA` preserves the corresponding discrete coproduct diagram. -/
recall CategoryTheory.derivedCategory_Q_preserves_coproduct
set_option linter.hashCommand false in
#check (CategoryTheory.derivedCategory_Q_preserves_coproduct :
  PreservesColimit (Discrete.functor M) (DerivedCategory.Q : DGMod ⥤ DA))

/- Lemma 22.22.4 (3): for a differential graded algebra `(A, d)`, the derived category `D(A, d)`
has arbitrary products. In the current Lean model this is the generic Chapter 19 owner
`CategoryTheory.derivedCategory_hasProductsOfShape`, specialized to `ModuleCat A`. -/
recall CategoryTheory.derivedCategory_hasProductsOfShape
set_option linter.hashCommand false in
#check (CategoryTheory.derivedCategory_hasProductsOfShape : HasProductsOfShape J DA)

/- Lemma 22.22.4 (4): products in `D(A, d)` are obtained by taking products of differential
graded modules. For a family `M` of representative cochain complexes, the canonical Chapter 19
product-preservation owner is `CategoryTheory.derivedCategory_Q_preserves_product_of_ab4Star`,
specialized here to `ModuleCat A`. -/
recall CategoryTheory.derivedCategory_Q_preserves_product_of_ab4Star
set_option linter.hashCommand false in
#check (CategoryTheory.derivedCategory_Q_preserves_product_of_ab4Star :
  PreservesLimit (Discrete.functor M) (DerivedCategory.Q : DGMod ⥤ DA))

end
